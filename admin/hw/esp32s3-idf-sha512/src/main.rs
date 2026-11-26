// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! rind's SHA-512 on the ESP32-S3 under ESP-IDF, where `esp32s3-sha512-unrolled`
//! runs the unrolled body from IRAM. Each round prints FIPS 180-4's known
//! answers and the bench inputs' digests, PASS or FAIL, then the median time
//! of one SHA-512 at each size, and ends with `ROUND-END`, over and over, so a
//! capture of any length holds whole rounds. admin/hw/esp32s3-sha512-idf.sh
//! reads only the rounds after the first, and only when every check passed.

use std::hint::black_box;

use rind::digest::{SHA512, digest};

/// FIPS 180-4's SHA-512 examples: the empty message, "abc", and the
/// two-block 896-bit message.
const KATS: [(&str, &[u8], &str); 3] = [
    (
        "empty",
        b"",
        "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce\
         47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e",
    ),
    (
        "abc",
        b"abc",
        "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a\
         2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f",
    ),
    (
        "two-block",
        b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno\
          ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
        "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018\
         501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909",
    ),
];

/// The timed sizes, the iterations in one sample of each (about 20 ms at
/// 80 MHz), and the digest of the bench input at that size, Python's
/// hashlib's of `bytes((i * 31 + 7) & 255 for i in range(n))`, so the
/// timed path is checked too.
const SIZES: [(usize, u32, &str); 4] = [
    (
        16,
        64,
        "363cdc413e8e4c320480c157b2a8192b327c588257fab846788e9906e04a3e33\
         d6c74c71a1ecb52bb21365f30fc9a9ee10e66d41d0cf9d73e8dba1aa86d4c950",
    ),
    (
        243,
        32,
        "80273283e866b30782c5ffa27afb70b5a9164cbabf777eaadf726f94dbb666ab\
         aae35a8f9e95808433ed3828bc7a39d5f291641062760209567be20ebb593e37",
    ),
    (
        1500,
        8,
        "72089755b510be6c5701ddd517234a7bdb7e4ec0fe53a60a4119ace8b8d54909\
         fb32a6fd90628320de76ae62cb0491f195b8bb9a978a98716b0ec6a31b91a15c",
    ),
    (
        16384,
        1,
        "c7a92b2e9c51d6a9f11737ac58fb4d6478d51f2454d02883f985b041d6a4dfb8\
         26ca99bdbf4c515786b4c8f238789aef8e4d7d4d83a038285604a649f92fc356",
    ),
];

/// Samples per size; the printed time is their median.
const SAMPLES: usize = 15;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn now_us() -> i64 {
    // SAFETY: esp_timer is started by ESP-IDF before app_main.
    unsafe { esp_idf_sys::esp_timer_get_time() }
}

fn main() {
    esp_idf_sys::link_patches();
    let label = option_env!("RIND_FW_LABEL").unwrap_or("unlabelled");
    let mhz = option_env!("RIND_FW_MHZ").unwrap_or("?");
    let input: Vec<u8> = (0..16384usize).map(|i| (i * 31 + 7) as u8).collect();
    let mut round = 0u64;
    loop {
        round += 1;
        println!("IDF-BENCH v1 label={label} mhz={mhz} round={round}");
        for (name, msg, want) in KATS {
            let ok = hex(digest(&SHA512, msg).as_ref()) == want;
            println!("KAT sha512 {name} {}", if ok { "PASS" } else { "FAIL" });
        }
        for (n, _, want) in SIZES {
            let ok = hex(digest(&SHA512, &input[..n]).as_ref()) == want;
            println!("KAT sha512 bench-{n}B {}", if ok { "PASS" } else { "FAIL" });
        }
        for (n, iters, _) in SIZES {
            let data = &input[..n];
            let mut samples = [0i64; SAMPLES];
            for s in samples.iter_mut() {
                let t0 = now_us();
                for _ in 0..iters {
                    black_box(digest(&SHA512, black_box(data)));
                }
                *s = now_us() - t0;
            }
            samples.sort_unstable();
            let med = samples[SAMPLES / 2];
            // Hundredths of a microsecond per digest.
            let per = med * 100 / i64::from(iters);
            println!("BENCH sha512 {n}B {}.{:02} us", per / 100, per % 100);
        }
        println!("ROUND-END {round}");
    }
}
