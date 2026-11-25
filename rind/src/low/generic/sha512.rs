// Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com) All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! SHA-512's block function: aws-lc's 64-bit `sha512_block_data_order_nohw`,
//! from `crypto/fipsmodule/sha/sha512.c` at commit
//! 5ed12cce0fd4453f2f63300d44325ed14f845d6f, in Rust, as
//! [`sha256`](sha256.rs) ports its SHA-256: sixteen rounds that read the
//! block, then a loop of sixteen over the window, with the same Ch and Maj
//! forms. The portable backend runs it everywhere but 32-bit
//! microcontrollers, which run [`sha512_rolled`](sha512_rolled.rs). aws-lc
//! compiles a rolled variant for 32-bit x86 instead; ported to Rust it took
//! 0.98 of this one's time on i686, too little for a second body.
//!
//! Every operation is an add, rotate, shift, or bitwise op, and every index
//! is a round number, so nothing branches on or indexes by the state or the
//! block. It is not formally verified: its correctness rests on its use in
//! OpenSSL, BoringSSL, and aws-lc, and on rind's tests of it against
//! FIPS 180-4, Wycheproof, and aws-lc-rs.

/// One round on the schedule word `$w`, the working variables named in
/// their current order.
#[cfg(any(
    not(all(
        not(target_pointer_width = "64"),
        any(target_os = "espidf", target_os = "none")
    )),
    test
))]
macro_rules! round {
    ($w:expr, $k:expr, $a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident) => {{
        let s1 = $e.rotate_right(14) ^ $e.rotate_right(18) ^ $e.rotate_right(41);
        let ch = (($f ^ $g) & $e) ^ $g;
        let t1 = $w
            .wrapping_add($h)
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add($k);
        let s0 = $a.rotate_right(28) ^ $a.rotate_right(34) ^ $a.rotate_right(39);
        let maj = (($a ^ $b) & ($b ^ $c)) ^ $b;
        $d = $d.wrapping_add(t1);
        $h = s0.wrapping_add(maj).wrapping_add(t1);
    }};
}

/// Compresses whole 128-byte `blocks` into `state`.
#[cfg(any(
    not(all(
        not(target_pointer_width = "64"),
        any(target_os = "espidf", target_os = "none")
    )),
    test
))]
pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));
    let (blocks, _) = blocks.as_chunks::<128>();
    for block in blocks {
        let (words, _) = block.as_chunks::<8>();
        let mut x: [u64; 16] = core::array::from_fn(|j| u64::from_be_bytes(words[j]));
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;

        macro_rules! first {
            ($j:literal, $($v:ident),*) => {
                round!(x[$j], K[$j], $($v),*)
            };
        }
        sixteen!(first, a, b, c, d, e, f, g, h);

        // As in `sha256`: unrolling all eighty rounds took 1.25 times this
        // loop's time on x86_64.
        let mut i = 16;
        while i < 80 {
            // W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16], FIPS 180-4
            // §6.4.2, with each index taken mod 16 in the window.
            macro_rules! rest {
                ($j:literal, $($v:ident),*) => {{
                    let w1 = x[($j + 1) & 15];
                    let w14 = x[($j + 14) & 15];
                    let s0 = w1.rotate_right(1) ^ w1.rotate_right(8) ^ (w1 >> 7);
                    let s1 = w14.rotate_right(19) ^ w14.rotate_right(61) ^ (w14 >> 6);
                    let w = x[$j]
                        .wrapping_add(s0)
                        .wrapping_add(s1)
                        .wrapping_add(x[($j + 9) & 15]);
                    x[$j] = w;
                    round!(w, K[i + $j], $($v),*)
                }};
            }
            sixteen!(rest, a, b, c, d, e, f, g, h);
            i += 16;
        }

        for (s, v) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *s = s.wrapping_add(v);
        }
    }
}

// FIPS 180-4 §4.2.3. With `esp32s3-sha512-unrolled` on ESP-IDF, in internal
// DRAM rather than flash `.rodata`, for `sha512_esp32s3`'s IRAM body: `.iram1`
// code is expected not to touch flash while the cache is off.
//
// SAFETY: the attribute only selects the output section. The bytes are these
// constants, and ESP-IDF maps `.dram1` into internal DRAM.
#[cfg_attr(
    all(
        target_arch = "xtensa",
        target_os = "espidf",
        rind_esp32s3,
        feature = "esp32s3-sha512-unrolled",
    ),
    unsafe(link_section = ".dram1.rodata")
)]
pub(super) static K: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use crate::low::ct;
    use crate::low::generic::{sha512, sha512_rolled};

    /// SHA-512's IV, FIPS 180-4 §5.3.5.
    const IV: [u64; 8] = [
        0x6a09e667f3bcc908,
        0xbb67ae8584caa73b,
        0x3c6ef372fe94f82b,
        0xa54ff53a5f1d36f1,
        0x510e527fade682d1,
        0x9b05688c2b3e6c1f,
        0x1f83d9abfb41bd6b,
        0x5be0cd19137e2179,
    ];

    /// The digest of a secret `message`, padded as `Sha512State` pads it.
    fn hash(message: &[u8]) -> [u8; 64] {
        let message = message.to_vec();
        ct::secret_slice(&message);
        let bits = (message.len() as u128).checked_mul(8).unwrap();
        let (blocks, rest) = crate::low::split_tail::<128, 16>(&message);
        let mut state = IV;
        sha512::sha512_compress_blocks(&mut state, blocks);
        let mut last = [[0u8; 128]; 2];
        sha512::sha512_compress_blocks(
            &mut state,
            crate::low::pad(rest, bits.to_be_bytes(), &mut last),
        );
        let mut out = [0u8; 64];
        for (bytes, word) in out
            .as_chunks_mut::<8>()
            .0
            .iter_mut()
            .zip(ct::into_public(state))
        {
            *bytes = word.to_be_bytes();
        }
        out
    }

    #[test]
    fn fips180() {
        // FIPS 180-4 SHA-512: the empty message, "abc", and the 112-byte
        // message whose padding fills a second block.
        let cases: [(&[u8], &str); 3] = [
            (
                b"",
                "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e",
            ),
            (
                b"abc",
                "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f",
            ),
            (
                b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
                "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909",
            ),
        ];
        for (message, hex_digest) in cases {
            let expected = hex::decode(hex_digest).unwrap();
            assert_eq!(hash(message).as_slice(), expected.as_slice());
        }
    }

    #[test]
    #[cfg(not(any(miri, target_family = "wasm")))]
    fn matches_aws_lc() {
        // Both padding boundaries and runs of several blocks, on a secret
        // message, against aws-lc's SHA-512.
        let message: [u8; 1200] = core::array::from_fn(|i| i.wrapping_mul(197) as u8);
        for len in [
            0, 1, 63, 64, 111, 112, 127, 128, 129, 239, 240, 255, 256, 257, 1200,
        ] {
            let input = &message[..len];
            let want = aws_lc_rs::digest::digest(&aws_lc_rs::digest::SHA512, input);
            assert_eq!(hash(input).as_slice(), want.as_ref(), "{len}");
        }
    }

    #[test]
    fn keyed_states() {
        // Arbitrary secret chaining states, as HMAC's keyed states are, and
        // all-zero and all-one states and blocks, against the rolled loop and
        // the backend's own compression. A run's split must not matter.
        for case in 0..16u64 {
            let state: [u64; 8] = core::array::from_fn(|i| match case {
                0 => 0,
                1 => u64::MAX,
                _ => {
                    case.wrapping_mul(0x9e37_79b9_7f4a_7c15)
                        .rotate_left(i as u32 * 7)
                        ^ i as u64
                }
            });
            let blocks: [u8; 128 * 5] = core::array::from_fn(|i| match case {
                0 => 0,
                1 => 0xff,
                _ => (i as u64).wrapping_mul(197).wrapping_add(case) as u8,
            });
            ct::secret_slice(&state);
            ct::secret_slice(&blocks);
            let mut whole = state;
            sha512::sha512_compress_blocks(&mut whole, &blocks);
            let mut split = state;
            for block in blocks.chunks(128) {
                sha512::sha512_compress_blocks(&mut split, block);
            }
            let mut rolled = state;
            sha512_rolled::sha512_compress_blocks(&mut rolled, &blocks);
            let mut backend = state;
            crate::low::sha512_compress_blocks(&mut backend, &blocks);
            let whole = ct::into_public(whole);
            assert_eq!(whole, ct::into_public(split), "{case}");
            assert_eq!(whole, ct::into_public(rolled), "{case}");
            assert_eq!(whole, ct::into_public(backend), "{case}");
        }
    }
}
