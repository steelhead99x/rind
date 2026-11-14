mod criterion;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

// Wrapping and unwrapping a 16- and a 32-byte key, each from the KEK's bytes,
// as pyca and JWE use a KEK: aws-lc-rs's `KeyWrap` consumes its key anyway.
fn bench_key_wrap(c: &mut Criterion) {
    for (mode, padded) in [("kw", false), ("kwp", true)] {
        for (aes, kek_len) in [("aes128", 16), ("aes256", 32)] {
            let kek = &[0x42u8; 32][..kek_len];
            let rind_kek = || rind::key_wrap::AesKek::new(rind_algorithm(kek_len), kek).unwrap();
            for (op, unwrap) in [("wrap", false), ("unwrap", true)] {
                let mut group = c.benchmark_group(format!("{aes}-{mode}-{op}"));
                for key_len in [16, 32] {
                    let size_name = format!("{key_len}B");
                    let key = &[0x24u8; 32][..key_len];
                    let mut wrapped = vec![0u8; key_len + 8];
                    if padded {
                        rind_kek().wrap_padded(key, &mut wrapped).unwrap();
                    } else {
                        rind_kek().wrap(key, &mut wrapped).unwrap();
                    }
                    // aws-lc-rs's padded wrap wants 15 bytes of room
                    let mut out = vec![0u8; key_len + 15];

                    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
                    group.bench_function(BenchmarkId::new("aws-lc-rs", &size_name), |b| {
                        use aws_lc_rs::key_wrap::{
                            AES_128, AES_256, AesKek, KeyWrap, KeyWrapPadded,
                        };
                        let algorithm = if kek_len == 16 { &AES_128 } else { &AES_256 };
                        b.iter(|| {
                            let kek = AesKek::new(algorithm, kek).unwrap();
                            match (padded, unwrap) {
                                (false, false) => kek.wrap(key, &mut out).unwrap(),
                                (false, true) => kek.unwrap(&wrapped, &mut out).unwrap(),
                                (true, false) => kek.wrap_with_padding(key, &mut out).unwrap(),
                                (true, true) => {
                                    kek.unwrap_with_padding(&wrapped, &mut out).unwrap()
                                }
                            };
                        });
                    });
                    group.bench_function(BenchmarkId::new("rind", &size_name), |b| {
                        b.iter(|| {
                            let kek = rind_kek();
                            match (padded, unwrap) {
                                (false, false) => kek.wrap(key, &mut out[..key_len + 8]).unwrap(),
                                (false, true) => kek.unwrap(&wrapped, &mut out[..key_len]).unwrap(),
                                (true, false) => {
                                    kek.wrap_padded(key, &mut out[..key_len + 8]).unwrap()
                                }
                                (true, true) => {
                                    kek.unwrap_padded(&wrapped, &mut out[..key_len]).unwrap();
                                }
                            }
                        });
                    });
                }
            }
        }
    }
}

fn rind_algorithm(kek_len: usize) -> &'static rind::cipher::Algorithm {
    if kek_len == 16 {
        &rind::key_wrap::AES_128
    } else {
        &rind::key_wrap::AES_256
    }
}

criterion_group!(benches, bench_key_wrap);
criterion_main!(benches);
