mod criterion;
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

fn rsa_key_generation(c: &mut Criterion) {
    // All these are gated under `NOISY_BENCHMARKS` for the benefit of codspeed,
    // which runs each test once and expects deterministic results.  RSA key generation
    // certainly is not that.
    if option_env!("NOISY_BENCHMARKS").is_none() {
        return;
    }

    let sizes = [
        (2048, rind::rsa::KeySize::Rsa2048),
        (3072, rind::rsa::KeySize::Rsa3072),
        (4096, rind::rsa::KeySize::Rsa4096),
    ];
    for (bits, ours) in sizes {
        let mut group = c.benchmark_group(format!("rsa{bits}-key-generation"));
        group.throughput(Throughput::Elements(1));
        // Each key takes tens to hundreds of milliseconds, so the default
        // hundred samples would take minutes.
        group.sample_size(10);

        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_function("aws-lc-rs", |b| {
            let theirs = match bits {
                2048 => aws_lc_rs::rsa::KeySize::Rsa2048,
                3072 => aws_lc_rs::rsa::KeySize::Rsa3072,
                _ => aws_lc_rs::rsa::KeySize::Rsa4096,
            };
            b.iter(|| {
                black_box(aws_lc_rs::rsa::KeyPair::generate(theirs).unwrap());
            })
        });

        group.bench_function("rind", |b| {
            b.iter(|| {
                black_box(rind::signature::RsaKeyPair::generate(ours).unwrap());
            })
        });

        // RustCrypto takes seconds per 4096-bit key.
        if bits == 2048 {
            group.bench_function("rustcrypto", |b| {
                use getrandom::{SysRng, rand_core::UnwrapErr};
                use rsa::RsaPrivateKey;

                b.iter(|| {
                    black_box(RsaPrivateKey::new(&mut UnwrapErr(SysRng), bits).unwrap());
                })
            });
        }
    }
}

criterion_group!(benches, rsa_key_generation);
criterion_main!(benches);
