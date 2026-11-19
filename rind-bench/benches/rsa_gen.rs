#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod criterion;
#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use criterion::{Criterion, Throughput, criterion_group, criterion_main};

#[cfg(not(target_arch = "xtensa"))]
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
                black_box(rind::rsa::KeyPair::generate(ours).unwrap());
            })
        });

        // Checked once per size: criterion runs the closure for every sample,
        // and each key costs a generation.
        let vg_generate = || {
            use verified_garbage::rsa::{BigUint, keygen};
            keygen::generate(bits, BigUint::from_be_bytes(&[1, 0, 1])).unwrap()
        };
        assert_eq!(vg_generate().modulus_len(), bits / 8);
        group.bench_function("verified-garbage", |b| b.iter(|| black_box(vg_generate())));

        // RustCrypto takes seconds per 4096-bit key.
        if bits == 2048 {
            group.bench_function("rustcrypto", |b| {
                use getrandom::{SysRng, rand_core::UnwrapErr};

                b.iter(|| {
                    black_box(rsa::PrivateKey::new(&mut UnwrapErr(SysRng), bits).unwrap());
                })
            });
        }
    }
}

#[cfg(not(target_arch = "xtensa"))]
criterion_group!(benches, rsa_key_generation);
#[cfg(not(target_arch = "xtensa"))]
criterion_main!(benches);
