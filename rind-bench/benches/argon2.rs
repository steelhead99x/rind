mod criterion;
use std::hint::black_box;
use std::time::Duration;

use argon2::{Algorithm, Argon2, ParamsBuilder, Version};
use criterion::{Criterion, criterion_group, criterion_main};
use rind::argon2::{Params, Secret};

// Release fills, one lane, the sizes the Argon2id comparison uses. A
// `RIND_CPU_DISABLE_*` run, with `--cfg rind_cpu_disable`, times the next
// permutation instead of the widest one.
fn argon2(c: &mut Criterion) {
    let secret = Secret::new(b"password").unwrap();
    let salt = b"somesalt";
    for (name, memory_kib, passes) in [
        ("1MiB-3", 1024, 3),
        ("16MiB-1", 16 * 1024, 1),
        ("64MiB-1", 64 * 1024, 1),
    ] {
        let mut group = c.benchmark_group(name);
        group.sample_size(10);
        group.warm_up_time(Duration::from_millis(200));
        group.measurement_time(Duration::from_secs(1));
        let params = Params::new(memory_kib, passes, 1).unwrap();
        let mut builder = ParamsBuilder::new();
        builder.m_cost(memory_kib).t_cost(passes).p_cost(1);
        let theirs = Argon2::new(
            Algorithm::Argon2id,
            Version::V0x13,
            builder.build().unwrap(),
        );
        let mut out = [0u8; 32];

        group.bench_function("rind", |b| {
            b.iter(|| {
                secret.derive(params, salt, b"", b"", &mut out).unwrap();
                black_box(out);
            });
        });
        group.bench_function("rustcrypto", |b| {
            b.iter(|| {
                theirs
                    .hash_password_into(b"password", salt, &mut out)
                    .unwrap();
                black_box(out);
            });
        });
    }
}

criterion_group!(benches, argon2);
criterion_main!(benches);
