mod criterion;
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

// RFC 9106's second recommendation, the one cheap enough to sample, and one
// lane of 16 MiB in one pass. Filling memory is nearly all the cost, so
// throughput is in bytes filled.
const COSTS: [(&str, u32, u32, u32); 2] = [
    ("16MiB-t1-p1", 1 << 14, 1, 1),
    ("64MiB-t3-p4", 1 << 16, 3, 4),
];

fn argon2(c: &mut Criterion) {
    let (password, salt) = (b"password", b"per-user salt");
    for (name, memory_kib, passes, lanes) in COSTS {
        let mut group = c.benchmark_group(format!("argon2id-{name}"));
        group.sample_size(10);
        group.throughput(Throughput::Bytes(memory_kib as u64 * 1024 * passes as u64));
        let mut out = [0u8; 32];

        group.bench_function("rustcrypto", |b| {
            let params = argon2::Params::new(memory_kib, passes, lanes, Some(32)).unwrap();
            let ctx =
                argon2::Argon2::new(argon2::Algorithm::Argon2id, argon2::Version::V0x13, params);
            b.iter(|| {
                ctx.hash_password_into(password, salt, &mut out).unwrap();
                black_box(&out);
            })
        });
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        group.bench_function("openssl", |b| {
            b.iter(|| {
                openssl::kdf::argon2id(
                    None, password, salt, None, None, passes, lanes, memory_kib, &mut out,
                )
                .unwrap();
                black_box(&out);
            })
        });
        group.bench_function("rind", |b| {
            let params = rind::argon2::Params::new(memory_kib, passes, lanes).unwrap();
            b.iter(|| {
                rind::argon2::derive(params, password, salt, &mut out).unwrap();
                black_box(&out);
            })
        });
    }
}

criterion_group!(benches, argon2);
criterion_main!(benches);
