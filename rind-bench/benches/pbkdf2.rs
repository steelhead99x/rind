#[macro_use]
mod criterion;
use std::hint::black_box;
use std::num::NonZeroU32;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

// One key the length of the hash, as password storage derives. The cost is
// all in the iterations, so throughput is in iterations per second.
const ITERATIONS: u32 = 1000;

fn bench(
    c: &mut Criterion,
    name: &str,
    ring: ring::pbkdf2::Algorithm,
    aws: aws!(pbkdf2::Algorithm),
    ours: &'static rind::pbkdf2::Algorithm,
    len: usize,
) {
    #[cfg(any(target_arch = "xtensa", target_os = "none"))]
    let _ = &aws;
    let mut group = c.benchmark_group(name);
    group.throughput(Throughput::Elements(ITERATIONS as u64));
    let iterations = NonZeroU32::new(ITERATIONS).unwrap();
    let mut out = vec![0u8; len];

    group.bench_function("ring", |b| {
        b.iter(|| {
            ring::pbkdf2::derive(ring, iterations, b"salt", b"password", &mut out);
            black_box(&out);
        })
    });
    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        b.iter(|| {
            aws_lc_rs::pbkdf2::derive(aws, iterations, b"salt", b"password", &mut out);
            black_box(&out);
        })
    });
    group.bench_function("rind", |b| {
        b.iter(|| {
            rind::pbkdf2::Secret::new(ours, b"password")
                .derive(iterations, b"salt", &mut out)
                .unwrap();
            black_box(&out);
        })
    });
}

fn pbkdf2(c: &mut Criterion) {
    bench(
        c,
        "pbkdf2-sha1",
        ring::pbkdf2::PBKDF2_HMAC_SHA1,
        aws!(pbkdf2::PBKDF2_HMAC_SHA1),
        &rind::pbkdf2::legacy::PBKDF2_HMAC_SHA1,
        20,
    );
    bench(
        c,
        "pbkdf2-sha256",
        ring::pbkdf2::PBKDF2_HMAC_SHA256,
        aws!(pbkdf2::PBKDF2_HMAC_SHA256),
        &rind::pbkdf2::PBKDF2_HMAC_SHA256,
        32,
    );
    bench(
        c,
        "pbkdf2-sha384",
        ring::pbkdf2::PBKDF2_HMAC_SHA384,
        aws!(pbkdf2::PBKDF2_HMAC_SHA384),
        &rind::pbkdf2::PBKDF2_HMAC_SHA384,
        48,
    );
    bench(
        c,
        "pbkdf2-sha512",
        ring::pbkdf2::PBKDF2_HMAC_SHA512,
        aws!(pbkdf2::PBKDF2_HMAC_SHA512),
        &rind::pbkdf2::PBKDF2_HMAC_SHA512,
        64,
    );
}

criterion_group!(benches, pbkdf2);
criterion_main!(benches);
