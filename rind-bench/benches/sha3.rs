#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
#[macro_use]
mod criterion;
#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};

#[cfg(not(target_arch = "xtensa"))]
fn bench<R: sha3::Digest, V: verified_garbage::hashes::HashFunction>(
    c: &mut Criterion,
    name: &str,
    aws: &'static aws!(digest::Algorithm),
    libcrux: fn(&[u8]),
    ours: &'static rind::digest::Algorithm,
) {
    #[cfg(any(target_arch = "xtensa", target_os = "none"))]
    let _ = &aws;
    let mut group = c.benchmark_group(name);
    for (size, size_name) in criterion::HASH_SIZES {
        let input = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));

        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_with_input(
            BenchmarkId::new("aws-lc-rs", size_name),
            &input,
            |b, input| {
                b.iter(|| {
                    let mut ctx = aws_lc_rs::digest::Context::new(aws);
                    ctx.update(input);
                    black_box(ctx.finish())
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new("rustcrypto", size_name),
            &input,
            |b, input| {
                b.iter(|| {
                    let mut ctx = R::new();
                    ctx.update(input);
                    black_box(ctx.finalize())
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new("libcrux", size_name),
            &input,
            |b, input| b.iter(|| libcrux(input)),
        );
        group.bench_with_input(BenchmarkId::new("rind", size_name), &input, |b, input| {
            b.iter(|| {
                let mut ctx = rind::digest::Context::new(ours);
                ctx.update(input);
                black_box(ctx.finish())
            })
        });
        let mut ctx = V::new();
        ctx.update(&input);
        assert_eq!(
            ctx.finalize().as_ref(),
            rind::digest::digest(ours, &input).as_ref()
        );
        group.bench_with_input(
            BenchmarkId::new("verified-garbage", size_name),
            &input,
            |b, input| {
                b.iter(|| {
                    let mut ctx = V::new();
                    ctx.update(input);
                    black_box(ctx.finalize())
                })
            },
        );
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn sha3_256(c: &mut Criterion) {
    bench::<sha3::Sha3_256, verified_garbage::hashes::sha3::Sha3_256>(
        c,
        "sha3-256",
        &aws!(digest::SHA3_256),
        |data| {
            black_box(libcrux_sha3::sha256(data));
        },
        &rind::digest::SHA3_256,
    );
}

#[cfg(not(target_arch = "xtensa"))]
fn sha3_384(c: &mut Criterion) {
    bench::<sha3::Sha3_384, verified_garbage::hashes::sha3::Sha3_384>(
        c,
        "sha3-384",
        &aws!(digest::SHA3_384),
        |data| {
            black_box(libcrux_sha3::sha384(data));
        },
        &rind::digest::SHA3_384,
    );
}

#[cfg(not(target_arch = "xtensa"))]
fn sha3_512(c: &mut Criterion) {
    bench::<sha3::Sha3_512, verified_garbage::hashes::sha3::Sha3_512>(
        c,
        "sha3-512",
        &aws!(digest::SHA3_512),
        |data| {
            black_box(libcrux_sha3::sha512(data));
        },
        &rind::digest::SHA3_512,
    );
}

#[cfg(not(target_arch = "xtensa"))]
criterion_group!(benches, sha3_256, sha3_384, sha3_512);
#[cfg(not(target_arch = "xtensa"))]
criterion_main!(benches);
