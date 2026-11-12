mod criterion;
use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use sha2::Digest;

fn test_ring_sha256(data: &[u8]) {
    let mut ctx = ring::digest::Context::new(&ring::digest::SHA256);
    ctx.update(data);
    black_box(ctx.finish());
}

fn test_ring_sha512(data: &[u8]) {
    let mut ctx = ring::digest::Context::new(&ring::digest::SHA512);
    ctx.update(data);
    black_box(ctx.finish());
}

fn test_ring_sha512_256(data: &[u8]) {
    let mut ctx = ring::digest::Context::new(&ring::digest::SHA512_256);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
fn test_aws_sha256(data: &[u8]) {
    let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::SHA256);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
fn test_aws_sha512(data: &[u8]) {
    let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::SHA512);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
fn test_aws_sha512_256(data: &[u8]) {
    let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::SHA512_256);
    ctx.update(data);
    black_box(ctx.finish());
}

fn test_rc_sha256(data: &[u8]) {
    let mut ctx = sha2::Sha256::new();
    ctx.update(data);
    black_box(ctx.finalize());
}

fn test_rc_sha512(data: &[u8]) {
    let mut ctx = sha2::Sha512::new();
    ctx.update(data);
    black_box(ctx.finalize());
}

fn test_rc_sha512_256(data: &[u8]) {
    let mut ctx = sha2::Sha512_256::new();
    ctx.update(data);
    black_box(ctx.finalize());
}

fn test_rind_sha256(data: &[u8]) {
    let mut ctx = rind::digest::Context::new(&rind::digest::SHA256);
    ctx.update(data);
    black_box(ctx.finish());
}

fn test_rind_sha512(data: &[u8]) {
    let mut ctx = rind::digest::Context::new(&rind::digest::SHA512);
    ctx.update(data);
    black_box(ctx.finish());
}

fn test_rind_sha512_256(data: &[u8]) {
    let mut ctx = rind::digest::Context::new(&rind::digest::SHA512_256);
    ctx.update(data);
    black_box(ctx.finish());
}

fn sha256(c: &mut Criterion) {
    let mut group = c.benchmark_group("sha256");
    for (size, size_name) in criterion::HASH_SIZES {
        let input = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_with_input(BenchmarkId::new("ring", size_name), &input, |b, input| {
            b.iter(|| test_ring_sha256(input))
        });
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_with_input(
            BenchmarkId::new("aws-lc-rs", size_name),
            &input,
            |b, input| b.iter(|| test_aws_sha256(input)),
        );
        group.bench_with_input(
            BenchmarkId::new("rustcrypto", size_name),
            &input,
            |b, input| b.iter(|| test_rc_sha256(input)),
        );
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_with_input(BenchmarkId::new(lib, size_name), &input, |b, input| {
                b.iter(|| test_rind_sha256(input))
            });
        }
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        group.bench_with_input(
            BenchmarkId::new("graviola", size_name),
            &input,
            |b, input| {
                b.iter(|| {
                    let mut ctx = graviola::hashing::sha2::Sha256Context::new();
                    ctx.update(input);
                    black_box(ctx.finish())
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new("libcrux", size_name),
            &input,
            |b, input| b.iter(|| black_box(libcrux_sha2::sha256(input))),
        );
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        group.bench_with_input(
            BenchmarkId::new("openssl", size_name),
            &input,
            |b, input| b.iter(|| black_box(openssl::sha::sha256(input))),
        );
    }
}

fn sha512(c: &mut Criterion) {
    let mut group = c.benchmark_group("sha512");
    for (size, size_name) in criterion::HASH_SIZES {
        let input = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_with_input(BenchmarkId::new("ring", size_name), &input, |b, input| {
            b.iter(|| test_ring_sha512(input))
        });
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_with_input(
            BenchmarkId::new("aws-lc-rs", size_name),
            &input,
            |b, input| b.iter(|| test_aws_sha512(input)),
        );
        group.bench_with_input(
            BenchmarkId::new("rustcrypto", size_name),
            &input,
            |b, input| b.iter(|| test_rc_sha512(input)),
        );
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_with_input(BenchmarkId::new(lib, size_name), &input, |b, input| {
                b.iter(|| test_rind_sha512(input))
            });
        }
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        group.bench_with_input(
            BenchmarkId::new("graviola", size_name),
            &input,
            |b, input| {
                b.iter(|| {
                    let mut ctx = graviola::hashing::sha2::Sha512Context::new();
                    ctx.update(input);
                    black_box(ctx.finish())
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new("libcrux", size_name),
            &input,
            |b, input| b.iter(|| black_box(libcrux_sha2::sha512(input))),
        );
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        group.bench_with_input(
            BenchmarkId::new("openssl", size_name),
            &input,
            |b, input| b.iter(|| black_box(openssl::sha::sha512(input))),
        );
    }
}

fn sha512_256(c: &mut Criterion) {
    let mut group = c.benchmark_group("sha512-256");
    for (size, size_name) in criterion::HASH_SIZES {
        let input = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_with_input(BenchmarkId::new("ring", size_name), &input, |b, input| {
            b.iter(|| test_ring_sha512_256(input))
        });
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_with_input(
            BenchmarkId::new("aws-lc-rs", size_name),
            &input,
            |b, input| b.iter(|| test_aws_sha512_256(input)),
        );
        group.bench_with_input(
            BenchmarkId::new("rustcrypto", size_name),
            &input,
            |b, input| b.iter(|| test_rc_sha512_256(input)),
        );
        group.bench_with_input(BenchmarkId::new("rind", size_name), &input, |b, input| {
            b.iter(|| test_rind_sha512_256(input))
        });
    }
}

// Many small updates show the cost of dispatching each one on the algorithm.
fn sha256_updates(c: &mut Criterion) {
    let mut group = c.benchmark_group("sha256-updates");
    let input = vec![0u8; 4096];
    group.throughput(Throughput::Bytes(input.len() as u64));
    for (chunk, chunk_name) in [(1, "1B"), (16, "16B")] {
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_with_input(
            BenchmarkId::new("aws-lc-rs", chunk_name),
            &input,
            |b, input| {
                b.iter(|| {
                    let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::SHA256);
                    for part in input.chunks(chunk) {
                        ctx.update(part);
                    }
                    black_box(ctx.finish());
                })
            },
        );
        group.bench_with_input(BenchmarkId::new("rind", chunk_name), &input, |b, input| {
            b.iter(|| {
                let mut ctx = rind::digest::Context::new(&rind::digest::SHA256);
                for part in input.chunks(chunk) {
                    ctx.update(part);
                }
                black_box(ctx.finish());
            })
        });
    }
}

criterion_group!(benches, sha256, sha512, sha512_256, sha256_updates);
criterion_main!(benches);
