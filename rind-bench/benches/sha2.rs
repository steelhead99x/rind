#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod criterion;
#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
#[cfg(not(target_arch = "xtensa"))]
use sha2::Digest;

#[cfg(not(target_arch = "xtensa"))]
fn test_ring_sha256(data: &[u8]) {
    let mut ctx = ring::digest::Context::new(&ring::digest::SHA256);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_ring_sha512(data: &[u8]) {
    let mut ctx = ring::digest::Context::new(&ring::digest::SHA512);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_ring_sha512_256(data: &[u8]) {
    let mut ctx = ring::digest::Context::new(&ring::digest::SHA512_256);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
#[cfg(not(target_arch = "xtensa"))]
fn test_aws_sha256(data: &[u8]) {
    let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::SHA256);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
#[cfg(not(target_arch = "xtensa"))]
fn test_aws_sha512(data: &[u8]) {
    let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::SHA512);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
#[cfg(not(target_arch = "xtensa"))]
fn test_aws_sha512_256(data: &[u8]) {
    let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::SHA512_256);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rc_sha256(data: &[u8]) {
    let mut ctx = sha2::Sha256::new();
    ctx.update(data);
    black_box(ctx.finalize());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rc_sha512(data: &[u8]) {
    let mut ctx = sha2::Sha512::new();
    ctx.update(data);
    black_box(ctx.finalize());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rc_sha512_256(data: &[u8]) {
    let mut ctx = sha2::Sha512_256::new();
    ctx.update(data);
    black_box(ctx.finalize());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rind_sha256(data: &[u8]) {
    let mut ctx = rind::digest::Context::new(&rind::digest::SHA256);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rind_sha512(data: &[u8]) {
    let mut ctx = rind::digest::Context::new(&rind::digest::SHA512);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rind_sha512_256(data: &[u8]) {
    let mut ctx = rind::digest::Context::new(&rind::digest::SHA512_256);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_vg<H: verified_garbage::hashes::HashFunction>(data: &[u8]) {
    let mut ctx = H::new();
    ctx.update(data);
    black_box(ctx.finalize());
}

// verified-garbage's row, after checking its digest matches rind's.
#[cfg(not(target_arch = "xtensa"))]
fn vg_row<H: verified_garbage::hashes::HashFunction>(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    ours: &'static rind::digest::Algorithm,
    size_name: &str,
    input: &[u8],
) {
    let mut ctx = H::new();
    ctx.update(input);
    assert_eq!(
        ctx.finalize().as_ref(),
        rind::digest::digest(ours, input).as_ref()
    );
    group.bench_with_input(
        BenchmarkId::new("verified-garbage", size_name),
        input,
        |b, input| b.iter(|| test_vg::<H>(input)),
    );
}

#[cfg(not(target_arch = "xtensa"))]
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
        vg_row::<verified_garbage::hashes::sha256::Sha256>(
            &mut group,
            &rind::digest::SHA256,
            size_name,
            &input,
        );
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
        #[cfg(all(
            feature = "__bench_openssl",
            target_family = "unix",
            not(target_arch = "xtensa")
        ))]
        group.bench_with_input(
            BenchmarkId::new("openssl", size_name),
            &input,
            |b, input| b.iter(|| black_box(openssl::sha::sha256(input))),
        );
    }
}

#[cfg(not(target_arch = "xtensa"))]
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
        vg_row::<verified_garbage::hashes::sha512::Sha512>(
            &mut group,
            &rind::digest::SHA512,
            size_name,
            &input,
        );
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
        #[cfg(all(
            feature = "__bench_openssl",
            target_family = "unix",
            not(target_arch = "xtensa")
        ))]
        group.bench_with_input(
            BenchmarkId::new("openssl", size_name),
            &input,
            |b, input| b.iter(|| black_box(openssl::sha::sha512(input))),
        );
    }
}

#[cfg(not(target_arch = "xtensa"))]
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
        vg_row::<verified_garbage::hashes::sha512_256::Sha512_256>(
            &mut group,
            &rind::digest::SHA512_256,
            size_name,
            &input,
        );
    }
}

// Many small updates show the cost of dispatching each one on the algorithm.
#[cfg(not(target_arch = "xtensa"))]
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

// rind's one-shot `digest` beside its `Context` path, to show the guard's
// cost: `digest` enters DIT once, while `Context::update` (on a full block)
// and `finish` enter it once each. Not a like-for-like row against the other
// libraries, which hash through a context, so the report never reads it.
#[cfg(not(target_arch = "xtensa"))]
fn sha256_oneshot(c: &mut Criterion) {
    let mut group = c.benchmark_group("sha256-oneshot");
    for (size, size_name) in criterion::HASH_SIZES {
        let input = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_with_input(BenchmarkId::new(lib, size_name), &input, |b, input| {
                b.iter(|| {
                    black_box(rind::digest::digest(
                        &rind::digest::SHA256,
                        black_box(input),
                    ))
                })
            });
        }
    }
}

#[cfg(not(target_arch = "xtensa"))]
criterion_group!(
    benches,
    sha256,
    sha512,
    sha512_256,
    sha256_updates,
    sha256_oneshot
);
#[cfg(not(target_arch = "xtensa"))]
criterion_main!(benches);
