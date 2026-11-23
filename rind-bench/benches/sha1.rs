#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod criterion;
#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
#[cfg(not(target_arch = "xtensa"))]
use sha1::Digest;

#[cfg(not(target_arch = "xtensa"))]
fn test_ring_sha1(data: &[u8]) {
    let mut ctx = ring::digest::Context::new(&ring::digest::SHA1_FOR_LEGACY_USE_ONLY);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
#[cfg(not(target_arch = "xtensa"))]
fn test_aws_sha1(data: &[u8]) {
    let mut ctx = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::SHA1_FOR_LEGACY_USE_ONLY);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rc_sha1(data: &[u8]) {
    let mut ctx = sha1::Sha1::new();
    ctx.update(data);
    black_box(ctx.finalize());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rind_sha1(data: &[u8]) {
    let mut ctx = rind::digest::Context::new(&rind::digest::legacy::SHA1);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(not(target_arch = "xtensa"))]
fn test_vg_sha1(data: &[u8]) {
    let mut ctx = verified_garbage::hashes::sha1::Sha1::new();
    ctx.update(data);
    black_box(ctx.finalize());
}

#[cfg(not(target_arch = "xtensa"))]
fn sha1(c: &mut Criterion) {
    let mut group = c.benchmark_group("sha1");
    for (size, size_name) in criterion::HASH_SIZES {
        let input = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_with_input(BenchmarkId::new("ring", size_name), &input, |b, input| {
            b.iter(|| test_ring_sha1(input))
        });
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_with_input(
            BenchmarkId::new("aws-lc-rs", size_name),
            &input,
            |b, input| b.iter(|| test_aws_sha1(input)),
        );
        group.bench_with_input(
            BenchmarkId::new("rustcrypto", size_name),
            &input,
            |b, input| b.iter(|| test_rc_sha1(input)),
        );
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_with_input(BenchmarkId::new(lib, size_name), &input, |b, input| {
                b.iter(|| test_rind_sha1(input))
            });
        }
        let mut ctx = verified_garbage::hashes::sha1::Sha1::new();
        ctx.update(&input);
        assert_eq!(
            ctx.finalize(),
            rind::digest::digest(&rind::digest::legacy::SHA1, &input).as_ref()
        );
        group.bench_with_input(
            BenchmarkId::new("verified-garbage", size_name),
            &input,
            |b, input| b.iter(|| test_vg_sha1(input)),
        );
    }
}

#[cfg(not(target_arch = "xtensa"))]
criterion_group!(benches, sha1);
#[cfg(not(target_arch = "xtensa"))]
criterion_main!(benches);
