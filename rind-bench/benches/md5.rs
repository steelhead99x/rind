mod criterion;
use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use md5::Digest;

// aws-lc's MD5, which aws-lc-rs does not export, through aws-lc-sys.
#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
fn test_aws_md5(data: &[u8]) {
    let mut out = [0u8; 16];
    // SAFETY: `data` is readable for its length, and `out` is writable for
    // MD5's 16-byte digest.
    let ok = unsafe {
        aws_lc_sys::EVP_Digest(
            data.as_ptr().cast(),
            data.len(),
            out.as_mut_ptr(),
            core::ptr::null_mut(),
            aws_lc_sys::EVP_md5(),
            core::ptr::null_mut(),
        )
    };
    assert_eq!(ok, 1);
    black_box(out);
}

fn test_rc_md5(data: &[u8]) {
    let mut ctx = md5::Md5::new();
    ctx.update(data);
    black_box(ctx.finalize());
}

fn test_rind_md5(data: &[u8]) {
    let mut ctx = rind::digest::Context::new(&rind::digest::legacy::MD5);
    ctx.update(data);
    black_box(ctx.finish());
}

fn md5(c: &mut Criterion) {
    let mut group = c.benchmark_group("md5");
    for (size, size_name) in criterion::HASH_SIZES {
        let input = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));

        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_with_input(
            BenchmarkId::new("aws-lc-rs", size_name),
            &input,
            |b, input| b.iter(|| test_aws_md5(input)),
        );
        group.bench_with_input(
            BenchmarkId::new("rustcrypto", size_name),
            &input,
            |b, input| b.iter(|| test_rc_md5(input)),
        );
        group.bench_with_input(BenchmarkId::new("rind", size_name), &input, |b, input| {
            b.iter(|| test_rind_md5(input))
        });
    }
}

criterion_group!(benches, md5);
criterion_main!(benches);
