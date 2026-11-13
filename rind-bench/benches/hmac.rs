#[macro_use]
mod criterion;
use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use hmac::{KeyInit, Mac};

/// A library's one-shot MAC: key, then message.
type OneShot = fn(&[u8], &[u8]);

fn rc<M: KeyInit + Mac>(key: &[u8], data: &[u8]) {
    let mut ctx = <M as KeyInit>::new_from_slice(key).unwrap();
    ctx.update(data);
    black_box(ctx.finalize());
}

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn graviola<H: graviola::hashing::Hash>(key: &[u8], data: &[u8]) {
    let mut ctx = graviola::hashing::hmac::Hmac::<H>::new(key);
    ctx.update(data);
    black_box(ctx.finish());
}

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
fn openssl(md: openssl::hash::MessageDigest, key: &[u8], data: &[u8]) {
    let key = openssl::pkey::PKey::hmac(key).unwrap();
    let mut signer = openssl::sign::Signer::new(md, &key).unwrap();
    signer.update(data).unwrap();
    black_box(signer.sign_to_vec().unwrap());
}

// Each row keys HMAC per message, as a one-off MAC does; the `reused-key`
// rows sign with a long-lived key, such as a STUN or SRTP session's.
fn bench(
    c: &mut Criterion,
    name: &str,
    ring: ring::hmac::Algorithm,
    aws: aws!(hmac::Algorithm),
    ours: &'static rind::hmac::Algorithm,
    key: &[u8],
    others: &[(&str, OneShot)],
) {
    #[cfg(any(target_arch = "xtensa", target_os = "none"))]
    let _ = aws;
    let mut group = c.benchmark_group(name);

    for (size, size_name) in criterion::HASH_SIZES {
        let input = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_with_input(BenchmarkId::new("ring", size_name), &input, |b, input| {
            b.iter(|| {
                let mut ctx = ring::hmac::Context::with_key(&ring::hmac::Key::new(ring, key));
                ctx.update(input);
                black_box(ctx.sign())
            })
        });
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_with_input(
            BenchmarkId::new("aws-lc-rs", size_name),
            &input,
            |b, input| {
                b.iter(|| {
                    let mut ctx =
                        aws_lc_rs::hmac::Context::with_key(&aws_lc_rs::hmac::Key::new(aws, key));
                    ctx.update(input);
                    black_box(ctx.sign())
                })
            },
        );
        for (library, mac) in others {
            group.bench_with_input(BenchmarkId::new(*library, size_name), &input, |b, input| {
                b.iter(|| mac(key, input))
            });
        }
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_with_input(BenchmarkId::new(lib, size_name), &input, |b, input| {
                b.iter(|| black_box(rind::hmac::sign(&rind::hmac::Key::new(ours, key), input)))
            });
        }

        let ring_key = ring::hmac::Key::new(ring, key);
        group.bench_with_input(
            BenchmarkId::new("ring/reused-key", size_name),
            &input,
            |b, input| b.iter(|| black_box(ring::hmac::sign(&ring_key, input))),
        );
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        let aws_key = aws_lc_rs::hmac::Key::new(aws, key);
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_with_input(
            BenchmarkId::new("aws-lc-rs/reused-key", size_name),
            &input,
            |b, input| b.iter(|| black_box(aws_lc_rs::hmac::sign(&aws_key, input))),
        );
        let rind_key = rind::hmac::Key::new(ours, key);
        group.bench_with_input(
            BenchmarkId::new("rind/reused-key", size_name),
            &input,
            |b, input| b.iter(|| black_box(rind::hmac::sign(&rind_key, input))),
        );
    }
}

fn hmac(c: &mut Criterion) {
    let sha1: Vec<(&str, OneShot)> = vec![("rustcrypto", rc::<hmac::Hmac<sha1::Sha1>>)];
    let sha256: Vec<(&str, OneShot)> = vec![
        ("rustcrypto", rc::<hmac::Hmac<sha2::Sha256>>),
        ("libcrux", |key, data| {
            let mut tag = [0u8; 32];
            libcrux_hmac::hmac_sha2_256(&mut tag, key, data);
            black_box(tag);
        }),
    ];
    let sha384: Vec<(&str, OneShot)> = vec![
        ("rustcrypto", rc::<hmac::Hmac<sha2::Sha384>>),
        ("libcrux", |key, data| {
            let mut tag = [0u8; 48];
            libcrux_hmac::hmac_sha2_384(&mut tag, key, data);
            black_box(tag);
        }),
    ];
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    let (sha256, sha384) = {
        use graviola::hashing::{Sha256, Sha384};
        let with = |mut rows: Vec<(&'static str, OneShot)>, mac: OneShot| {
            rows.push(("graviola", mac));
            rows
        };
        (
            with(sha256, graviola::<Sha256>),
            with(sha384, graviola::<Sha384>),
        )
    };
    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    let (sha1, sha256, sha384) = {
        use openssl::hash::MessageDigest;
        let with = |mut rows: Vec<(&'static str, OneShot)>, mac: OneShot| {
            rows.push(("openssl", mac));
            rows
        };
        (
            with(sha1, |key, data| openssl(MessageDigest::sha1(), key, data)),
            with(sha256, |key, data| {
                openssl(MessageDigest::sha256(), key, data)
            }),
            with(sha384, |key, data| {
                openssl(MessageDigest::sha384(), key, data)
            }),
        )
    };

    bench(
        c,
        "hmac-sha1",
        ring::hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
        aws!(hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY),
        &rind::hmac::legacy::HMAC_SHA1,
        &[0xff; 20],
        &sha1,
    );
    bench(
        c,
        "hmac-sha256",
        ring::hmac::HMAC_SHA256,
        aws!(hmac::HMAC_SHA256),
        &rind::hmac::HMAC_SHA256,
        &[0xff; 32],
        &sha256,
    );
    bench(
        c,
        "hmac-sha384",
        ring::hmac::HMAC_SHA384,
        aws!(hmac::HMAC_SHA384),
        &rind::hmac::HMAC_SHA384,
        &[0xff; 48],
        &sha384,
    );
}

criterion_group!(benches, hmac);
criterion_main!(benches);
