mod criterion;
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

const MESSAGE: &[u8] =
    b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";

fn sizes(c: &mut Criterion) {
    let keys: [(usize, &[u8]); 3] = [
        (2048, include_bytes!("../../rind/src/high/rsa/rsa2048.der")),
        (3072, include_bytes!("../../rind/src/high/rsa/rsa3072.der")),
        (4096, include_bytes!("../../rind/src/high/rsa/rsa4096.der")),
    ];
    for (bits, private_key) in keys {
        use rind::signature::{RsaKeyPair, sign};
        let key = RsaKeyPair::from_pkcs1(private_key).unwrap();
        let signature = key.sign(&sign::RSA_PKCS1_SHA256, MESSAGE).unwrap();
        let signature = signature.as_ref().to_vec();

        let mut group = c.benchmark_group(format!("rsa{bits}-sizes-pkcs1-sha256-sign"));
        group.throughput(Throughput::Elements(1));
        group.bench_function("aws-lc-rs", |b| {
            use aws_lc_rs::{rand, rsa, signature};
            let key = rsa::KeyPair::from_der(private_key).unwrap();
            let rng = rand::SystemRandom::new();
            let mut out = vec![0u8; bits / 8];
            b.iter(|| {
                black_box(key.sign(&signature::RSA_PKCS1_SHA256, &rng, MESSAGE, &mut out)).unwrap();
            })
        });
        group.bench_function("rind", |b| {
            b.iter(|| {
                black_box(key.sign(&sign::RSA_PKCS1_SHA256, MESSAGE)).unwrap();
            })
        });
        group.finish();

        let mut group = c.benchmark_group(format!("rsa{bits}-sizes-pkcs1-sha256-verify"));
        group.throughput(Throughput::Elements(1));
        group.bench_function("aws-lc-rs", |b| {
            use aws_lc_rs::signature::{self, KeyPair};
            let key = aws_lc_rs::rsa::KeyPair::from_der(private_key).unwrap();
            let public_key = key.public_key().as_ref().to_vec();
            let public_key = signature::UnparsedPublicKey::new(
                &signature::RSA_PKCS1_2048_8192_SHA256,
                public_key,
            );
            b.iter(|| {
                black_box(public_key.verify(MESSAGE, &signature)).unwrap();
            })
        });
        group.bench_function("rind", |b| {
            let public_key = key.public_key(&sign::RSA_PKCS1_SHA256);
            b.iter(|| {
                black_box(public_key.verify(MESSAGE, &signature)).unwrap();
            })
        });
        group.finish();
    }
}

criterion_group!(benches, sizes);
criterion_main!(benches);
