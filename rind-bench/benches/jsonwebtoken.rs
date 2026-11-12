//! Per-token cost of each jsonwebtoken provider.
//!
//! jsonwebtoken builds a signer or verifier from the key on every token, so
//! `token` is what a caller pays, and `load` is the part spent on the key.

mod criterion;
use std::hint::black_box;

use aws_lc_rs::rand::SystemRandom;
use aws_lc_rs::signature::{
    ECDSA_P256_SHA256_FIXED_SIGNING, ECDSA_P384_SHA384_FIXED_SIGNING, EcdsaKeyPair,
    EcdsaSigningAlgorithm, Ed25519KeyPair, KeyPair,
};
use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use jsonwebtoken::crypto::{CryptoProvider, aws_lc};
use jsonwebtoken::{Algorithm, DecodingKey, EncodingKey};

fn providers() -> [(&'static str, &'static CryptoProvider); 2] {
    [
        ("aws-lc-rs", &aws_lc::DEFAULT_PROVIDER),
        ("rind", &rind_jsonwebtoken::DEFAULT_PROVIDER),
    ]
}

// The header and claims of a typical token, as jsonwebtoken signs them.
const MESSAGE: &[u8] = b"eyJhbGciOiJFUzI1NiIsInR5cCI6IkpXVCJ9.eyJyb290IjoiZGVtbyIsInB1dCI6WyIiXSwiZ2V0IjpbIiJdLCJleHAiOjE3OTI4MTYwMDAsImlhdCI6MTc2MTI4MDAwMH0";

fn ecdsa(signing: &'static EcdsaSigningAlgorithm) -> (EncodingKey, DecodingKey) {
    let pkcs8 = EcdsaKeyPair::generate_pkcs8(signing, &SystemRandom::new()).unwrap();
    let pair = EcdsaKeyPair::from_pkcs8(signing, pkcs8.as_ref()).unwrap();
    (
        EncodingKey::from_ec_der(pkcs8.as_ref()),
        DecodingKey::from_ec_der(pair.public_key().as_ref()),
    )
}

// Keys in the forms a JWK becomes: PKCS#8 that carries the public key, and
// RSA verified from its modulus and exponent.
fn keys() -> Vec<(Algorithm, EncodingKey, DecodingKey)> {
    let secret = b"a shared secret of thirty-two by";
    let (es256_private, es256_public) = ecdsa(&ECDSA_P256_SHA256_FIXED_SIGNING);
    let (es384_private, es384_public) = ecdsa(&ECDSA_P384_SHA384_FIXED_SIGNING);

    let ed25519 = Ed25519KeyPair::generate_pkcs8(&SystemRandom::new()).unwrap();
    let ed25519_public = Ed25519KeyPair::from_pkcs8(ed25519.as_ref())
        .unwrap()
        .public_key()
        .as_ref()
        .to_vec();

    let rsa = include_bytes!("../../rind/src/high/rsa/rsa2048.der");
    let rsa_public = rind::signature::RsaKeyPair::from_pkcs1(rsa)
        .unwrap()
        .public_key(&rind::signature::sign::RSA_PKCS1_SHA256);
    let (n, e) = (aws_lc::DEFAULT_PROVIDER
        .key_utils
        .rsa_pub_components_from_public_key)(rsa_public.as_ref())
    .unwrap();

    vec![
        (
            Algorithm::HS256,
            EncodingKey::from_secret(secret),
            DecodingKey::from_secret(secret),
        ),
        (Algorithm::ES256, es256_private, es256_public),
        (Algorithm::ES384, es384_private, es384_public),
        (
            Algorithm::EdDSA,
            EncodingKey::from_ed_der(ed25519.as_ref()),
            DecodingKey::from_ed_der(&ed25519_public),
        ),
        (
            Algorithm::RS256,
            EncodingKey::from_rsa_der(rsa),
            DecodingKey::from_rsa_raw_components(&n, &e),
        ),
    ]
}

fn sign(c: &mut Criterion) {
    for (algorithm, encoding, _) in keys() {
        let mut group = c.benchmark_group(format!("jwt-{algorithm:?}-sign").to_lowercase());
        group.throughput(Throughput::Elements(1));

        for (name, provider) in providers() {
            group.bench_function(format!("{name}/token"), |b| {
                b.iter(|| {
                    let signer = (provider.signer_factory)(&algorithm, &encoding).unwrap();
                    black_box(signer.try_sign(MESSAGE).unwrap());
                })
            });
            group.bench_function(format!("{name}/load"), |b| {
                b.iter(|| black_box((provider.signer_factory)(&algorithm, &encoding).unwrap()))
            });
        }
    }
}

fn verify(c: &mut Criterion) {
    for (algorithm, encoding, decoding) in keys() {
        let mut group = c.benchmark_group(format!("jwt-{algorithm:?}-verify").to_lowercase());
        group.throughput(Throughput::Elements(1));

        let signature = (aws_lc::DEFAULT_PROVIDER.signer_factory)(&algorithm, &encoding)
            .unwrap()
            .try_sign(MESSAGE)
            .unwrap();

        for (name, provider) in providers() {
            group.bench_function(format!("{name}/token"), |b| {
                b.iter(|| {
                    let verifier = (provider.verifier_factory)(&algorithm, &decoding).unwrap();
                    verifier.verify(MESSAGE, &signature).unwrap();
                })
            });
            group.bench_function(format!("{name}/load"), |b| {
                b.iter(|| black_box((provider.verifier_factory)(&algorithm, &decoding).unwrap()))
            });
        }
    }
}

criterion_group!(benches, sign, verify);
criterion_main!(benches);
