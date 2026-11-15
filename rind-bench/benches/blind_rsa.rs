//! RFC 9474's RSABSSA-SHA384-PSS-Deterministic with a 2048-bit key, Privacy
//! Pass's publicly verifiable tokens: the client's blind, the server's
//! signature, the client's finalize, and anyone's verify. Both libraries use
//! the same key.
mod criterion;
use std::hint::black_box;

use blind_rsa_signatures::{DefaultRng, Deterministic, PSS, Sha384};
use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use rind::blind_rsa::{KeyPair, PublicKey, RSABSSA_SHA384_PSS_DETERMINISTIC as ALGORITHM};

const MESSAGE: &[u8] = b"a Privacy Pass token input";

type RcSecretKey = blind_rsa_signatures::SecretKey<Sha384, PSS, Deterministic>;
type RcPublicKey = blind_rsa_signatures::PublicKey<Sha384, PSS, Deterministic>;

struct Keys {
    rind: KeyPair,
    rind_public: PublicKey,
    rustcrypto: RcSecretKey,
    rustcrypto_public: RcPublicKey,
}

fn keys() -> Keys {
    let rind = KeyPair::generate(&ALGORITHM, rind::rsa::KeySize::Rsa2048).unwrap();
    let rustcrypto = RcSecretKey::from_der(rind.to_pkcs8().as_ref()).unwrap();
    let keys = Keys {
        rind_public: rind.public_key(),
        rustcrypto_public: rustcrypto.public_key().unwrap(),
        rind,
        rustcrypto,
    };
    // Each library verifies the other's signature, so the rows time the same
    // scheme.
    let (blinded, blinding) = keys.rind_public.blind(MESSAGE).unwrap();
    let signature = blinding
        .finalize(keys.rind.blind_sign(blinded.as_ref()).unwrap().as_ref())
        .unwrap();
    keys.rustcrypto_public
        .verify(
            &blind_rsa_signatures::Signature(signature.as_ref().to_vec()),
            None,
            MESSAGE,
        )
        .unwrap();
    let blinded = keys
        .rustcrypto_public
        .blind(&mut DefaultRng, MESSAGE)
        .unwrap();
    let signature = keys
        .rustcrypto_public
        .finalize(
            &keys.rustcrypto.blind_sign(&blinded.blind_message).unwrap(),
            &blinded,
            MESSAGE,
        )
        .unwrap();
    keys.rind_public.verify(MESSAGE, &signature).unwrap();
    keys
}

fn bench(c: &mut Criterion) {
    let keys = keys();

    let mut group = c.benchmark_group("blind-rsa2048-blind");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
        b.iter(|| black_box(keys.rind_public.blind(MESSAGE).unwrap()));
    });
    group.bench_function("rustcrypto", |b| {
        b.iter(|| {
            black_box(
                keys.rustcrypto_public
                    .blind(&mut DefaultRng, MESSAGE)
                    .unwrap(),
            )
        });
    });
    group.finish();

    let mut group = c.benchmark_group("blind-rsa2048-sign");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
        let (blinded, _) = keys.rind_public.blind(MESSAGE).unwrap();
        b.iter(|| black_box(keys.rind.blind_sign(blinded.as_ref()).unwrap()));
    });
    group.bench_function("rustcrypto", |b| {
        let blinded = keys
            .rustcrypto_public
            .blind(&mut DefaultRng, MESSAGE)
            .unwrap();
        b.iter(|| black_box(keys.rustcrypto.blind_sign(&blinded.blind_message).unwrap()));
    });
    group.finish();

    // rind's finalize consumes its blinding, so each iteration blinds afresh,
    // untimed. Both check the unblinded signature, as RFC 9474 requires.
    let mut group = c.benchmark_group("blind-rsa2048-finalize");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
        b.iter_batched(
            || {
                let (blinded, blinding) = keys.rind_public.blind(MESSAGE).unwrap();
                (blinding, keys.rind.blind_sign(blinded.as_ref()).unwrap())
            },
            |(blinding, reply)| black_box(blinding.finalize(reply.as_ref()).unwrap()),
            BatchSize::SmallInput,
        );
    });
    group.bench_function("rustcrypto", |b| {
        let blinded = keys
            .rustcrypto_public
            .blind(&mut DefaultRng, MESSAGE)
            .unwrap();
        let reply = keys.rustcrypto.blind_sign(&blinded.blind_message).unwrap();
        b.iter(|| {
            black_box(
                keys.rustcrypto_public
                    .finalize(&reply, &blinded, MESSAGE)
                    .unwrap(),
            )
        });
    });
    group.finish();

    let mut group = c.benchmark_group("blind-rsa2048-verify");
    group.throughput(Throughput::Elements(1));
    let (blinded, blinding) = keys.rind_public.blind(MESSAGE).unwrap();
    let signature = blinding
        .finalize(keys.rind.blind_sign(blinded.as_ref()).unwrap().as_ref())
        .unwrap();
    group.bench_function("rind", |b| {
        b.iter(|| {
            keys.rind_public
                .verify(MESSAGE, signature.as_ref())
                .unwrap()
        });
    });
    group.bench_function("rustcrypto", |b| {
        let signature = blind_rsa_signatures::Signature(signature.as_ref().to_vec());
        b.iter(|| {
            keys.rustcrypto_public
                .verify(&signature, None, MESSAGE)
                .unwrap()
        });
    });
}

criterion_group!(benches, bench);
criterion_main!(benches);
