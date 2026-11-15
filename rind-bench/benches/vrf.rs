//! RFC 9381's ECVRF try-and-increment suites: a proof of one key
//! transparency label, and its verification from the encoded proof against a
//! parsed public key.
mod criterion;
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

const ALPHA: &[u8] = b"alice@example.com";
const SEED: [u8; 32] = [0x42; 32];

fn prove(c: &mut Criterion) {
    {
        let mut group = c.benchmark_group("vrf-edwards25519-prove");
        group.throughput(Throughput::Elements(1));

        group.bench_function("rind", |b| {
            use rind::vrf::{ECVRF_EDWARDS25519_SHA512_TAI, SecretKey};
            let key = SecretKey::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, &SEED).unwrap();
            b.iter(|| black_box(key.prove(ALPHA).unwrap()));
        });

        group.bench_function("rustcrypto", |b| {
            use vrf_rfc9381::ec::edwards25519::tai::EdVrfEdwards25519TaiSecretKey;
            use vrf_rfc9381::{Proof, Prover};
            let key = EdVrfEdwards25519TaiSecretKey::from_slice(&SEED).unwrap();
            b.iter(|| {
                let proof = key.prove(ALPHA).unwrap();
                black_box((
                    proof.encode_to_pi(),
                    proof.proof_to_hash(edwards()).unwrap(),
                ))
            });
        });
    }

    let mut group = c.benchmark_group("vrf-p256-prove");
    group.throughput(Throughput::Elements(1));

    group.bench_function("rind", |b| {
        use rind::vrf::{ECVRF_P256_SHA256_TAI, SecretKey};
        let key = SecretKey::from_bytes(&ECVRF_P256_SHA256_TAI, &SEED).unwrap();
        b.iter(|| black_box(key.prove(ALPHA).unwrap()));
    });

    group.bench_function("rustcrypto", |b| {
        use vrf_rfc9381::ec::p256::tai::EcVrfP256TaiSecretKey;
        use vrf_rfc9381::{Proof, Prover};
        let key = EcVrfP256TaiSecretKey::from_slice(&SEED).unwrap();
        b.iter(|| {
            let proof = key.prove(ALPHA).unwrap();
            black_box((proof.encode_to_pi(), proof.proof_to_hash(p256()).unwrap()))
        });
    });
}

// rind's `prove` returns the proof and its output together, so the other
// library's rows encode both too.
fn edwards() -> vrf_rfc9381::Ciphersuite {
    vrf_rfc9381::Ciphersuite::ECVRF_EDWARDS25519_SHA512_TAI
}

fn p256() -> vrf_rfc9381::Ciphersuite {
    vrf_rfc9381::Ciphersuite::ECVRF_P256_SHA256_TAI
}

// Both libraries prove the same output from the same seed, and each verifies
// the other's proof, so the rows time the same suites.
fn check_interop() {
    use rind::vrf::{ECVRF_EDWARDS25519_SHA512_TAI, ECVRF_P256_SHA256_TAI, PublicKey, SecretKey};
    use vrf_rfc9381::ec::edwards25519::tai::{EdVrfEdwards25519Tai, EdVrfEdwards25519TaiSecretKey};
    use vrf_rfc9381::ec::p256::tai::{EcVrfP256Tai, EcVrfP256TaiSecretKey};
    use vrf_rfc9381::{Prover, VRF};

    let ours = SecretKey::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, &SEED).unwrap();
    let theirs = EdVrfEdwards25519TaiSecretKey::from_slice(&SEED).unwrap();
    let (proof, output) = ours.prove(ALPHA).unwrap();
    let pi = EdVrfEdwards25519Tai.prove(&theirs, ALPHA).unwrap();
    let theirs_output = EdVrfEdwards25519Tai
        .verify(&theirs.verifier(), ALPHA, proof.as_ref())
        .unwrap();
    assert_eq!(output.as_ref(), theirs_output.as_slice());
    let public_key =
        PublicKey::new(&ECVRF_EDWARDS25519_SHA512_TAI, ours.public_key().as_ref()).unwrap();
    public_key.verify(ALPHA, &pi).unwrap();

    let ours = SecretKey::from_bytes(&ECVRF_P256_SHA256_TAI, &SEED).unwrap();
    let theirs = EcVrfP256TaiSecretKey::from_slice(&SEED).unwrap();
    let (proof, output) = ours.prove(ALPHA).unwrap();
    let pi = EcVrfP256Tai.prove(&theirs, ALPHA).unwrap();
    let theirs_output = EcVrfP256Tai
        .verify(&theirs.verifier(), ALPHA, proof.as_ref())
        .unwrap();
    assert_eq!(output.as_ref(), theirs_output.as_slice());
    let public_key = PublicKey::new(&ECVRF_P256_SHA256_TAI, ours.public_key().as_ref()).unwrap();
    public_key.verify(ALPHA, &pi).unwrap();
}

fn verify(c: &mut Criterion) {
    check_interop();
    {
        let mut group = c.benchmark_group("vrf-edwards25519-verify");
        group.throughput(Throughput::Elements(1));

        group.bench_function("rind", |b| {
            use rind::vrf::{ECVRF_EDWARDS25519_SHA512_TAI, PublicKey, SecretKey};
            let key = SecretKey::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, &SEED).unwrap();
            let (proof, _) = key.prove(ALPHA).unwrap();
            let public_key =
                PublicKey::new(&ECVRF_EDWARDS25519_SHA512_TAI, key.public_key().as_ref()).unwrap();
            b.iter(|| black_box(public_key.verify(ALPHA, proof.as_ref()).unwrap()));
        });

        group.bench_function("rustcrypto", |b| {
            use vrf_rfc9381::ec::edwards25519::tai::{
                EdVrfEdwards25519Tai, EdVrfEdwards25519TaiSecretKey,
            };
            use vrf_rfc9381::{Prover, VRF};
            let key = EdVrfEdwards25519TaiSecretKey::from_slice(&SEED).unwrap();
            let pi = EdVrfEdwards25519Tai.prove(&key, ALPHA).unwrap();
            let public_key = key.verifier();
            b.iter(|| {
                black_box(
                    EdVrfEdwards25519Tai
                        .verify(&public_key, ALPHA, &pi)
                        .unwrap(),
                )
            });
        });
    }

    let mut group = c.benchmark_group("vrf-p256-verify");
    group.throughput(Throughput::Elements(1));

    group.bench_function("rind", |b| {
        use rind::vrf::{ECVRF_P256_SHA256_TAI, PublicKey, SecretKey};
        let key = SecretKey::from_bytes(&ECVRF_P256_SHA256_TAI, &SEED).unwrap();
        let (proof, _) = key.prove(ALPHA).unwrap();
        let public_key = PublicKey::new(&ECVRF_P256_SHA256_TAI, key.public_key().as_ref()).unwrap();
        b.iter(|| black_box(public_key.verify(ALPHA, proof.as_ref()).unwrap()));
    });

    group.bench_function("rustcrypto", |b| {
        use vrf_rfc9381::ec::p256::tai::{EcVrfP256Tai, EcVrfP256TaiSecretKey};
        use vrf_rfc9381::{Prover, VRF};
        let key = EcVrfP256TaiSecretKey::from_slice(&SEED).unwrap();
        let pi = EcVrfP256Tai.prove(&key, ALPHA).unwrap();
        let public_key = key.verifier();
        b.iter(|| black_box(EcVrfP256Tai.verify(&public_key, ALPHA, &pi).unwrap()));
    });
}

criterion_group!(benches, prove, verify);
criterion_main!(benches);
