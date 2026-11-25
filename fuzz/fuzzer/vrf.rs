#![no_main]

//! ECVRF under a seed the fuzzer writes, with the public key, input, and
//! proof tampered with in flight.
//!
//! No reference implements ECVRF on aws-lc, so this checks rind against
//! itself and the protocol's independent oracles, `akd_core` for
//! Edwards25519 and `vrf-rfc9381` for P-256: each proves the same bytes for
//! the key and input, an untampered proof verifies to the proved output, and
//! a tampered one is refused rather than panicking or verifying, and the
//! oracle verifies every proof rind does, to the same output where it
//! exposes one. Both load or refuse the same seeds, so P-256's scalars
//! reach 1, n - 1, and the values past n that are refused.

use akd_core::ecvrf::{VRFPrivateKey, VRFPublicKey};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::Error;
use rind::vrf::*;
use vrf_rfc9381::ec::p256::EcVrfProof;
use vrf_rfc9381::ec::p256::tai::{EcVrfP256TaiPublicKey, EcVrfP256TaiSecretKey};
use vrf_rfc9381::{Proof as _, Prover as _, Verifier as _};

mod edit;

const ALGORITHMS: [&Algorithm; 2] = [&ECVRF_EDWARDS25519_SHA512_TAI, &ECVRF_P256_SHA256_TAI];

#[derive(Arbitrary, Debug)]
struct Input {
    algorithm: u8,
    seed: Vec<u8>,
    alpha: Vec<u8>,
    public_key: edit::Edit,
    proof: edit::Edit,
    alpha_edit: edit::Edit,
}

fuzz_target!(|input: Input| {
    let index = usize::from(input.algorithm % 2);
    let secret_key = KeyPair::from_seed(ALGORITHMS[index], &input.seed);
    let theirs = independent_prove(index, &input.seed, &input.alpha);
    let Ok(secret_key) = secret_key else {
        assert!(theirs.is_none());
        return;
    };
    assert_eq!(secret_key.to_seed().as_ref(), &input.seed[..]);
    let (proof, output) = secret_key
        .prove(&input.alpha)
        .expect("try-and-increment finds a point");
    assert_eq!(theirs.as_deref(), Some(proof.as_ref()));

    let mut public_key = secret_key.public_key().as_ref().to_vec();
    let mut changed = input.public_key.apply(&mut public_key);
    let Ok(public_key) = PublicKey::new(ALGORITHMS[index], &public_key) else {
        assert!(changed);
        return;
    };
    let mut proof = proof.as_ref().to_vec();
    changed |= input.proof.apply(&mut proof);
    let mut alpha = input.alpha.clone();
    changed |= input.alpha_edit.apply(&mut alpha);

    match public_key.verify(&alpha, &proof) {
        Ok(verified) => {
            assert!(!changed);
            assert_eq!(verified.as_ref(), output.as_ref());
            assert!(independent_verify(
                index,
                public_key.as_ref(),
                &alpha,
                &proof,
                output.as_ref()
            ));
        }
        Err(e) => {
            assert_eq!(e, Error::BadSignature);
            assert!(changed);
        }
    }
});

/// The oracle's proof of `alpha` under `seed`, or `None` if it refuses the
/// seed.
fn independent_prove(index: usize, seed: &[u8], alpha: &[u8]) -> Option<Vec<u8>> {
    match index {
        0 => Some(
            VRFPrivateKey::try_from(seed)
                .ok()?
                .prove(alpha)
                .to_bytes()
                .to_vec(),
        ),
        _ => Some(
            EcVrfP256TaiSecretKey::from_slice(seed)
                .ok()?
                .prove(alpha)
                .unwrap()
                .encode_to_pi()
                .to_vec(),
        ),
    }
}

/// Whether the oracle verifies `proof` of `alpha` under `public_key`, and,
/// where it exposes the output, to `output`. `akd_core` keeps its output
/// private, but it verifies the same proof bytes rind proves.
fn independent_verify(
    index: usize,
    public_key: &[u8],
    alpha: &[u8],
    proof: &[u8],
    output: &[u8],
) -> bool {
    match index {
        0 => {
            let (Ok(public_key), Ok(proof)) = (
                VRFPublicKey::try_from(public_key),
                akd_core::ecvrf::Proof::try_from(proof),
            ) else {
                return false;
            };
            public_key.verify(&proof, alpha).is_ok()
        }
        _ => {
            let (Ok(public_key), Ok(proof)) = (
                EcVrfP256TaiPublicKey::from_slice(public_key),
                EcVrfProof::decode_pi(proof),
            ) else {
                return false;
            };
            public_key
                .verify(alpha, proof)
                .is_ok_and(|verified| verified[..] == *output)
        }
    }
}
