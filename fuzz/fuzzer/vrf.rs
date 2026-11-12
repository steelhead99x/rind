#![no_main]

//! ECVRF with the public key, input, and proof tampered with in flight.
//!
//! No reference implements ECVRF on aws-lc, so this checks rind against
//! itself: an untampered proof verifies to the proved output, and a tampered
//! one is refused rather than panicking or verifying.

use std::sync::LazyLock;

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::Error;
use rind::vrf::*;

mod edit;

const ALGORITHMS: [&Algorithm; 2] = [&ECVRF_EDWARDS25519_SHA512_TAI, &ECVRF_P256_SHA256_TAI];

static KEYS: LazyLock<[SecretKey; 2]> = LazyLock::new(|| {
    ALGORITHMS.map(|algorithm| SecretKey::from_bytes(algorithm, &[0x42; 32]).unwrap())
});

#[derive(Arbitrary, Debug)]
struct Input {
    algorithm: u8,
    alpha: Vec<u8>,
    public_key: edit::Edit,
    proof: edit::Edit,
    alpha_edit: edit::Edit,
}

fuzz_target!(|input: Input| {
    let index = usize::from(input.algorithm % 2);
    let secret_key = &KEYS[index];
    let (proof, output) = secret_key.prove(&input.alpha);

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
        }
        Err(e) => {
            assert_eq!(e, Error::BadSignature);
            assert!(changed);
        }
    }
});
