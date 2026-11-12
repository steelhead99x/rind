#![no_main]

//! RSA blind signatures with each message tampered with in flight: the
//! client's blinded message, the server's reply, and the finalized
//! signature, and a key the fuzzer writes.
//!
//! No reference implements blind RSA on aws-lc, so this checks rind against
//! itself: an untampered exchange verifies, and a tampered message fails as
//! its step documents, rather than panicking or verifying.

use std::sync::LazyLock;

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::Error;
use rind::blind_rsa::*;

mod edit;

const PKCS8: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der");

const ALGORITHMS: [&Algorithm; 4] = [
    &RSABSSA_SHA384_PSS_RANDOMIZED,
    &RSABSSA_SHA384_PSSZERO_RANDOMIZED,
    &RSABSSA_SHA384_PSS_DETERMINISTIC,
    &RSABSSA_SHA384_PSSZERO_DETERMINISTIC,
];

static KEYS: LazyLock<[KeyPair; 4]> =
    LazyLock::new(|| ALGORITHMS.map(|algorithm| KeyPair::from_pkcs8(algorithm, PKCS8).unwrap()));

#[derive(Arbitrary, Debug)]
struct Input {
    algorithm: u8,
    message: Vec<u8>,
    blinded: edit::Edit,
    reply: edit::Edit,
    signature: edit::Edit,
    spki: edit::Edit,
}

fuzz_target!(|input: Input| {
    let index = usize::from(input.algorithm % 4);
    let key_pair = &KEYS[index];
    let public_key = key_pair.public_key();

    let mut spki = public_key.to_spki().as_ref().to_vec();
    let spki_changed = input.spki.apply(&mut spki);
    if let Ok(parsed) = PublicKey::new(ALGORITHMS[index], &spki) {
        // Only a change to the modulus or exponent survives, which makes
        // another key.
        if !spki_changed {
            assert_eq!(parsed.to_spki().as_ref(), public_key.to_spki().as_ref());
        }
    }

    let (blinded, blinding) = public_key.blind(&input.message).unwrap();
    let mut blinded = blinded.as_ref().to_vec();
    let blinded_changed = input.blinded.apply(&mut blinded);
    let reply = match key_pair.blind_sign(&blinded) {
        Ok(reply) => reply,
        Err(e) => {
            assert_eq!(e, Error::WrongLength);
            assert!(blinded_changed);
            return;
        }
    };
    let mut reply = reply.as_ref().to_vec();
    let changed = input.reply.apply(&mut reply) | blinded_changed;
    let signature = match blinding.finalize(&reply) {
        Ok(signature) => signature,
        Err(e) => {
            assert_eq!(e, Error::BadSignature);
            assert!(changed);
            return;
        }
    };
    assert!(!changed);

    let mut signature = signature.as_ref().to_vec();
    let changed = input.signature.apply(&mut signature);
    let result = public_key.verify(&input.message, &signature);
    assert_eq!(result.is_ok(), !changed, "{result:?}");
});
