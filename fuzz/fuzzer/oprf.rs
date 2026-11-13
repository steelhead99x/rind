#![no_main]

//! The VOPRF with the blinded elements, evaluated elements, and proof
//! tampered with in flight, over every suite.
//!
//! No reference implements RFC 9497 on aws-lc, so this checks rind against
//! itself: an untampered batch finalizes to the server's direct evaluation of
//! each input, and a tampered one is refused rather than panicking or
//! finalizing.

use std::sync::LazyLock;

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::Error;
use rind::oprf::voprf::{Blind, ServerKey};
use rind::oprf::{P256_SHA256, P384_SHA384, P521_SHA512, RISTRETTO255_SHA512, Suite};

mod edit;

const SUITES: [&Suite; 4] = [
    &RISTRETTO255_SHA512,
    &P256_SHA256,
    &P384_SHA384,
    &P521_SHA512,
];

static KEYS: LazyLock<[ServerKey; 4]> =
    LazyLock::new(|| SUITES.map(|suite| ServerKey::derive(suite, &[0x42; 32], b"fuzz").unwrap()));

#[derive(Arbitrary, Debug)]
struct Input {
    suite: u8,
    inputs: Vec<Vec<u8>>,
    blinded: edit::Edit,
    evaluated: edit::Edit,
    proof: edit::Edit,
}

fuzz_target!(|input: Input| {
    let index = usize::from(input.suite % 4);
    let (suite, key) = (SUITES[index], &KEYS[index]);
    let inputs = &input.inputs[..input.inputs.len().min(8)];

    let mut blinds = Vec::new();
    let mut blinded = Vec::new();
    for input in inputs {
        // RFC 9497 5.1 refuses inputs of `2^16 - 1` bytes or more.
        if input.len() >= usize::from(u16::MAX) {
            assert_eq!(Blind::new(suite, input).unwrap_err(), Error::WrongLength);
            assert_eq!(key.evaluate(input).unwrap_err(), Error::WrongLength);
            return;
        }
        let (blind, element) = Blind::new(suite, input).unwrap();
        blinds.push(blind);
        blinded.extend_from_slice(element.as_ref());
    }
    let mut changed = input.blinded.apply(&mut blinded);
    let Ok((evaluated, proof)) = key.blind_evaluate(&blinded) else {
        assert!(changed || inputs.is_empty());
        return;
    };
    let mut evaluated = evaluated.as_ref().to_vec();
    changed |= input.evaluated.apply(&mut evaluated);
    let mut proof = proof.as_ref().to_vec();
    changed |= input.proof.apply(&mut proof);

    match Blind::finalize_batch(blinds, &evaluated, &proof, key.public_key()) {
        Ok(outputs) => {
            assert!(!changed);
            for (output, input) in outputs.iter().zip(inputs) {
                assert_eq!(output.as_ref(), key.evaluate(input).unwrap().as_ref());
            }
        }
        Err(_) => assert!(changed),
    }
});
