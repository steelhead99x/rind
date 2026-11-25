#![no_main]

//! The VOPRF with the blinded elements, evaluated elements, and proof
//! tampered with in flight, over every suite.
//!
//! No reference implements RFC 9497 on aws-lc, so this checks rind against
//! itself and the `voprf` crate: the crate derives the same key, evaluates
//! rind's blinded elements and each input as rind does, and finalizes rind's
//! evaluation and proof, and an untampered batch finalizes to the server's
//! direct evaluation of each input, and a tampered one is refused rather
//! than panicking or finalizing.
//!
//! On armv7 and the portable backend, `voprf` runs rind's own group
//! arithmetic, fiat-crypto's for the NIST suites and `curve25519-dalek` for
//! ristretto255, so there the textbook reference also hashes each input to
//! the group and multiplies by the key, and the crate checks only the
//! protocol above.

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rand_core_voprf::OsRng;
use rind::Error;
use rind::oprf::voprf::{Blind, ServerKey};
use rind::oprf::{P256_SHA256, P384_SHA384, P521_SHA512, RISTRETTO255_SHA512, Suite};
use voprf::{BlindedElement, EvaluationElement, Group, Proof, VoprfClient, VoprfServer};

mod edit;
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
mod oracle;

const SUITES: [&Suite; 4] = [
    &RISTRETTO255_SHA512,
    &P256_SHA256,
    &P384_SHA384,
    &P521_SHA512,
];

const SEED: [u8; 32] = [0x42; 32];
const INFO: &[u8] = b"fuzz";

static KEYS: std::sync::LazyLock<[ServerKey; 4]> =
    std::sync::LazyLock::new(|| SUITES.map(|suite| ServerKey::derive(suite, &SEED, INFO).unwrap()));

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
    match index {
        0 => matches_voprf!(voprf::Ristretto255, key, inputs, &blinded),
        1 => matches_voprf!(p256_voprf::NistP256, key, inputs, &blinded),
        2 => matches_voprf!(p384_voprf::NistP384, key, inputs, &blinded),
        _ => matches_voprf!(p521_voprf::NistP521, key, inputs, &blinded),
    }
    #[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
    reference::check(index, key, inputs, &blinded);

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

/// The `voprf` crate's server for suite `$cs`, from the same seed, has
/// rind's public key, evaluates each input and rind's blinded elements as
/// rind does, and its clients finalize rind's evaluation and proof of their
/// own blinded inputs to the direct outputs.
macro_rules! matches_voprf {
    ($cs:ty, $key:expr, $inputs:expr, $blinded:expr) => {{
        type G = <$cs as voprf::CipherSuite>::Group;
        let (key, inputs, blinded): (&ServerKey, &[Vec<u8>], &[u8]) = ($key, $inputs, $blinded);
        static THEIRS: std::sync::LazyLock<VoprfServer<$cs>> =
            std::sync::LazyLock::new(|| VoprfServer::new_from_seed(&SEED, INFO).unwrap());
        let theirs = &*THEIRS;
        assert_eq!(
            key.public_key().as_ref(),
            &G::serialize_elem(theirs.get_public_key())[..]
        );
        let direct: Vec<_> = inputs
            .iter()
            .map(|input| theirs.evaluate(input).unwrap())
            .collect();
        for (input, direct) in inputs.iter().zip(&direct) {
            assert_eq!(key.evaluate(input).unwrap().as_ref(), &direct[..]);
        }

        if !inputs.is_empty() {
            let element_len = blinded.len() / inputs.len();
            let elements: Vec<_> = blinded
                .chunks(element_len)
                .map(|element| BlindedElement::<$cs>::deserialize(element).unwrap())
                .collect();
            let evaluated = theirs.batch_blind_evaluate(&mut OsRng, &elements).unwrap();
            let evaluated: Vec<u8> = evaluated
                .messages
                .iter()
                .flat_map(|message| message.serialize())
                .collect();
            let (ours, _) = key.blind_evaluate(blinded).unwrap();
            assert_eq!(ours.as_ref(), evaluated);

            let mut clients = Vec::new();
            let mut blinded = Vec::new();
            for input in inputs {
                let result = VoprfClient::<$cs>::blind(input, &mut OsRng).unwrap();
                clients.push(result.state);
                blinded.extend_from_slice(&result.message.serialize());
            }
            let (evaluated, proof) = key.blind_evaluate(&blinded).unwrap();
            let messages: Vec<_> = evaluated
                .as_ref()
                .chunks(element_len)
                .map(|bytes| EvaluationElement::<$cs>::deserialize(bytes).unwrap())
                .collect();
            let proof = Proof::<$cs>::deserialize(proof.as_ref()).unwrap();
            let inputs = inputs.to_vec();
            let outputs = VoprfClient::batch_finalize(
                &inputs,
                &clients,
                &messages,
                &proof,
                theirs.get_public_key(),
            )
            .unwrap();
            for (output, direct) in outputs.zip(&direct) {
                assert_eq!(output.unwrap(), *direct);
            }
        }
    }};
}
use matches_voprf;

/// The textbook reference's group operations, which share no code with the
/// arithmetic rind and `voprf` run on armv7 and the portable backend.
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
mod reference {
    use num_bigint::BigUint;
    use rind::oprf::voprf::ServerKey;
    use sha2::Digest;

    use super::oracle::reference::{self, Edwards};

    /// Each suite's RFC 9497 identifier, in `SUITES`' order.
    const IDENTIFIERS: [&[u8]; 4] = [
        b"ristretto255-SHA512",
        b"P256-SHA256",
        b"P384-SHA384",
        b"P521-SHA512",
    ];

    /// rind's direct evaluation of each input is `Finalize` over the key
    /// times the input hashed to the group, and its evaluation of each
    /// blinded element is the key times that element.
    pub fn check(index: usize, key: &ServerKey, inputs: &[Vec<u8>], blinded: &[u8]) {
        // VOPRF's mode is 0x01.
        let dst = [b"HashToGroup-OPRFV1-\x01-", IDENTIFIERS[index]].concat();
        let scalar = key.to_scalar();
        let group = Group::new(index, scalar.as_ref());
        for input in inputs {
            let element = group.mul(&group.hash_to_group(input, &dst)).unwrap();
            let finalize = [
                &(input.len() as u16).to_be_bytes()[..],
                input,
                &(element.len() as u16).to_be_bytes(),
                &element,
                b"Finalize",
            ]
            .concat();
            let output = match index {
                0 | 3 => sha2::Sha512::digest(&finalize).to_vec(),
                1 => sha2::Sha256::digest(&finalize).to_vec(),
                _ => sha2::Sha384::digest(&finalize).to_vec(),
            };
            assert_eq!(key.evaluate(input).unwrap().as_ref(), output);
        }
        if inputs.is_empty() {
            return;
        }
        let (evaluated, _) = key.blind_evaluate(blinded).unwrap();
        let element_len = blinded.len() / inputs.len();
        for (blinded, evaluated) in blinded
            .chunks(element_len)
            .zip(evaluated.as_ref().chunks(element_len))
        {
            assert_eq!(group.mul(blinded).as_deref(), Some(evaluated));
        }
    }

    /// One suite's group, with the key's scalar.
    enum Group {
        Ristretto255(Edwards, BigUint),
        Nist(reference::Weierstrass, BigUint),
    }

    impl Group {
        fn new(index: usize, scalar: &[u8]) -> Self {
            match index {
                0 => Self::Ristretto255(reference::edwards25519(), BigUint::from_bytes_le(scalar)),
                1 => Self::Nist(reference::p256(), BigUint::from_bytes_be(scalar)),
                2 => Self::Nist(reference::p384(), BigUint::from_bytes_be(scalar)),
                _ => Self::Nist(reference::p521(), BigUint::from_bytes_be(scalar)),
            }
        }

        /// RFC 9497's `HashToGroup`, encoded as `SerializeElement` does.
        fn hash_to_group(&self, input: &[u8], dst: &[u8]) -> Vec<u8> {
            match self {
                // `expand_message_xmd` depends only on the hash, and
                // P-521's suite expands with SHA-512, as ristretto255's does.
                Self::Ristretto255(curve, _) => {
                    let uniform = reference::p521()
                        .expand_message_xmd(input, dst, 64)
                        .unwrap();
                    let point = curve.ristretto_from_uniform_bytes(&uniform.try_into().unwrap());
                    curve.ristretto_encode(&point).to_vec()
                }
                Self::Nist(curve, _) => compress(&curve.hash_to_curve(input, dst).unwrap()),
            }
        }

        /// The key's scalar times the encoded element, encoded, or `None`
        /// if the element does not decode or the product is the identity.
        fn mul(&self, element: &[u8]) -> Option<Vec<u8>> {
            match self {
                Self::Ristretto255(curve, k) => {
                    let point = curve.ristretto_decode(element.try_into().ok()?)?;
                    let product = curve.mul(k, &point);
                    (product != Edwards::identity())
                        .then(|| curve.ristretto_encode(&product).to_vec())
                }
                Self::Nist(curve, k) => {
                    let point = curve.mul(k, &Some(curve.decode(element)?));
                    point.is_some().then(|| compress(&curve.encode(&point)))
                }
            }
        }
    }

    /// SEC 1's compressed form of an uncompressed point.
    fn compress(point: &[u8]) -> Vec<u8> {
        let len = (point.len() - 1) / 2;
        [&[2 | (point[2 * len] & 1)][..], &point[1..=len]].concat()
    }
}
