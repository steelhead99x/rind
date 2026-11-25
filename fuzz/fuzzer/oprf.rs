#![no_main]

//! Both RFC 9497 modes, the OPRF and the VOPRF, under a key the fuzzer
//! writes, as a scalar or as `DeriveKeyPair`'s seed and info, with the
//! blinded elements, evaluated elements, and proof tampered with in flight,
//! over every suite.
//!
//! No reference implements RFC 9497 on aws-lc, so this checks rind against
//! itself and the `voprf` crate: both load or refuse the same keys, the
//! crate evaluates rind's blinded elements and each input as rind does under
//! the same key, and rind evaluates the crate's clients' blinded elements to
//! what they finalize to the direct outputs. An untampered exchange
//! finalizes to the server's direct evaluation of each input. A tampered
//! element is refused exactly when the crate cannot decode it, and a
//! tampered exchange is refused, or, in the OPRF mode, which cannot tell,
//! finalizes to another output, rather than panicking or finalizing to the
//! right one.
//!
//! On armv7 and the portable backend, `voprf` runs rind's own group
//! arithmetic, fiat-crypto's for the NIST suites and `curve25519-dalek` for
//! ristretto255, so there the textbook reference also hashes each input to
//! the group and multiplies by the key, and the crate checks only the
//! protocol above.

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rand_core_voprf::OsRng;
use rind::Error;
use rind::oprf::{self, P256_SHA256, P384_SHA384, P521_SHA512, RISTRETTO255_SHA512, Suite, voprf};

mod edit;
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
mod oracle;

const SUITES: [&Suite; 4] = [
    &RISTRETTO255_SHA512,
    &P256_SHA256,
    &P384_SHA384,
    &P521_SHA512,
];

/// The server's key, as both sides load it.
#[derive(Arbitrary, Debug)]
enum Key {
    /// `SerializeScalar`'s encoding, which reaches the edge scalars.
    Scalar(Vec<u8>),
    /// `DeriveKeyPair`'s inputs.
    Seed { seed: Vec<u8>, info: Vec<u8> },
}

#[derive(Arbitrary, Debug)]
struct Input {
    suite: u8,
    verifiable: bool,
    key: Key,
    inputs: Vec<Vec<u8>>,
    blinded: edit::Edit,
    evaluated: edit::Edit,
    proof: edit::Edit,
}

fuzz_target!(|input: Input| {
    let index = usize::from(input.suite % 4);
    let suite = SUITES[index];
    let inputs = &input.inputs[..input.inputs.len().min(8)];
    // RFC 9497 5.1 refuses inputs of `2^16 - 1` bytes or more.
    if let Some(long) = inputs.iter().find(|i| i.len() >= usize::from(u16::MAX)) {
        assert_eq!(
            oprf::Blind::new(suite, long).unwrap_err(),
            Error::WrongLength
        );
        assert_eq!(
            voprf::Blind::new(suite, long).unwrap_err(),
            Error::WrongLength
        );
        // A fixed key, so the check holds whether or not the fuzzed one loads.
        let (seed, info) = ([0x42; 32], b"fuzz");
        let key = oprf::ServerKey::derive(suite, &seed, info).unwrap();
        assert_eq!(key.evaluate(long).unwrap_err(), Error::WrongLength);
        let key = voprf::ServerKey::derive(suite, &seed, info).unwrap();
        assert_eq!(key.evaluate(long).unwrap_err(), Error::WrongLength);
        return;
    }
    match (index, input.verifiable) {
        (0, false) => run_oprf!(::voprf::Ristretto255, index, &input, inputs),
        (1, false) => run_oprf!(p256_voprf::NistP256, index, &input, inputs),
        (2, false) => run_oprf!(p384_voprf::NistP384, index, &input, inputs),
        (_, false) => run_oprf!(p521_voprf::NistP521, index, &input, inputs),
        (0, true) => run_voprf!(::voprf::Ristretto255, index, &input, inputs),
        (1, true) => run_voprf!(p256_voprf::NistP256, index, &input, inputs),
        (2, true) => run_voprf!(p384_voprf::NistP384, index, &input, inputs),
        (_, true) => run_voprf!(p521_voprf::NistP521, index, &input, inputs),
    }
});

/// Each suite's `SerializeScalar` length, in `SUITES`' order.
const SCALAR_LENS: [usize; 4] = [32, 32, 48, 66];

/// Loads the key on both sides with `$ours::from_scalar` or `derive` and
/// `$theirs::new_with_key` or `new_from_seed`, which take and refuse the
/// same within rind's documented bounds, or returns from the target.
macro_rules! load {
    ($ours:ty, $theirs:ty, $index:expr, $key:expr) => {{
        let suite = SUITES[$index];
        let (ours, theirs) = match $key {
            Key::Scalar(scalar) => {
                let ours = <$ours>::from_scalar(suite, scalar);
                // The crate's NIST suites zero-pad a scalar of 24 bytes or
                // more; rind takes only `SerializeScalar`'s length.
                if scalar.len() != SCALAR_LENS[$index] {
                    assert!(ours.is_err());
                    return;
                }
                (ours, <$theirs>::new_with_key(scalar))
            }
            Key::Seed { seed, info } => {
                let ours = <$ours>::derive(suite, seed, info);
                // rind refuses an `info` of `2^16 - 1` bytes, which the
                // crate takes, as it does such an input.
                if info.len() >= usize::from(u16::MAX) {
                    assert_eq!(ours.err(), Some(Error::WrongLength));
                    return;
                }
                (ours, <$theirs>::new_from_seed(seed, info))
            }
        };
        assert_eq!(
            ours.is_ok(),
            theirs.is_ok(),
            "{:?} {:?}",
            ours.as_ref().err(),
            theirs.as_ref().err()
        );
        let (Ok(ours), Ok(theirs)) = (ours, theirs) else {
            return;
        };
        (ours, theirs)
    }};
}
use load;

/// The OPRF mode in suite `$cs`, one input at a time.
macro_rules! run_oprf {
    ($cs:ty, $index:expr, $input:expr, $inputs:expr) => {{
        use ::voprf::{BlindedElement, EvaluationElement, OprfClient, OprfServer};
        let (index, input, inputs): (usize, &Input, &[Vec<u8>]) = ($index, $input, $inputs);
        let suite = SUITES[index];
        let (key, theirs) = load!(oprf::ServerKey, OprfServer<$cs>, index, &input.key);

        let mut outputs = Vec::new();
        let mut pairs = Vec::new();
        for message in inputs {
            let direct = key.evaluate(message).unwrap();
            assert_eq!(direct.as_ref(), &theirs.evaluate(message).unwrap()[..]);

            // Their client, our server.
            let result = OprfClient::<$cs>::blind(message, &mut OsRng).unwrap();
            let evaluated = key.blind_evaluate(&result.message.serialize()).unwrap();
            let evaluated = EvaluationElement::<$cs>::deserialize(evaluated.as_ref()).unwrap();
            let output = result.state.finalize(message, &evaluated).unwrap();
            assert_eq!(&output[..], direct.as_ref());

            // Our client, their server and ours.
            let (blind, blinded) = oprf::Blind::new(suite, message).unwrap();
            let mut blinded = blinded.as_ref().to_vec();
            let evaluated = key.blind_evaluate(&blinded).unwrap();
            let element = BlindedElement::<$cs>::deserialize(&blinded).unwrap();
            assert_eq!(
                evaluated.as_ref(),
                &theirs.blind_evaluate(&element).serialize()[..]
            );
            let right = evaluated.as_ref().to_vec();
            pairs.push((blinded.clone(), right.clone()));
            outputs.push(direct);
            let direct = outputs.last().unwrap();

            // rind takes exactly the elements the crate decodes: on the
            // curve, canonical, and not the identity. The crate ignores
            // bytes past an element, so the length is checked here.
            let decodes = |bytes: &[u8]| {
                bytes.len() == right.len() && BlindedElement::<$cs>::deserialize(bytes).is_ok()
            };
            input.blinded.apply(&mut blinded);
            let evaluated = key.blind_evaluate(&blinded);
            assert_eq!(
                evaluated.is_ok(),
                decodes(&blinded),
                "{:?}",
                evaluated.as_ref().err()
            );
            let Ok(evaluated) = evaluated else {
                continue;
            };
            let mut evaluated = evaluated.as_ref().to_vec();
            input.evaluated.apply(&mut evaluated);
            // The OPRF mode cannot tell a wrong element from a right one,
            // but another element is another output. Edits can cancel, as
            // negating the blinded element and then the evaluated one does,
            // so the expectation reads the element finalized.
            match blind.finalize(&evaluated) {
                Ok(output) => {
                    assert!(decodes(&evaluated));
                    assert_eq!(output.as_ref() == direct.as_ref(), evaluated == right);
                }
                Err(e) => {
                    assert!(matches!(e, Error::KeyRejected(_)), "{e:?}");
                    assert!(!decodes(&evaluated));
                }
            }
        }
        #[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
        reference::check(
            index,
            0,
            key.to_scalar().as_ref(),
            &inputs
                .iter()
                .zip(&outputs)
                .map(|(i, o)| (&i[..], o.as_ref()))
                .collect::<Vec<_>>(),
            &pairs
                .iter()
                .map(|(b, e)| (&b[..], &e[..]))
                .collect::<Vec<_>>(),
        );
        let _ = (outputs, pairs);
    }};
}
use run_oprf;

/// The VOPRF mode in suite `$cs`, the inputs in one batch.
macro_rules! run_voprf {
    ($cs:ty, $index:expr, $input:expr, $inputs:expr) => {{
        use ::voprf::{BlindedElement, EvaluationElement, Group, Proof, VoprfClient, VoprfServer};
        type G = <$cs as ::voprf::CipherSuite>::Group;
        let (index, input, inputs): (usize, &Input, &[Vec<u8>]) = ($index, $input, $inputs);
        let suite = SUITES[index];
        let (key, theirs) = load!(voprf::ServerKey, VoprfServer<$cs>, index, &input.key);
        assert_eq!(
            key.public_key().as_ref(),
            &G::serialize_elem(theirs.get_public_key())[..]
        );

        let direct: Vec<_> = inputs
            .iter()
            .map(|message| key.evaluate(message).unwrap())
            .collect();
        for (message, direct) in inputs.iter().zip(&direct) {
            assert_eq!(direct.as_ref(), &theirs.evaluate(message).unwrap()[..]);
        }

        let mut blinds = Vec::new();
        let mut blinded = Vec::new();
        for message in inputs {
            let (blind, element) = voprf::Blind::new(suite, message).unwrap();
            blinds.push(blind);
            blinded.extend_from_slice(element.as_ref());
        }

        // A public key is one element, encoded.
        let element_len = key.public_key().as_ref().len();
        if !inputs.is_empty() {
            // Their server evaluates our blinded elements as ours does.
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
            let (ours, _) = key.blind_evaluate(&blinded).unwrap();
            assert_eq!(ours.as_ref(), evaluated);
            #[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
            reference::check(
                index,
                1,
                key.to_scalar().as_ref(),
                &inputs
                    .iter()
                    .zip(&direct)
                    .map(|(i, o)| (&i[..], o.as_ref()))
                    .collect::<Vec<_>>(),
                &blinded
                    .chunks(element_len)
                    .zip(ours.as_ref().chunks(element_len))
                    .collect::<Vec<_>>(),
            );

            // Their clients finalize our evaluation and proof.
            let mut clients = Vec::new();
            let mut theirs_blinded = Vec::new();
            for message in inputs {
                let result = VoprfClient::<$cs>::blind(message, &mut OsRng).unwrap();
                clients.push(result.state);
                theirs_blinded.extend_from_slice(&result.message.serialize());
            }
            let (evaluated, proof) = key.blind_evaluate(&theirs_blinded).unwrap();
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
            .unwrap()
            .collect::<Vec<_>>();
            assert_eq!(outputs.len(), direct.len());
            for (output, direct) in outputs.into_iter().zip(&direct) {
                assert_eq!(&output.unwrap()[..], direct.as_ref());
            }
        }

        let mut changed = input.blinded.apply(&mut blinded);
        // rind takes a batch of one or more elements the crate decodes;
        // edits only shrink it, so it stays within rind's batch limit.
        let decodes = !blinded.is_empty()
            && blinded.len().is_multiple_of(element_len)
            && blinded
                .chunks(element_len)
                .all(|element| BlindedElement::<$cs>::deserialize(element).is_ok());
        let evaluated = key.blind_evaluate(&blinded);
        assert_eq!(evaluated.is_ok(), decodes, "{:?}", evaluated.as_ref().err());
        let Ok((evaluated, proof)) = evaluated else {
            return;
        };
        let mut evaluated = evaluated.as_ref().to_vec();
        changed |= input.evaluated.apply(&mut evaluated);
        let mut proof = proof.as_ref().to_vec();
        changed |= input.proof.apply(&mut proof);

        match voprf::Blind::finalize_batch(blinds, &evaluated, &proof, key.public_key()) {
            Ok(outputs) => {
                assert!(!changed);
                assert_eq!(outputs.len(), direct.len());
                for (output, direct) in outputs.iter().zip(&direct) {
                    assert_eq!(output.as_ref(), direct.as_ref());
                }
            }
            Err(_) => assert!(changed),
        }
    }};
}
use run_voprf;

/// The textbook reference's group operations, which share no code with the
/// arithmetic rind and `voprf` run on armv7 and the portable backend.
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
mod reference {
    use num_bigint::BigUint;
    use sha2::Digest;

    use super::oracle::reference::{self, Edwards};

    /// Each suite's RFC 9497 identifier, in `SUITES`' order.
    const IDENTIFIERS: [&[u8]; 4] = [
        b"ristretto255-SHA512",
        b"P256-SHA256",
        b"P384-SHA384",
        b"P521-SHA512",
    ];

    /// Each direct output is `Finalize` over the key times the input hashed
    /// to the group in `mode`, 0 for the OPRF and 1 for the VOPRF, and each
    /// evaluated element is the key times its blinded element.
    pub fn check(
        index: usize,
        mode: u8,
        scalar: &[u8],
        direct: &[(&[u8], &[u8])],
        evaluated: &[(&[u8], &[u8])],
    ) {
        let dst = [
            b"HashToGroup-OPRFV1-",
            &[mode][..],
            b"-",
            IDENTIFIERS[index],
        ]
        .concat();
        let group = Group::new(index, scalar);
        for &(input, output) in direct {
            let element = group.mul(&group.hash_to_group(input, &dst)).unwrap();
            let finalize = [
                &(input.len() as u16).to_be_bytes()[..],
                input,
                &(element.len() as u16).to_be_bytes(),
                &element,
                b"Finalize",
            ]
            .concat();
            let expected = match index {
                0 | 3 => sha2::Sha512::digest(&finalize).to_vec(),
                1 => sha2::Sha256::digest(&finalize).to_vec(),
                _ => sha2::Sha384::digest(&finalize).to_vec(),
            };
            assert_eq!(output, expected);
        }
        for &(blinded, evaluated) in evaluated {
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
