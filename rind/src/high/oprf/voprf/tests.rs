// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use serde_json::Value;

use super::super::evaluate;
use super::super::tests::{Run, derived, field, h, run, scalar, str_field, suite_of, suites};
use super::super::{
    BlindInner as OprfBlindInner, P256_SHA256, P384_SHA384, P521_SHA512, RISTRETTO255_SHA512,
};
use super::*;
use crate::error::KeyFormatError;

const SUITES: [&Suite; 4] = [
    &RISTRETTO255_SHA512,
    &P256_SHA256,
    &P384_SHA384,
    &P521_SHA512,
];

/// RFC 9497 A's VOPRF vectors, single and batched, step by step with their
/// blinds and proof nonces, then through the public API.
#[test]
fn rfc9497_voprf_vectors() {
    struct Steps;
    impl Run for Steps {
        fn run<G: Group>(self, suite: &Value)
        where
            KeyInner: From<Key<G>>,
            OprfBlindInner: From<ClientState<G>>,
            BlindInner: From<VerifiableState<G>> + Pick<VerifiableState<G>>,
            PublicInner: From<Public<G>>,
        {
            let _entry = Entry::new_secret();
            let key = Key::<G> {
                k: derived::<G>(Mode::Voprf, suite),
            };
            let public = Public::<G>::of(&key.k);
            assert_eq!(public.bytes.as_ref(), str_field(suite, "pkSm"));
            let public_key = PublicKey(public.clone().into());

            for v in suite["vectors"].as_array().unwrap() {
                let inputs = field(v, "Input");
                let outputs = field(v, "Output");
                assert_eq!(v["Batch"].as_u64().unwrap() as usize, inputs.len());

                let mut blinds = Vec::new();
                let mut blinded = Vec::new();
                for (input, blind) in inputs.iter().zip(field(v, "Blind")) {
                    let (state, element) =
                        VerifiableState::<G>::new(input, scalar::<G>(&blind)).unwrap();
                    blinded.extend_from_slice(element.as_ref());
                    blinds.push(Blind(state.into()));
                }
                assert_eq!(blinded, field(v, "BlindedElement").concat());

                let r = scalar::<G>(&h(v["Proof"]["r"].as_str().unwrap()));
                let (evaluated, proof) = key.blind_evaluate_with(&public, &blinded, r).unwrap();
                assert_eq!(evaluated.as_ref(), field(v, "EvaluationElement").concat());
                assert_eq!(proof.as_ref(), h(v["Proof"]["proof"].as_str().unwrap()));

                let finalized =
                    Blind::finalize_batch(blinds, evaluated.as_ref(), proof.as_ref(), &public_key)
                        .unwrap();
                assert_eq!(finalized.len(), outputs.len());
                for ((output, expected), input) in finalized.iter().zip(&outputs).zip(&inputs) {
                    assert_eq!(ct::into_public(output.0.clone()).as_ref(), &expected[..]);
                    let direct = evaluate::<G>(Mode::Voprf, &key.k, input).unwrap();
                    assert_eq!(ct::into_public(direct.0.clone()).as_ref(), &expected[..]);
                }
            }

            let server = ServerKey::derive(
                G::suite(),
                &str_field(suite, "seed"),
                &str_field(suite, "keyInfo"),
            )
            .unwrap();
            assert_eq!(server.suite(), G::suite());
            assert_eq!(server.public_key().as_ref(), str_field(suite, "pkSm"));
            assert_eq!(
                ct::into_public(server.to_bytes().0.clone()).as_ref(),
                str_field(suite, "skSm")
            );
            let parsed = PublicKey::new(G::suite(), &str_field(suite, "pkSm")).unwrap();
            assert_eq!(parsed.suite(), G::suite());
            for v in suite["vectors"].as_array().unwrap() {
                let mut blinds = Vec::new();
                let mut blinded = Vec::new();
                for input in field(v, "Input") {
                    let (blind, element) = Blind::new(G::suite(), &input).unwrap();
                    assert_eq!(blind.suite(), G::suite());
                    blinds.push(blind);
                    blinded.extend_from_slice(element.as_ref());
                }
                let (evaluated, proof) = server.blind_evaluate(&blinded).unwrap();
                let finalized =
                    Blind::finalize_batch(blinds, evaluated.as_ref(), proof.as_ref(), &parsed)
                        .unwrap();
                for (output, expected) in finalized.iter().zip(field(v, "Output")) {
                    assert_eq!(ct::into_public(output.0.clone()).as_ref(), expected);
                }
            }
        }
    }
    for suite in suites(1) {
        run(&suite, Steps);
    }
}

/// The group order of each suite, in its scalars' byte order.
fn order(suite: &Suite) -> Vec<u8> {
    h(match suite.id {
        SuiteId::Ristretto255Sha512 => {
            "edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010"
        }
        SuiteId::P256Sha256 => "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        SuiteId::P384Sha384 => {
            "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973"
        }
        SuiteId::P521Sha512 => {
            "01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409"
        }
    })
}

/// Every single-bit change to a vector's proof, a proof truncated or
/// extended, one with a scalar at the group order or (for ristretto255) a
/// second encoding of one, one against another key, and one over swapped
/// elements are refused.
#[test]
fn refuses_altered_proofs() {
    struct Steps;
    impl Run for Steps {
        fn run<G: Group>(self, suite: &Value)
        where
            KeyInner: From<Key<G>>,
            OprfBlindInner: From<ClientState<G>>,
            BlindInner: From<VerifiableState<G>> + Pick<VerifiableState<G>>,
            PublicInner: From<Public<G>>,
        {
            let _entry = Entry::new_secret();
            let pk = str_field(suite, "pkSm");
            let element = decode::<G>(&pk).unwrap();
            let public = Public::<G> {
                element,
                bytes: encode::<G>(&element),
            };
            for v in suite["vectors"].as_array().unwrap() {
                let blinded_bytes = field(v, "BlindedElement").concat();
                let evaluated_bytes = field(v, "EvaluationElement").concat();
                let blinded = decode_batch::<G>(&blinded_bytes).unwrap();
                let evaluated = decode_batch::<G>(&evaluated_bytes).unwrap();
                let proof = h(v["Proof"]["proof"].as_str().unwrap());
                let check = |public: &Public<G>,
                             evaluated: &[G::Element],
                             evaluated_bytes: &[u8],
                             proof: &[u8]| {
                    verify::<G>(
                        public,
                        &blinded,
                        &blinded_bytes,
                        evaluated,
                        evaluated_bytes,
                        proof,
                    )
                };
                check(&public, &evaluated, &evaluated_bytes, &proof).unwrap();

                for bit in 0..proof.len() * 8 {
                    let mut altered = proof.clone();
                    altered[bit / 8] ^= 1 << (bit % 8);
                    assert_eq!(
                        check(&public, &evaluated, &evaluated_bytes, &altered).unwrap_err(),
                        Error::BadSignature,
                        "bit {bit}"
                    );
                }
                for bad in [&proof[1..], &[&proof[..], &[0]].concat()] {
                    assert_eq!(
                        check(&public, &evaluated, &evaluated_bytes, bad).unwrap_err(),
                        Error::BadSignature
                    );
                }

                let order = order(G::suite());
                let mut at_order = proof.clone();
                at_order[G::SCALAR_LEN..].copy_from_slice(&order);
                assert_eq!(
                    check(&public, &evaluated, &evaluated_bytes, &at_order).unwrap_err(),
                    Error::BadSignature
                );
                if G::suite() == &RISTRETTO255_SHA512 {
                    // `c + L` is the same scalar as `c`, but not canonical.
                    let mut unreduced = proof.clone();
                    let mut carry = 0u16;
                    for (c, l) in unreduced[..32].iter_mut().zip(&order) {
                        let sum = u16::from(*c) + u16::from(*l) + carry;
                        *c = sum as u8;
                        carry = sum >> 8;
                    }
                    assert_eq!(carry, 0);
                    assert_eq!(
                        check(&public, &evaluated, &evaluated_bytes, &unreduced).unwrap_err(),
                        Error::BadSignature
                    );
                }

                let other = Public::<G>::of(&G::random_scalar().unwrap());
                assert_eq!(
                    check(&other, &evaluated, &evaluated_bytes, &proof).unwrap_err(),
                    Error::BadSignature
                );

                if evaluated.len() > 1 {
                    let mut swapped = evaluated.clone();
                    swapped.swap(0, 1);
                    let (first, rest) = evaluated_bytes.split_at(G::ELEMENT_LEN);
                    let (second, rest) = rest.split_at(G::ELEMENT_LEN);
                    let swapped_bytes = [second, first, rest].concat();
                    assert_eq!(
                        check(&public, &swapped, &swapped_bytes, &proof).unwrap_err(),
                        Error::BadSignature
                    );
                }
            }
        }
    }
    for suite in suites(1) {
        run(&suite, Steps);
    }
}

/// A batch of `n` blinds and their blinded elements, concatenated.
fn blind_batch(suite: &'static Suite, n: usize) -> (Vec<Blind>, Vec<u8>) {
    let mut blinds = Vec::new();
    let mut blinded = Vec::new();
    for i in 0..n {
        let (blind, element) = Blind::new(suite, format!("input {i}").as_bytes()).unwrap();
        blinds.push(blind);
        blinded.extend_from_slice(element.as_ref());
    }
    (blinds, blinded)
}

/// A random batch round-trips through the server for every suite, and
/// matches the server's direct evaluation.
#[test]
fn round_trips() {
    for suite in SUITES {
        let server = ServerKey::generate(suite).unwrap();
        let public_key = PublicKey::new(suite, server.public_key().as_ref()).unwrap();
        let (blinds, blinded) = blind_batch(suite, 3);
        let (evaluated, proof) = server.blind_evaluate(&blinded).unwrap();
        let outputs =
            Blind::finalize_batch(blinds, evaluated.as_ref(), proof.as_ref(), &public_key).unwrap();
        for (i, output) in outputs.iter().enumerate() {
            let direct = server.evaluate(format!("input {i}").as_bytes()).unwrap();
            assert_eq!(
                ct::into_public(output.0.clone()).as_ref(),
                ct::into_public(direct.0.clone()).as_ref()
            );
        }

        let (blind, blinded) = Blind::new(suite, b"single").unwrap();
        let (evaluated, proof) = server.blind_evaluate(blinded.as_ref()).unwrap();
        let output = blind
            .finalize(evaluated.as_ref(), proof.as_ref(), &public_key)
            .unwrap();
        let direct = server.evaluate(b"single").unwrap();
        assert_eq!(
            ct::into_public(output.0.clone()).as_ref(),
            ct::into_public(direct.0.clone()).as_ref()
        );
        assert!(format!("{server:?}").starts_with("ServerKey"));
    }
}

/// Batches that are empty, ragged, too long, or of a different length than
/// the client's blinds are refused, as are blinds of another suite.
#[test]
fn refuses_bad_batches() {
    for suite in SUITES {
        let server = ServerKey::generate(suite).unwrap();
        let (blinds, blinded) = blind_batch(suite, 2);
        assert_eq!(server.blind_evaluate(&[]).unwrap_err(), Error::WrongLength);
        assert_eq!(
            server.blind_evaluate(&blinded[1..]).unwrap_err(),
            Error::WrongLength
        );
        let (evaluated, proof) = server.blind_evaluate(&blinded).unwrap();
        let half = evaluated.as_ref().len() / 2;
        assert_eq!(
            Blind::finalize_batch(
                blinds,
                &evaluated.as_ref()[..half],
                proof.as_ref(),
                server.public_key()
            )
            .unwrap_err(),
            Error::WrongLength
        );

        let (blinds, _) = blind_batch(suite, 1);
        assert_eq!(
            Blind::finalize_batch(blinds, &[], proof.as_ref(), server.public_key()).unwrap_err(),
            Error::WrongLength
        );
        assert_eq!(
            Blind::finalize_batch(Vec::new(), &[], proof.as_ref(), server.public_key())
                .unwrap_err(),
            Error::WrongLength
        );

        let other = match suite == &P256_SHA256 {
            true => &P384_SHA384,
            false => &P256_SHA256,
        };
        let (blinds, _) = blind_batch(other, 1);
        assert_eq!(
            Blind::finalize_batch(
                blinds,
                &evaluated.as_ref()[..half],
                proof.as_ref(),
                server.public_key()
            )
            .unwrap_err(),
            Error::Unsupported
        );
    }

    // One more than the largest batch is refused.
    let suite = &RISTRETTO255_SHA512;
    let server = ServerKey::generate(suite).unwrap();
    let (_, blinded) = Blind::new(suite, b"input").unwrap();
    let too_many = blinded.as_ref().repeat(MAX_BATCH + 1);
    assert_eq!(
        server.blind_evaluate(&too_many).unwrap_err(),
        Error::WrongLength
    );
}

/// The largest batch, 65536 elements, evaluates and proves.
#[test]
#[cfg_attr(miri, ignore = "slow")]
fn largest_batch() {
    let suite = &RISTRETTO255_SHA512;
    let server = ServerKey::generate(suite).unwrap();
    let (_, blinded) = Blind::new(suite, b"input").unwrap();
    let batch = blinded.as_ref().repeat(MAX_BATCH);
    let (evaluated, proof) = server.blind_evaluate(&batch).unwrap();
    assert_eq!(evaluated.as_ref().len(), batch.len());
    assert_eq!(proof.as_ref().len(), 64);
}

/// Public keys of the wrong length, off the curve, or the identity are
/// refused.
#[test]
fn refuses_bad_public_keys() {
    for suite in SUITES {
        let server = ServerKey::generate(suite).unwrap();
        let good = server.public_key().as_ref();
        let zero = vec![0u8; good.len()];
        let mut off_curve = good.to_vec();
        // A negative ristretto255 encoding, or an X9.62 tag no point has.
        off_curve[0] ^= if suite == &RISTRETTO255_SHA512 {
            1
        } else {
            0x80
        };
        let cases: [(&[u8], KeyFormatError); 4] = [
            // Zeros encode ristretto255's identity, and no NIST point.
            (
                &zero,
                match suite == &RISTRETTO255_SHA512 {
                    true => KeyFormatError::SmallOrder,
                    false => KeyFormatError::NotOnCurve,
                },
            ),
            (&off_curve, KeyFormatError::NotOnCurve),
            (&good[1..], KeyFormatError::WrongLength),
            (&[good, &[0]].concat(), KeyFormatError::WrongLength),
        ];
        for (bad, error) in cases {
            assert_eq!(PublicKey::new(suite, bad).unwrap_err(), Error::from(error));
        }
        let parsed = PublicKey::new(suite, good).unwrap();
        assert_eq!(parsed.as_ref(), good);
        assert!(format!("{parsed:?}").starts_with("PublicKey"));
        let loaded = ServerKey::from_bytes(suite, server.to_bytes().as_ref()).unwrap();
        assert_eq!(loaded.public_key().as_ref(), good);
    }
}

/// The modes are separated: one key's outputs differ between them.
#[test]
fn modes_differ() {
    for suite in SUITES {
        let oprf = super::super::ServerKey::generate(suite).unwrap();
        let voprf = ServerKey::from_bytes(suite, oprf.to_bytes().as_ref()).unwrap();
        assert_ne!(
            ct::into_public(oprf.evaluate(b"x").unwrap().0.clone()).as_ref(),
            ct::into_public(voprf.evaluate(b"x").unwrap().0.clone()).as_ref()
        );
    }
}

/// Blinding, evaluation with its proof, and finalization take no branch or
/// memory index on the inputs, the blinds, or the server's key.
#[test]
fn stays_secret() {
    for suite in suites(1) {
        let s = suite_of(suite["identifier"].as_str().unwrap());
        let seed = str_field(&suite, "seed");
        ct::secret_slice(&seed);
        let server = ServerKey::derive(s, &seed, &str_field(&suite, "keyInfo")).unwrap();
        for v in suite["vectors"].as_array().unwrap() {
            let mut blinds = Vec::new();
            let mut blinded = Vec::new();
            for input in field(v, "Input") {
                ct::secret_slice(&input);
                let (blind, element) = Blind::new(s, &input).unwrap();
                blinds.push(blind);
                blinded.extend_from_slice(element.as_ref());
            }
            let (evaluated, proof) = server.blind_evaluate(&blinded).unwrap();
            let outputs = Blind::finalize_batch(
                blinds,
                evaluated.as_ref(),
                proof.as_ref(),
                server.public_key(),
            )
            .unwrap();
            for (output, expected) in outputs.iter().zip(field(v, "Output")) {
                assert_eq!(ct::into_public(output.0.clone()).as_ref(), expected);
            }
        }
    }
}
