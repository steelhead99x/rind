// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use serde_json::Value;

use super::*;

// Keep the real group's arithmetic and real point conversion. Only the
// hash output is forced to an opposite-point sum: finding such a message
// would require a hash preimage, which is unsuitable for a regression test.
nist_group!(
    IdentityP256,
    p256,
    Sha256Context,
    b"P256-SHA256",
    P256_SHA256,
    p256::hash_to_curve::hash_to_infinity
);
nist_group!(
    IdentityP384,
    p384,
    Sha384Context,
    b"P384-SHA384",
    P384_SHA384,
    p384::hash_to_curve::hash_to_infinity
);
nist_group!(
    IdentityP521,
    p521,
    Sha512Context,
    b"P521-SHA512",
    P521_SHA512,
    p521::hash_to_curve::hash_to_infinity
);

fn refuses_identity_hash<G: Group>() {
    let _entry = Entry::new_secret();
    let input = ct::into_secret(*b"identity");
    let mut key = vec![0; G::SCALAR_LEN];
    key[G::SCALAR_LEN - 1] = 2;
    ct::secret_slice(&key);
    for mode in [Mode::Oprf, Mode::Voprf] {
        assert_eq!(
            ClientState::<G>::blind(mode, &input, scalar::<G>(&key)).err(),
            Some(identity())
        );
        assert_eq!(
            evaluate::<G>(mode, &scalar::<G>(&key), &input).err(),
            Some(identity())
        );
    }
}

#[test]
fn p256_refuses_identity_hash_at_oprf_boundaries() {
    refuses_identity_hash::<IdentityP256>();
}

#[test]
fn p384_refuses_identity_hash_at_oprf_boundaries() {
    refuses_identity_hash::<IdentityP384>();
}

#[test]
fn p521_refuses_identity_hash_at_oprf_boundaries() {
    refuses_identity_hash::<IdentityP521>();
}

pub(super) fn h(hex: &str) -> Vec<u8> {
    hex::decode(hex).unwrap()
}

/// RFC 9497 Appendix A's vectors for `mode`: each suite's entry, with its
/// identifier.
pub(super) fn suites(mode: u64) -> Vec<Value> {
    let path = format!(
        "{}/../thirdparty/vectors/rfc9497/allVectors.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let all: Vec<Value> = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let suites: Vec<Value> = all.into_iter().filter(|s| s["mode"] == mode).collect();
    assert_eq!(suites.len(), 4);
    suites
}

/// A vector's field, hex, split at the commas a batch's values have.
pub(super) fn field(v: &Value, name: &str) -> Vec<Vec<u8>> {
    v[name].as_str().unwrap().split(',').map(h).collect()
}

pub(super) fn str_field(v: &Value, name: &str) -> Vec<u8> {
    h(v[name].as_str().unwrap())
}

pub(super) fn suite_of(identifier: &str) -> &'static Suite {
    match identifier {
        "ristretto255-SHA512" => &RISTRETTO255_SHA512,
        "P256-SHA256" => &P256_SHA256,
        "P384-SHA384" => &P384_SHA384,
        "P521-SHA512" => &P521_SHA512,
        _ => unreachable!("{identifier}"),
    }
}

/// The vector's suite's group, to run a step in.
pub(super) trait Run {
    fn run<G: Group>(self, suite: &Value)
    where
        KeyInner: From<Key<G>>,
        BlindInner: From<ClientState<G>>,
        voprf::BlindInner: From<voprf::VerifiableState<G>> + Pick<voprf::VerifiableState<G>>,
        voprf::PublicInner: From<voprf::Public<G>>;
}

pub(super) fn run(suite: &Value, step: impl Run) {
    let identifier = suite["identifier"].as_str().unwrap();
    with_group!(suite_of(identifier), G => {
        assert_eq!(G::NAME, identifier.as_bytes());
        step.run::<G>(suite)
    })
}

/// The suite's key, by `DeriveKeyPair` over its seed and info.
pub(super) fn derived<G: Group>(mode: Mode, suite: &Value) -> G::Scalar {
    let _entry = Entry::new_secret();
    let k = derive_scalar::<G>(
        mode,
        &str_field(suite, "seed"),
        &str_field(suite, "keyInfo"),
    )
    .unwrap();
    assert_eq!(
        ct::into_public(scalar_bytes::<G>(&k)).as_ref(),
        str_field(suite, "skSm")
    );
    k
}

pub(super) fn scalar<G: Group>(bytes: &[u8]) -> G::Scalar {
    G::scalar_from_bytes(bytes).unwrap()
}

/// RFC 9497 A's OPRF vectors, step by step with their blinds, then through
/// the public API from the derived key.
#[test]
fn rfc9497_oprf_vectors() {
    struct Steps;
    impl Run for Steps {
        fn run<G: Group>(self, suite: &Value)
        where
            KeyInner: From<Key<G>>,
            BlindInner: From<ClientState<G>>,
        {
            let _entry = Entry::new_secret();
            let k = derived::<G>(Mode::Oprf, suite);
            let key = Key::<G> { k };
            for v in suite["vectors"].as_array().unwrap() {
                let input = str_field(v, "Input");
                let blind = scalar::<G>(&str_field(v, "Blind"));
                let (state, _, blinded) =
                    ClientState::<G>::blind(Mode::Oprf, &input, blind).unwrap();
                assert_eq!(blinded.as_ref(), str_field(v, "BlindedElement"));
                let evaluated = encode::<G>(&key.mul(&decode::<G>(blinded.as_ref()).unwrap()));
                assert_eq!(
                    ct::into_public(evaluated.clone()).as_ref(),
                    str_field(v, "EvaluationElement")
                );
                let output = state.finalize(&decode::<G>(evaluated.as_ref()).unwrap());
                assert_eq!(
                    ct::into_public(output.0.clone()).as_ref(),
                    str_field(v, "Output")
                );

                let output = Blind(state.into())
                    .finalize(&str_field(v, "EvaluationElement"))
                    .unwrap();
                assert_eq!(
                    ct::into_public(output.0.clone()).as_ref(),
                    str_field(v, "Output")
                );
            }

            let suite_ref = G::suite();
            let server = ServerKey::derive(
                suite_ref,
                &str_field(suite, "seed"),
                &str_field(suite, "keyInfo"),
            )
            .unwrap();
            assert_eq!(server.suite(), suite_ref);
            assert_eq!(
                ct::into_public(server.to_bytes().0.clone()).as_ref(),
                str_field(suite, "skSm")
            );
            for v in suite["vectors"].as_array().unwrap() {
                let evaluated = server
                    .blind_evaluate(&str_field(v, "BlindedElement"))
                    .unwrap();
                assert_eq!(evaluated.as_ref(), str_field(v, "EvaluationElement"));
                let output = server.evaluate(&str_field(v, "Input")).unwrap();
                assert_eq!(
                    ct::into_public(output.0.clone()).as_ref(),
                    str_field(v, "Output")
                );
            }
        }
    }
    for suite in suites(0) {
        run(&suite, Steps);
    }
}

/// A random blind round-trips through the server for every suite, and
/// matches the server's direct evaluation.
#[test]
fn round_trips() {
    for suite in [
        &RISTRETTO255_SHA512,
        &P256_SHA256,
        &P384_SHA384,
        &P521_SHA512,
    ] {
        let server = ServerKey::generate(suite).unwrap();
        let loaded = ServerKey::from_bytes(suite, server.to_bytes().as_ref()).unwrap();
        for input in [&b""[..], b"input", &[0x5a; MAX_INPUT]] {
            let (blind, blinded) = Blind::new(suite, input).unwrap();
            assert_eq!(blind.suite(), suite);
            let evaluated = loaded.blind_evaluate(blinded.as_ref()).unwrap();
            let output = blind.finalize(evaluated.as_ref()).unwrap();
            let direct = server.evaluate(input).unwrap();
            assert_eq!(
                ct::into_public(output.0.clone()).as_ref(),
                ct::into_public(direct.0.clone()).as_ref()
            );
        }
        assert!(format!("{server:?}").starts_with("ServerKey"));
    }
}

/// RFC 9497 5.1's limit: inputs and key info of `2^16 - 1` bytes or more
/// are refused.
#[test]
fn refuses_long_inputs() {
    let long = vec![0u8; MAX_INPUT + 1];
    for suite in [
        &RISTRETTO255_SHA512,
        &P256_SHA256,
        &P384_SHA384,
        &P521_SHA512,
    ] {
        assert_eq!(Blind::new(suite, &long).unwrap_err(), Error::WrongLength);
        let server = ServerKey::generate(suite).unwrap();
        assert_eq!(server.evaluate(&long).unwrap_err(), Error::WrongLength);
        assert_eq!(
            ServerKey::derive(suite, &[0; 32], &long).unwrap_err(),
            Error::WrongLength
        );
        ServerKey::derive(suite, &[0; 32], &long[1..]).unwrap();
        assert_eq!(
            voprf::Blind::new(suite, &long).unwrap_err(),
            Error::WrongLength
        );
    }
}

/// Keys of the wrong length, zero, or not below the group order are
/// refused.
#[test]
fn refuses_bad_keys() {
    let orders = [
        (
            &RISTRETTO255_SHA512,
            "edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010",
        ),
        (
            &P256_SHA256,
            "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        ),
        (
            &P384_SHA384,
            "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
        ),
        (
            &P521_SHA512,
            "01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409",
        ),
    ];
    for (suite, order) in orders {
        let order = h(order);
        let zero = vec![0; order.len()];
        for bad in [&order[..], &zero, &order[1..], &[&order[..], &[0]].concat()] {
            assert!(matches!(
                ServerKey::from_bytes(suite, bad).unwrap_err(),
                Error::KeyRejected(_)
            ));
            assert!(matches!(
                voprf::ServerKey::from_bytes(suite, bad).unwrap_err(),
                Error::KeyRejected(_)
            ));
        }
        // The order less one is the largest key.
        let mut largest = order.clone();
        match suite.id {
            SuiteId::Ristretto255Sha512 => largest[0] -= 1,
            _ => *largest.last_mut().unwrap() -= 1,
        }
        ServerKey::from_bytes(suite, &largest).unwrap();
    }
}

/// Elements of the wrong length, off the curve, or the identity are refused
/// on both sides.
#[test]
fn refuses_bad_elements() {
    for suite in [
        &RISTRETTO255_SHA512,
        &P256_SHA256,
        &P384_SHA384,
        &P521_SHA512,
    ] {
        let server = ServerKey::generate(suite).unwrap();
        let (_, blinded) = Blind::new(suite, b"input").unwrap();
        let good = blinded.as_ref();
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
            assert_eq!(server.blind_evaluate(bad).unwrap_err(), Error::from(error));
            let (blind, _) = Blind::new(suite, b"input").unwrap();
            assert_eq!(blind.finalize(bad).unwrap_err(), Error::from(error));
        }
    }
}

/// An input hashing to the identity is refused; none is known, so this
/// checks the ristretto255 test for it with an element that is.
#[test]
fn identity_is_refused() {
    let _entry = Entry::new_secret();
    assert!(Ristretto255::element_from_bytes(&[0; 32]).is_none());
    let identity =
        ristretto255::Element::mul_base(&ristretto255::Scalar::from_uniform_bytes(&[0; 64]));
    assert_eq!(identity.to_bytes(), [0; 32]);
}

/// The suites' names and lengths are RFC 9497 section 4's.
#[test]
fn suites_match_rfc9497() {
    fn lengths<G: Group>() -> (usize, usize, usize) {
        (G::ELEMENT_LEN, G::SCALAR_LEN, G::Hash::OUTPUT)
    }
    assert_eq!(lengths::<Ristretto255>(), (32, 32, 64));
    assert_eq!(lengths::<P256>(), (33, 32, 32));
    assert_eq!(lengths::<P384>(), (49, 48, 48));
    assert_eq!(lengths::<P521>(), (67, 66, 64));
    assert_eq!(format!("{:?}", RISTRETTO255_SHA512), "ristretto255-SHA512");
    assert_ne!(RISTRETTO255_SHA512, P256_SHA256);
}

/// Blinding, evaluation, and finalization take no branch or memory index
/// on the input, the blind, or the server's key.
#[test]
fn stays_secret() {
    struct Steps;
    impl Run for Steps {
        fn run<G: Group>(self, suite: &Value)
        where
            KeyInner: From<Key<G>>,
            BlindInner: From<ClientState<G>>,
        {
            let seed = str_field(suite, "seed");
            ct::secret_slice(&seed);
            let server =
                ServerKey::derive(G::suite(), &seed, &str_field(suite, "keyInfo")).unwrap();
            for v in suite["vectors"].as_array().unwrap() {
                let input = str_field(v, "Input");
                ct::secret_slice(&input);
                let (blind, blinded) = Blind::new(G::suite(), &input).unwrap();
                let evaluated = server.blind_evaluate(blinded.as_ref()).unwrap();
                let output = blind.finalize(evaluated.as_ref()).unwrap();
                assert_eq!(
                    ct::into_public(output.0.clone()).as_ref(),
                    str_field(v, "Output")
                );
                let output = server.evaluate(&input).unwrap();
                assert_eq!(
                    ct::into_public(output.0.clone()).as_ref(),
                    str_field(v, "Output")
                );
            }
        }
    }
    for suite in suites(0) {
        run(&suite, Steps);
    }
}
