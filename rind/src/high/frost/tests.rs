// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use serde_json::Value;

use super::*;

fn h(hex: &str) -> Vec<u8> {
    hex::decode(hex).unwrap()
}

fn field(v: &Value, name: &str) -> Vec<u8> {
    h(v[name].as_str().unwrap())
}

/// RFC 9591 Appendix E's vectors for one suite, from the CFRG draft's `poc`.
fn vectors(name: &str) -> Value {
    let path = format!(
        "{}/../thirdparty/vectors/rfc9591/frost-{name}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
}

/// The share of the vector's participant `id`, out of `shares`.
fn share_of(shares: &[SigningShare], id: u64) -> &SigningShare {
    &shares[id as usize - 1]
}

/// Runs RFC 9591 Appendix E's vector for `G` through every step: dealing
/// with its polynomial, committing with its randomness, the binding
/// factors, the signature shares, and the signature.
fn check_vector<G: Group>(name: &str) {
    let _entry = Entry::new_secret();
    let v = vectors(name);
    let inputs = &v["inputs"];
    let max: u16 = v["config"]["MAX_PARTICIPANTS"]
        .as_str()
        .unwrap()
        .parse()
        .unwrap();

    let mut coefficients = vec![field(inputs, "group_secret_key")];
    for c in inputs["share_polynomial_coefficients"].as_array().unwrap() {
        coefficients.push(h(c.as_str().unwrap()));
    }
    let coefficients: Vec<G::Scalar> = coefficients
        .iter()
        .map(|c| G::scalar_from_bytes(c.as_slice().try_into().unwrap()).unwrap())
        .collect();
    let (shares, commitment) = deal_with::<G>(&coefficients, max);
    let public_key = commitment.public_key();
    assert_eq!(public_key.as_ref(), field(inputs, "group_public_key"));
    assert_eq!(usize::from(commitment.min_signers()), coefficients.len());

    for s in inputs["participant_shares"].as_array().unwrap() {
        let share = share_of(&shares, s["identifier"].as_u64().unwrap());
        let want = field(s, "participant_share");
        assert_eq!(ct::into_public(share.to_scalar().0), &want[..]);
        let loaded = SigningShare::from_scalar(share.identifier(), &want, &commitment).unwrap();
        assert_eq!(loaded.public_key(), public_key);
    }

    let mut nonces = Vec::new();
    let mut commitments = Vec::new();
    for o in v["round_one_outputs"]["outputs"].as_array().unwrap() {
        let share = share_of(&shares, o["identifier"].as_u64().unwrap());
        let random = [
            field(o, "hiding_nonce_randomness").try_into().unwrap(),
            field(o, "binding_nonce_randomness").try_into().unwrap(),
        ];
        let n = SigningNonces::commit_with::<G>(share, &random)
            .unwrap()
            .unwrap();
        assert_eq!(ct::into_public(n.hiding), &field(o, "hiding_nonce")[..]);
        assert_eq!(ct::into_public(n.binding), &field(o, "binding_nonce")[..]);
        let want = [
            share.identifier().as_ref().to_vec(),
            field(o, "hiding_nonce_commitment"),
            field(o, "binding_nonce_commitment"),
        ]
        .concat();
        assert_eq!(n.commitments.as_ref(), want);
        commitments.push(Commitments::new(G::suite(), &want).unwrap());
        nonces.push((share, n));
    }

    let message = field(inputs, "message");
    // Reversed, as the package sorts them.
    commitments.reverse();
    let package = SigningPackage::new(public_key, &commitments, &message).unwrap();
    for (i, o) in v["round_one_outputs"]["outputs"]
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
    {
        assert_eq!(package.binding_factors[i], &field(o, "binding_factor")[..]);
    }

    let mut signature_shares = Vec::new();
    for ((share, n), o) in nonces
        .into_iter()
        .zip(v["round_two_outputs"]["outputs"].as_array().unwrap())
    {
        let signature_share = n.sign(share, &package).unwrap();
        assert_eq!(
            &signature_share.as_ref()[SCALAR_LEN..],
            field(o, "sig_share")
        );
        package.verify_share(&signature_share, &commitment).unwrap();
        signature_shares.push(signature_share);
    }

    let signature = package.aggregate(&signature_shares).unwrap();
    assert_eq!(signature.as_ref(), field(&v["final_output"], "sig"));
    public_key.verify(&message, signature.as_ref()).unwrap();
}

#[test]
fn rfc9591_ed25519() {
    check_vector::<Ed25519>("ed25519-sha512");
}

#[test]
fn rfc9591_ristretto255() {
    check_vector::<Ristretto255>("ristretto255-sha512");
}

#[test]
fn rfc9591_p256() {
    check_vector::<P256>("p256-sha256");
}

const SUITES: [&Suite; 3] = [&ED25519_SHA512, &RISTRETTO255_SHA512, &P256_SHA256];

/// Signs `message` with the shares at `signers`, through the public API.
fn sign(
    shares: &[SigningShare],
    signers: &[usize],
    message: &[u8],
) -> (SigningPackage, Vec<SignatureShare>) {
    let (nonces, commitments): (Vec<_>, Vec<_>) = signers
        .iter()
        .map(|&i| SigningNonces::commit(&shares[i]).unwrap())
        .unzip();
    let package = SigningPackage::new(shares[0].public_key(), &commitments, message).unwrap();
    let signature_shares = nonces
        .into_iter()
        .zip(signers)
        .map(|(n, &i)| n.sign(&shares[i], &package).unwrap())
        .collect();
    (package, signature_shares)
}

/// Every threshold of every group signs, and only a threshold does.
#[test]
fn any_threshold_signs() {
    for suite in SUITES {
        for (min, max) in [(2, 2), (2, 3), (3, 5), (5, 5)] {
            let (shares, commitment) = deal(suite, min, max).unwrap();
            assert_eq!(shares.len(), usize::from(max));
            assert_eq!(commitment.min_signers(), min);
            assert_eq!(
                VssCommitment::new(suite, commitment.as_ref()).unwrap(),
                commitment
            );
            let public_key = commitment.public_key();
            for (n, share) in shares.iter().enumerate() {
                assert_eq!(
                    share.identifier(),
                    &Identifier::new(suite, share.identifier().as_ref()).unwrap()
                );
                let reloaded = SigningShare::from_scalar(
                    share.identifier(),
                    share.to_scalar().as_ref(),
                    &commitment,
                )
                .unwrap();
                assert_eq!(reloaded.public_key(), public_key);
                assert_eq!(reloaded.min_signers(), min);
                let _entry = Entry::new_public();
                with_group!(suite, G => assert_eq!(
                    share.identifier().as_ref(),
                    G::scalar_to_bytes(&scalar_from_u16::<G>(n as u16 + 1))
                ));
            }

            // The last `min` participants, and every participant.
            let last: Vec<usize> = (usize::from(max - min)..usize::from(max)).collect();
            let all: Vec<usize> = (0..usize::from(max)).collect();
            for signers in [last, all] {
                let (package, signature_shares) = sign(&shares, &signers, b"message");
                for share in &signature_shares {
                    package.verify_share(share, &commitment).unwrap();
                }
                let signature = package.aggregate(&signature_shares).unwrap();
                public_key.verify(b"message", signature.as_ref()).unwrap();
                assert_eq!(
                    public_key.verify(b"messagf", signature.as_ref()),
                    Err(Error::BadSignature)
                );
            }

            // One short of the threshold: each signer refuses.
            let few: Vec<usize> = (0..usize::from(min - 1)).collect();
            let (nonces, commitments): (Vec<_>, Vec<_>) = few
                .iter()
                .map(|&i| SigningNonces::commit(&shares[i]).unwrap())
                .unzip();
            let package = SigningPackage::new(public_key, &commitments, b"m").unwrap();
            for (n, &i) in nonces.into_iter().zip(&few) {
                assert_eq!(n.sign(&shares[i], &package).err(), Some(Error::WrongLength));
            }
        }
    }
}

/// A FROST(Ed25519, SHA-512) signature verifies as an Ed25519 signature,
/// through `rind::signature`.
#[test]
fn ed25519_signatures_are_ed25519() {
    use crate::high::signature::{PublicKey as SignaturePublicKey, verify};
    let (shares, commitment) = deal(&ED25519_SHA512, 2, 3).unwrap();
    let (package, signature_shares) = sign(&shares, &[0, 2], b"hello");
    let signature = package.aggregate(&signature_shares).unwrap();
    let key = SignaturePublicKey::new(&verify::ED25519, commitment.public_key().as_ref()).unwrap();
    key.verify(b"hello", signature.as_ref()).unwrap();
    assert!(key.verify(b"hellp", signature.as_ref()).is_err());
}

/// The coordinator's aggregation fails on one bad share, and verifying each
/// share names it.
#[test]
fn bad_shares_are_identified() {
    for suite in SUITES {
        let (shares, commitment) = deal(suite, 3, 4).unwrap();
        let (package, mut signature_shares) = sign(&shares, &[0, 1, 3], b"message");
        // Participant 2's share, with 1 added to its scalar.
        let _entry = Entry::new_public();
        let bad = &signature_shares[1];
        let z = with_group!(suite, G => {
            let z = add::<G>(&bad.z::<G>(), &scalar_from_u16::<G>(1));
            G::scalar_to_bytes(&z)
        });
        let mut bytes = bad.as_ref().to_vec();
        bytes[SCALAR_LEN..].copy_from_slice(&z);
        signature_shares[1] = SignatureShare::new(suite, &bytes).unwrap();

        assert_eq!(
            package.aggregate(&signature_shares).err(),
            Some(Error::BadSignature)
        );
        let culprits: Vec<_> = signature_shares
            .iter()
            .filter(|share| package.verify_share(share, &commitment).is_err())
            .map(SignatureShare::identifier)
            .collect();
        assert_eq!(culprits, [*shares[1].identifier()]);

        // A share another participant's verifying key does not match.
        let swapped = [
            &signature_shares[2].as_ref()[..SCALAR_LEN],
            &signature_shares[0].as_ref()[SCALAR_LEN..],
        ]
        .concat();
        let swapped = SignatureShare::new(suite, &swapped).unwrap();
        assert_eq!(
            package.verify_share(&swapped, &commitment),
            Err(Error::BadSignature)
        );
    }
}

fn rejected(reason: KeyFormatError) -> Option<Error> {
    Some(reason.into())
}

/// Misused values are refused, without signing.
#[test]
fn refuses_misuse() {
    let (shares, commitment) = deal(&RISTRETTO255_SHA512, 2, 3).unwrap();
    let (other_shares, other_commitment) = deal(&RISTRETTO255_SHA512, 2, 3).unwrap();
    let (p256_shares, p256_commitment) = deal(&P256_SHA256, 2, 3).unwrap();
    let public_key = commitment.public_key();

    let (n0, c0) = SigningNonces::commit(&shares[0]).unwrap();
    let (n1, c1) = SigningNonces::commit(&shares[1]).unwrap();
    let (_, c1_again) = SigningNonces::commit(&shares[1]).unwrap();
    let (_, p256_c) = SigningNonces::commit(&p256_shares[0]).unwrap();

    // The package.
    assert_eq!(
        SigningPackage::new(public_key, &[c0.clone(), c1.clone(), c1_again], b"m").err(),
        rejected(KeyFormatError::DuplicateIdentifier)
    );
    assert_eq!(
        SigningPackage::new(public_key, &[c0.clone(), p256_c], b"m").err(),
        Some(Error::Unsupported)
    );
    assert_eq!(
        SigningPackage::new(public_key, &[], b"m").err(),
        Some(Error::WrongLength)
    );

    // Signing.
    let package = SigningPackage::new(public_key, &[c0.clone(), c1.clone()], b"m").unwrap();
    let other_package = SigningPackage::new(
        other_commitment.public_key(),
        &[c0.clone(), c1.clone()],
        b"m",
    )
    .unwrap();
    let only_1 = SigningPackage::new(public_key, core::slice::from_ref(&c1), b"m").unwrap();
    let (n, _) = SigningNonces::commit(&shares[0]).unwrap();
    assert_eq!(
        n.sign(&shares[0], &other_package).err(),
        rejected(KeyFormatError::MismatchedPublicKey)
    );
    let (n, _) = SigningNonces::commit(&shares[0]).unwrap();
    assert_eq!(
        n.sign(&shares[1], &package).err(),
        rejected(KeyFormatError::MismatchedCommitments)
    );
    // Another group's participant with the same identifier, whose
    // commitments a package under this group's key carries.
    let (n, c) = SigningNonces::commit(&other_shares[0]).unwrap();
    let mixed = SigningPackage::new(public_key, &[c, c1.clone()], b"m").unwrap();
    assert_eq!(
        n.sign(&shares[0], &mixed).err(),
        rejected(KeyFormatError::MismatchedCommitments)
    );
    // Another polynomial with the same group key, whose share for the same
    // identifier has another secret.
    let scalar = |b: u8| Ristretto255::scalar_from_bytes(&[b; SCALAR_LEN]).unwrap();
    let (same_key, _) = deal_with::<Ristretto255>(&[scalar(1), scalar(2)], 2);
    let (same_key_other, _) = deal_with::<Ristretto255>(&[scalar(1), scalar(3)], 2);
    assert_eq!(same_key[0].public_key(), same_key_other[0].public_key());
    let (n, c) = SigningNonces::commit(&same_key_other[0]).unwrap();
    let (_, c2) = SigningNonces::commit(&same_key[1]).unwrap();
    let same_key_package = SigningPackage::new(same_key[0].public_key(), &[c, c2], b"m").unwrap();
    assert_eq!(
        n.sign(&same_key[0], &same_key_package).err(),
        rejected(KeyFormatError::MismatchedCommitments)
    );
    // Fresh nonces whose commitments are not the package's.
    let (n, _) = SigningNonces::commit(&shares[0]).unwrap();
    assert_eq!(
        n.sign(&shares[0], &package).err(),
        rejected(KeyFormatError::MismatchedCommitments)
    );
    let (n, _) = SigningNonces::commit(&shares[0]).unwrap();
    assert_eq!(n.sign(&shares[0], &only_1).err(), Some(Error::WrongLength));
    let three = SigningPackage::new(
        public_key,
        &[c1.clone(), SigningNonces::commit(&shares[2]).unwrap().1],
        b"m",
    )
    .unwrap();
    let (n, _) = SigningNonces::commit(&shares[0]).unwrap();
    assert_eq!(
        n.sign(&shares[0], &three).err(),
        rejected(KeyFormatError::UnknownIdentifier)
    );
    let (n, _) = SigningNonces::commit(&shares[0]).unwrap();
    assert_eq!(
        n.sign(&p256_shares[0], &package).err(),
        Some(Error::Unsupported)
    );

    // Aggregation.
    let s0 = n0.sign(&shares[0], &package).unwrap();
    let s1 = n1.sign(&shares[1], &package).unwrap();
    assert_eq!(
        package.aggregate(core::slice::from_ref(&s0)).err(),
        Some(Error::WrongLength)
    );
    assert_eq!(
        package.aggregate(&[s0.clone(), s0.clone()]).err(),
        rejected(KeyFormatError::UnknownIdentifier)
    );
    // In either order.
    let signature = package.aggregate(&[s1.clone(), s0.clone()]).unwrap();
    public_key.verify(b"m", signature.as_ref()).unwrap();
    assert_eq!(
        package.verify_share(&s0, &other_commitment).err(),
        rejected(KeyFormatError::MismatchedPublicKey)
    );
    assert_eq!(
        package.verify_share(&s0, &p256_commitment).err(),
        Some(Error::Unsupported)
    );
    assert_eq!(
        only_1.verify_share(&s0, &commitment).err(),
        rejected(KeyFormatError::UnknownIdentifier)
    );

    // Loading a share.
    let scalar = shares[0].to_scalar();
    assert_eq!(
        SigningShare::from_scalar(shares[0].identifier(), scalar.as_ref(), &other_commitment).err(),
        rejected(KeyFormatError::MismatchedPublicKey)
    );
    assert_eq!(
        SigningShare::from_scalar(shares[1].identifier(), scalar.as_ref(), &commitment).err(),
        rejected(KeyFormatError::MismatchedPublicKey)
    );
    assert_eq!(
        SigningShare::from_scalar(shares[0].identifier(), scalar.as_ref(), &p256_commitment).err(),
        Some(Error::Unsupported)
    );
    assert_eq!(
        SigningShare::from_scalar(shares[0].identifier(), &[0; 32], &commitment).err(),
        rejected(KeyFormatError::ScalarOutOfRange)
    );
    assert_eq!(
        SigningShare::from_scalar(shares[0].identifier(), &[0; 31], &commitment).err(),
        rejected(KeyFormatError::WrongLength)
    );

    // Dealing.
    for (min, max) in [(0, 3), (1, 3), (4, 3), (2, 1)] {
        assert_eq!(
            deal(&ED25519_SHA512, min, max).err(),
            Some(Error::WrongLength)
        );
    }
}

/// The group orders, `n`, most significant byte first.
const ED25519_ORDER: &str = "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed";
const P256_ORDER: &str = "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551";

/// The group order, as the suite encodes a scalar.
fn order(suite: &Suite) -> Vec<u8> {
    match suite.id {
        SuiteId::P256Sha256 => h(P256_ORDER),
        _ => h(ED25519_ORDER).into_iter().rev().collect(),
    }
}

/// Identifiers and scalars are refused at the group order, and identifiers
/// at zero; identifiers order as integers.
#[test]
fn identifiers_are_nonzero_scalars() {
    for suite in SUITES {
        let n = order(suite);
        let reason = |bytes: &[u8]| Identifier::new(suite, bytes).err();
        assert_eq!(reason(&n), rejected(KeyFormatError::ScalarOutOfRange));
        assert_eq!(reason(&[0; 32]), rejected(KeyFormatError::ScalarOutOfRange));
        assert_eq!(reason(&[1; 31]), rejected(KeyFormatError::WrongLength));
        assert_eq!(
            reason(&[0xff; 32]),
            rejected(KeyFormatError::ScalarOutOfRange)
        );

        let _entry = Entry::new_public();
        let [one, two_five_six] = with_group!(suite, G => [1, 256].map(Identifier::from_u16::<G>));
        assert!(one < two_five_six);
        assert_ne!(one, two_five_six);
        // `n - 1`, the largest.
        let mut max = n.clone();
        let last = match suite.id {
            SuiteId::P256Sha256 => 31,
            _ => 0,
        };
        max[last] -= 1;
        assert!(two_five_six < Identifier::new(suite, &max).unwrap());

        // A signature share's scalar may be zero but not `n`.
        let share = |z: &[u8]| SignatureShare::new(suite, &[one.as_ref(), z].concat());
        share(&[0; 32]).unwrap();
        assert_eq!(share(&n).err(), rejected(KeyFormatError::ScalarOutOfRange));
        assert_eq!(
            SignatureShare::new(suite, &[0; 64]).err(),
            rejected(KeyFormatError::ScalarOutOfRange)
        );
        assert_eq!(
            SignatureShare::new(suite, &[0; 63]).err(),
            rejected(KeyFormatError::WrongLength)
        );
    }
    // Suites never compare equal.
    let _entry = Entry::new_public();
    assert_ne!(
        Identifier::from_u16::<Ed25519>(1),
        Identifier::from_u16::<Ristretto255>(1)
    );
}

/// Ed25519 encodings of the identity, a small-order point, and a point
/// with a small-order component, each refused where an element is read.
fn bad_ed25519_elements() -> Vec<Vec<u8>> {
    let _entry = Entry::new_public();
    let base = edwards25519::Point::mul_base(&scalar_from_u16::<Ed25519>(1));
    // `(0, -1)`, of order 2.
    let mut order_two = [0xff; 32];
    order_two[0] = 0xec;
    order_two[31] = 0x7f;
    let torsion = edwards25519::Point::from_bytes(&order_two).unwrap();
    vec![
        Ed25519::IDENTITY.to_vec(),
        order_two.to_vec(),
        base.add(&torsion).to_bytes().to_vec(),
    ]
}

/// Malformed elements are refused wherever they are read, and never panic.
#[test]
fn refuses_bad_elements() {
    let (shares, commitment) = deal(&ED25519_SHA512, 2, 3).unwrap();
    let (_, c) = SigningNonces::commit(&shares[0]).unwrap();
    let id = shares[0].identifier().as_ref();
    let good = commitment.public_key().as_ref();
    for bad in bad_ed25519_elements() {
        assert!(PublicKey::new(&ED25519_SHA512, &bad).is_err());
        assert!(VssCommitment::new(&ED25519_SHA512, &[good, &bad].concat()).is_err());
        assert!(Commitments::new(&ED25519_SHA512, &[id, &bad, good].concat()).is_err());
        assert!(Commitments::new(&ED25519_SHA512, &[id, good, &bad].concat()).is_err());
    }
    // The NIST curve's: not on the curve, and the zeros no compressed
    // point is.
    for bad in [[&[2][..], &[0xff; 32]].concat(), vec![0; 33]] {
        assert!(PublicKey::new(&P256_SHA256, &bad).is_err());
    }
    // ristretto255's identity, and a non-canonical encoding.
    for bad in [[0u8; 32], [0xff; 32]] {
        assert!(PublicKey::new(&RISTRETTO255_SHA512, &bad).is_err());
    }
    for suite in SUITES {
        let len = with_group!(suite, G => G::ELEMENT_LEN);
        assert_eq!(
            PublicKey::new(suite, &vec![2; len + 1]).err(),
            rejected(KeyFormatError::WrongLength)
        );
        assert_eq!(
            VssCommitment::new(suite, &vec![2; len]).err(),
            Some(Error::WrongLength)
        );
        assert_eq!(
            VssCommitment::new(suite, &vec![2; 2 * len + 1]).err(),
            Some(Error::WrongLength)
        );
        assert_eq!(
            Commitments::new(suite, &c.as_ref()[1..]).err(),
            rejected(KeyFormatError::WrongLength)
        );
    }
    assert_eq!(Commitments::new(&ED25519_SHA512, c.as_ref()).unwrap(), c);
}

/// Every single-bit change to a signature or its message is refused.
#[test]
fn refuses_altered_signatures() {
    for suite in SUITES {
        let (shares, commitment) = deal(suite, 2, 2).unwrap();
        let (package, signature_shares) = sign(&shares, &[0, 1], b"message");
        let signature = package.aggregate(&signature_shares).unwrap();
        let public_key = commitment.public_key();
        let bytes = signature.as_ref();
        for bit in 0..bytes.len() * 8 {
            let mut altered = bytes.to_vec();
            altered[bit / 8] ^= 1 << (bit % 8);
            assert_eq!(
                public_key.verify(b"message", &altered),
                Err(Error::BadSignature),
                "{suite:?} bit {bit}"
            );
        }
        for len in [0, bytes.len() - 1, bytes.len() + 1] {
            let mut resized = bytes.to_vec();
            resized.resize(len, 0);
            assert_eq!(
                public_key.verify(b"message", &resized),
                Err(Error::BadSignature)
            );
        }
        // `z = n`, which a reduced check would take as zero.
        let r_len = bytes.len() - SCALAR_LEN;
        let n_z = [&bytes[..r_len], &order(suite)].concat();
        assert_eq!(
            public_key.verify(b"message", &n_z),
            Err(Error::BadSignature)
        );
    }
}

proptest::proptest! {
    /// Arbitrary bytes, for every value that reads them, never panic.
    #[test]
    fn arbitrary_inputs_never_panic(bytes in proptest::collection::vec(proptest::num::u8::ANY, 0..140)) {
        for suite in SUITES {
            Identifier::new(suite, &bytes).ok();
            PublicKey::new(suite, &bytes).ok();
            VssCommitment::new(suite, &bytes).ok();
            Commitments::new(suite, &bytes).ok();
            SignatureShare::new(suite, &bytes).ok();
        }
    }
}

/// Under `admin/ctgrind`, memcheck fails this if dealing, loading a share,
/// committing, or signing branches on or indexes by the dealer's
/// polynomial, a share, or a nonce.
#[test]
fn stays_secret() {
    fn run<G: Group>(name: &str) {
        let _entry = Entry::new_secret();
        let v = vectors(name);
        let inputs = &v["inputs"];
        let mut coefficients = vec![field(inputs, "group_secret_key")];
        for c in inputs["share_polynomial_coefficients"].as_array().unwrap() {
            coefficients.push(h(c.as_str().unwrap()));
        }
        let coefficients: Vec<G::Scalar> = coefficients
            .iter()
            .map(|c| {
                ct::secret_slice(c);
                G::scalar_from_bytes(c.as_slice().try_into().unwrap()).unwrap()
            })
            .collect();
        let (shares, commitment) = deal_with::<G>(&coefficients, 3);
        let mut loaded = Vec::new();
        for share in &shares {
            let scalar = share.to_scalar();
            loaded.push(
                SigningShare::from_scalar(share.identifier(), scalar.as_ref(), &commitment)
                    .unwrap(),
            );
        }
        let mut nonces = Vec::new();
        let mut commitments = Vec::new();
        for o in v["round_one_outputs"]["outputs"].as_array().unwrap() {
            let share = share_of(&loaded, o["identifier"].as_u64().unwrap());
            let mut random = [[0u8; 32]; 2];
            random[0].copy_from_slice(&field(o, "hiding_nonce_randomness"));
            random[1].copy_from_slice(&field(o, "binding_nonce_randomness"));
            ct::secret_slice(&random);
            let n = SigningNonces::commit_with::<G>(share, &random)
                .unwrap()
                .unwrap();
            commitments.push(n.commitments.clone());
            nonces.push((share, n));
        }
        let message = field(inputs, "message");
        let package = SigningPackage::new(commitment.public_key(), &commitments, &message).unwrap();
        let shares: Vec<_> = nonces
            .into_iter()
            .map(|(share, n)| n.sign(share, &package).unwrap())
            .collect();
        let signature = package.aggregate(&shares).unwrap();
        assert_eq!(signature.as_ref(), field(&v["final_output"], "sig"));
    }
    run::<Ed25519>("ed25519-sha512");
    run::<Ristretto255>("ristretto255-sha512");
    run::<P256>("p256-sha256");
}
