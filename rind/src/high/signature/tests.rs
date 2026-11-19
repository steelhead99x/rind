// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::error::{Error, KeyFormatError};
use crate::high::asn1::{self, Type, pkix};
use crate::high::ed25519::Ed25519SigningKey;
use crate::high::{pkcs8, spki};
use crate::low;
use crate::ml_dsa::{MlDsa44, MlDsa65, MlDsa87, ParameterSet};
use crate::slh_dsa::{
    SlhDsaSha2_128f, SlhDsaSha2_128s, SlhDsaSha2_192f, SlhDsaSha2_256f, SlhDsaShake128f,
    SlhDsaShake192f, SlhDsaShake256f,
};
use crate::{ecdsa, ed25519, ml_dsa, rsa, slh_dsa};

const ECDSA_SIGNING: [&ecdsa::SigningAlgorithm; 6] = [
    &ecdsa::sign::P256_SHA256_ASN1,
    &ecdsa::sign::P256_SHA256_FIXED,
    &ecdsa::sign::P384_SHA384_ASN1,
    &ecdsa::sign::P384_SHA384_FIXED,
    &ecdsa::sign::P521_SHA512_ASN1,
    &ecdsa::sign::P521_SHA512_FIXED,
];

/// The verification algorithm of each of [`ECDSA_SIGNING`]'s names.
const ECDSA_VERIFICATION: [&ecdsa::VerificationAlgorithm; 6] = [
    &ecdsa::verify::P256_SHA256_ASN1,
    &ecdsa::verify::P256_SHA256_FIXED,
    &ecdsa::verify::P384_SHA384_ASN1,
    &ecdsa::verify::P384_SHA384_FIXED,
    &ecdsa::verify::P521_SHA512_ASN1,
    &ecdsa::verify::P521_SHA512_FIXED,
];

fn rejected(result: Result<impl fmt::Debug, Error>) -> Error {
    result.expect_err("accepted")
}

// Each reader of a generated key pair's public key sees the same key,
// whichever reads first.
#[test]
fn ecdsa_generated_public_key_agrees_whichever_reads_first() {
    type Reader = fn(&'static ecdsa::SigningAlgorithm, &ecdsa::KeyPair) -> Vec<u8>;
    let readers: [Reader; 4] = [
        |_, pair| pair.public_key().as_ref().to_vec(),
        |_, pair| pair.public_key().to_spki().as_ref().to_vec(),
        |signing, pair| {
            let pkcs8 = pair.to_pkcs8();
            let loaded = ecdsa::KeyPair::from_pkcs8(signing, pkcs8.as_ref()).unwrap();
            loaded.public_key().to_spki().as_ref().to_vec()
        },
        |signing, pair| {
            let sec1 = pair.to_sec1();
            let loaded = ecdsa::KeyPair::from_sec1(signing, sec1.as_ref()).unwrap();
            loaded.public_key().to_spki().as_ref().to_vec()
        },
    ];
    for signing in ECDSA_SIGNING {
        for first in 0..readers.len() {
            let pair = ecdsa::KeyPair::generate(signing).unwrap();
            readers[first](signing, &pair);
            let point = pair.public_key().as_ref().to_vec();
            let spki = pair.public_key().to_spki().as_ref().to_vec();
            for (i, reader) in readers.iter().enumerate() {
                let read = reader(signing, &pair);
                let expected = if i == 0 { &point } else { &spki };
                assert_eq!(&read, expected, "{signing:?}, {first} first, {i}");
            }
        }
    }
}

#[test]
fn ecdsa_verifies_only_under_its_algorithm() {
    for (i, signing) in ECDSA_SIGNING.into_iter().enumerate() {
        let pair = ecdsa::KeyPair::generate(signing).unwrap();
        let signature = pair.sign(b"message").unwrap();
        let encoded = pair.public_key();
        for (j, algorithm) in ECDSA_VERIFICATION.into_iter().enumerate() {
            let result = ecdsa::PublicKey::new(algorithm, encoded.as_ref())
                .and_then(|key| key.verify(b"message", signature.as_ref()));
            assert_eq!(result.is_ok(), i == j, "{signing:?} {algorithm:?}");
        }
        encoded.verify(b"message", signature.as_ref()).unwrap();
        assert_eq!(
            encoded.verify(b"other", signature.as_ref()),
            Err(Error::BadSignature)
        );
    }
}

// Signing as a verify-only constant, such as a cross-hash pair, needs crate
// access, so this differential test lives here rather than in
// `tests/crosschecks.rs`. Wycheproof has no P-256 with SHA-384 vectors, nor
// P-521 with SHA-256 or SHA-384.
#[test]
#[cfg(not(any(miri, target_family = "wasm")))]
fn ecdsa_verification_matches_aws_lc_rs() {
    use aws_lc_rs::signature as theirs;

    use crate::ecdsa::verify;

    let algorithms: [(_, &'static theirs::EcdsaVerificationAlgorithm); 12] = [
        (&verify::P256_SHA256_ASN1, &theirs::ECDSA_P256_SHA256_ASN1),
        (&verify::P256_SHA384_ASN1, &theirs::ECDSA_P256_SHA384_ASN1),
        (&verify::P256_SHA512_ASN1, &theirs::ECDSA_P256_SHA512_ASN1),
        (&verify::P384_SHA256_ASN1, &theirs::ECDSA_P384_SHA256_ASN1),
        (&verify::P384_SHA384_ASN1, &theirs::ECDSA_P384_SHA384_ASN1),
        (&verify::P384_SHA512_ASN1, &theirs::ECDSA_P384_SHA512_ASN1),
        (&verify::P521_SHA256_ASN1, &theirs::ECDSA_P521_SHA256_ASN1),
        (&verify::P521_SHA384_ASN1, &theirs::ECDSA_P521_SHA384_ASN1),
        (&verify::P521_SHA512_ASN1, &theirs::ECDSA_P521_SHA512_ASN1),
        (&verify::P256_SHA256_FIXED, &theirs::ECDSA_P256_SHA256_FIXED),
        (&verify::P384_SHA384_FIXED, &theirs::ECDSA_P384_SHA384_FIXED),
        (&verify::P521_SHA512_FIXED, &theirs::ECDSA_P521_SHA512_FIXED),
    ];
    for (ours, theirs) in algorithms {
        let signing = Box::leak(Box::new(ecdsa::SigningAlgorithm::signing(ours)));
        let pair = ecdsa::KeyPair::generate(signing).unwrap();
        let signature = pair.sign(b"message").unwrap();
        let encoded = pair.public_key();
        theirs::UnparsedPublicKey::new(theirs, encoded.as_ref())
            .verify(b"message", signature.as_ref())
            .unwrap_or_else(|_| panic!("aws-lc-rs refused {ours:?}"));

        let verifier = ecdsa::PublicKey::new(ours, encoded.as_ref()).unwrap();
        verifier.verify(b"message", signature.as_ref()).unwrap();
        assert_eq!(
            verifier.verify(b"other", signature.as_ref()),
            Err(Error::BadSignature)
        );
    }
}

#[test]
fn ecdsa_signs_and_verifies_any_digest() {
    use crate::high::digest::{self, SHA256, SHA384, SHA512};
    use crate::low::ct;

    for signing in ECDSA_SIGNING {
        let pair = ecdsa::KeyPair::generate(signing).unwrap();
        let encoded = pair.public_key();
        for algorithm in [&SHA256, &SHA384, &SHA512] {
            // Under `admin/ctgrind`, nothing may branch on or index by the
            // digest, nor the key, which its hooks mark secret.
            let message = [0xa5; 100];
            ct::secret_slice(&message);
            let digest = digest::digest(algorithm, &message);
            let signature = ct::into_public(pair.sign_digest(&digest).unwrap());
            let digest = ct::into_public(digest);

            encoded
                .verify_digest(&digest, signature.as_ref())
                .unwrap_or_else(|_| panic!("{signing:?} {algorithm:?}"));
            let other = digest::digest(algorithm, b"other");
            assert_eq!(
                encoded.verify_digest(&other, signature.as_ref()),
                Err(Error::BadSignature)
            );

            // The key pair's own hash verifies a message only if the digest
            // was of that hash.
            let message = ct::into_public(message);
            assert_eq!(
                encoded.verify(&message, signature.as_ref()).is_ok(),
                core::ptr::eq(algorithm, signing.hash()),
                "{signing:?} {algorithm:?}"
            );
        }

        // A signature over a message verifies over its digest.
        let signature = pair.sign(b"message").unwrap();
        encoded
            .verify_digest(
                &digest::digest(signing.hash(), b"message"),
                signature.as_ref(),
            )
            .unwrap();
    }
}

#[test]
fn ecdsa_digests_refused_as_unsupported() {
    use crate::high::digest::{self, SHA1, SHA3_256, SHA3_384, SHA3_512, SHA256, SHA512_256};

    let sha256 = digest::digest(&SHA256, b"message");
    for signing in ECDSA_SIGNING {
        let pair = ecdsa::KeyPair::generate(signing).unwrap();
        let signature = pair.sign_digest(&sha256).unwrap();
        for algorithm in [&SHA1, &SHA512_256, &SHA3_256, &SHA3_384, &SHA3_512] {
            let digest = digest::digest(algorithm, b"message");
            assert_eq!(rejected(pair.sign_digest(&digest)), Error::Unsupported);
            assert_eq!(
                pair.public_key().verify_digest(&digest, signature.as_ref()),
                Err(Error::Unsupported)
            );
        }
    }
}

#[test]
fn public_keys_refuse_malformed_keys() {
    let pair = ecdsa::KeyPair::generate(&ecdsa::sign::P256_SHA256_ASN1).unwrap();
    let point = pair.public_key().as_ref();
    for (algorithm, bytes) in [
        (&ecdsa::verify::P256_SHA256_ASN1, &point[1..]),
        (&ecdsa::verify::P384_SHA384_ASN1, point),
    ] {
        assert!(
            ecdsa::PublicKey::new(algorithm, bytes).is_err(),
            "{algorithm:?}"
        );
    }
    assert!(ed25519::PublicKey::new(&point[..31]).is_err());
    assert!(rsa::PublicKey::new(point).is_err());

    // An Ed25519 encoding of the right length but off the curve.
    let off_curve = ed25519::PublicKey::new(&[0xff; 32]);
    assert_eq!(off_curve.err(), Some(KeyFormatError::NotOnCurve.into()));
}

#[test]
fn ecdsa_private_key_round_trips() {
    for signing in ECDSA_SIGNING {
        let pair = ecdsa::KeyPair::generate(signing).unwrap();
        let len = signing.scalar_len();
        // The scalar stays secret, so ctgrind checks the copy out and the
        // load back in.
        let scalar = pair.to_scalar();
        let scalar = scalar.as_ref();
        assert_eq!(scalar.len(), len);

        let public = pair.public_key().as_ref();
        let reloaded = ecdsa::KeyPair::from_scalar_and_public_key(signing, scalar, public).unwrap();
        assert_eq!(reloaded.public_key().as_ref(), public);
        assert_eq!(reloaded.to_pkcs8().as_ref(), pair.to_pkcs8().as_ref());

        // The scalar must be exactly the curve's length, even with a zero
        // byte added or removed.
        let padded = [&[0][..], scalar].concat();
        for scalar in [&padded[..], &scalar[1..]] {
            assert_eq!(
                rejected(ecdsa::KeyPair::from_scalar_and_public_key(
                    signing, scalar, public
                )),
                KeyFormatError::WrongLength.into()
            );
        }

        // Zero and anything at or above the order are refused.
        for scalar in [[0u8; 66], [0xff; 66]] {
            assert_eq!(
                rejected(ecdsa::KeyPair::from_scalar_and_public_key(
                    signing,
                    &scalar[..len],
                    public
                )),
                KeyFormatError::ScalarOutOfRange.into()
            );
        }

        // Another key's point, or the point truncated, is refused.
        let other = ecdsa::KeyPair::generate(signing).unwrap();
        for public in [other.public_key().as_ref(), &public[..public.len() - 1]] {
            assert_eq!(
                rejected(ecdsa::KeyPair::from_scalar_and_public_key(
                    signing, scalar, public
                )),
                KeyFormatError::MismatchedPublicKey.into()
            );
        }
    }
}

/// A scalar with its negation's point, which has the same x and the other
/// y, is refused: n - d's point is -(dG).
#[test]
fn ecdsa_p256_refuses_the_negated_point() {
    const N: [u8; 32] = [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63,
        0x25, 0x51,
    ];
    let signing = &ecdsa::sign::P256_SHA256_FIXED;
    let pair = ecdsa::KeyPair::generate(signing).unwrap();
    // The subtraction below branches on the scalar in a debug build.
    let scalar = pair.to_scalar();
    low::ct::public_slice(scalar.as_ref());
    let mut negated = [0u8; 32];
    let mut borrow = 0;
    for i in (0..32).rev() {
        let difference = i16::from(N[i]) - i16::from(scalar.as_ref()[i]) - borrow;
        negated[i] = difference as u8;
        borrow = i16::from(difference < 0);
    }
    assert_eq!(
        rejected(ecdsa::KeyPair::from_scalar_and_public_key(
            signing,
            &negated,
            pair.public_key().as_ref()
        )),
        KeyFormatError::MismatchedPublicKey.into()
    );
}

#[test]
fn ecdsa_key_is_bound_to_its_curve() {
    use crate::ecdsa::{KeyPair, PublicKey, sign, verify};

    let p256 = include_bytes!("../ecdsa/secp256r1.pkcs8.der");
    let p384 = include_bytes!("../ecdsa/secp384r1.pkcs8.der");
    let p521 = include_bytes!("../ecdsa/secp521r1.pkcs8.der");
    KeyPair::from_pkcs8(&sign::P256_SHA256_ASN1, p256).unwrap();
    KeyPair::from_pkcs8(&sign::P384_SHA384_ASN1, p384).unwrap();
    KeyPair::from_pkcs8(&sign::P521_SHA512_ASN1, p521).unwrap();
    assert!(KeyPair::from_pkcs8(&sign::P256_SHA256_ASN1, p384).is_err());
    assert!(KeyPair::from_pkcs8(&sign::P384_SHA384_ASN1, p256).is_err());
    assert!(KeyPair::from_pkcs8(&sign::P384_SHA384_ASN1, p521).is_err());
    assert!(KeyPair::from_pkcs8(&sign::P521_SHA512_ASN1, p384).is_err());

    let p256 = include_bytes!("../ecdsa/secp256r1.der");
    let p384 = include_bytes!("../ecdsa/secp384r1.der");
    KeyPair::from_sec1(&sign::P256_SHA256_ASN1, p256).unwrap();
    assert!(KeyPair::from_sec1(&sign::P256_SHA256_ASN1, p384).is_err());

    // A P-384 point is the wrong length for a P-256 key.
    let pair = KeyPair::from_pkcs8(
        &sign::P384_SHA384_ASN1,
        include_bytes!("../ecdsa/secp384r1.pkcs8.der"),
    )
    .unwrap();
    assert_eq!(
        rejected(PublicKey::new(
            &verify::P256_SHA384_ASN1,
            pair.public_key().as_ref()
        )),
        KeyFormatError::WrongLength.into()
    );
}

#[test]
fn key_loaders_refuse_trailing_bytes() {
    type Load = fn(&[u8]) -> Result<(), Error>;
    let cases: [(&[u8], Load); 8] = [
        (include_bytes!("../ecdsa/secp256r1.pkcs8.der"), |der| {
            ecdsa::KeyPair::from_pkcs8(&ecdsa::sign::P256_SHA256_ASN1, der).map(drop)
        }),
        (include_bytes!("../ecdsa/secp384r1.pkcs8.der"), |der| {
            ecdsa::KeyPair::from_pkcs8(&ecdsa::sign::P384_SHA384_ASN1, der).map(drop)
        }),
        (include_bytes!("../ecdsa/secp521r1.pkcs8.der"), |der| {
            ecdsa::KeyPair::from_pkcs8(&ecdsa::sign::P521_SHA512_ASN1, der).map(drop)
        }),
        (include_bytes!("../ecdsa/secp256r1.der"), |der| {
            ecdsa::KeyPair::from_sec1(&ecdsa::sign::P256_SHA256_ASN1, der).map(drop)
        }),
        (include_bytes!("../rsa/rsa2048.pkcs8.der"), |der| {
            rsa::KeyPair::from_pkcs8(der).map(drop)
        }),
        (include_bytes!("../rsa/rsa2048.der"), |der| {
            rsa::KeyPair::from_pkcs1(der).map(drop)
        }),
        (include_bytes!("../rsa/rsa2047.pub.der"), |der| {
            rsa::PublicKey::new(der).map(drop)
        }),
        (include_bytes!("../asn1/testdata/ed25519-p8v2.bin"), |der| {
            ed25519::KeyPair::from_pkcs8(der).map(drop)
        }),
    ];
    for (der, load) in cases {
        load(der).unwrap();
        assert_eq!(
            rejected(load(&[der, &[0x00]].concat())),
            KeyFormatError::Asn1(asn1::Error::UnexpectedTrailingData).into(),
            "{der:02x?}",
        );
    }
}

#[test]
fn rsa_signs_as_long_as_the_modulus() {
    use crate::rsa::{KeyPair, PublicKey, sign, verify};

    let pair = KeyPair::from_pkcs1(include_bytes!("../rsa/rsa2048.der")).unwrap();
    let signature = pair.sign(&sign::PSS_SHA256, b"message").unwrap();
    assert_eq!(signature.as_ref().len(), 256);

    let public_key = pair.public_key();
    public_key
        .verify(&verify::PSS_SHA256, b"message", signature.as_ref())
        .unwrap();
    assert_eq!(
        public_key.verify(&verify::PSS_SHA256, b"other", signature.as_ref()),
        Err(Error::BadSignature)
    );
    assert_eq!(
        public_key.verify(&verify::PKCS1_SHA256, b"message", signature.as_ref()),
        Err(Error::BadSignature)
    );

    // The encoding parses back.
    PublicKey::new(public_key.as_ref())
        .unwrap()
        .verify(&verify::PSS_SHA256, b"message", signature.as_ref())
        .unwrap();
}

#[test]
fn rsa_public_key_components() {
    use crate::rsa::{KeyPair, PublicKey, PublicKeyComponents, sign, verify};

    let pair = KeyPair::from_pkcs1(include_bytes!("../rsa/rsa2048.der")).unwrap();
    let signature = pair.sign(&sign::PKCS1_SHA256, b"message").unwrap();
    let signature = signature.as_ref();

    let der = pair.public_key();
    let parsed = pkix::RSAPublicKey::from_bytes(der.as_ref()).unwrap();
    let n = parsed.modulus.as_ref().strip_prefix(&[0]).unwrap();
    let e = parsed.publicExponent.as_ref();
    let key = PublicKeyComponents { n, e };
    let public_key = PublicKey::from_components(&key).unwrap();
    assert_eq!(public_key.as_ref(), der.as_ref());
    for algorithm in [&verify::PKCS1_SHA256, &verify::legacy::PKCS1_1024_SHA256] {
        public_key.verify(algorithm, b"message", signature).unwrap();
        assert_eq!(
            public_key.verify(algorithm, b"other", signature),
            Err(Error::BadSignature)
        );
    }
    for algorithm in [
        &verify::legacy::PKCS1_SHA1,
        &verify::legacy::PKCS1_1024_SHA512,
    ] {
        assert_eq!(
            public_key.verify(algorithm, b"message", signature),
            Err(Error::BadSignature)
        );
    }

    // A 2048-bit key is below this algorithm's floor.
    assert_eq!(
        public_key.verify(&verify::legacy::PKCS1_3072_SHA384, b"message", signature),
        Err(KeyFormatError::RsaModulus.into())
    );

    let n0 = [&[0], n].concat();
    let e0 = [&[0], e].concat();
    let malformed: [(&[u8], &[u8], Error); 5] = [
        (&n0, e, KeyFormatError::LeadingZero.into()),
        (n, &e0, KeyFormatError::LeadingZero.into()),
        (n, &[2, 0, 0, 0, 1], KeyFormatError::RsaExponent.into()),
        (&[], e, KeyFormatError::RsaModulus.into()),
        (n, &[], KeyFormatError::RsaExponent.into()),
    ];
    for (n, e, expected) in malformed {
        let key = PublicKeyComponents { n, e };
        assert_eq!(rejected(PublicKey::from_components(&key)), expected);
    }
}

/// A PKCS#8 ML-DSA key of `oid` holding `private_key`, and `public_key` if
/// given (v2).
fn ml_dsa_pkcs8(
    oid: &asn1::ObjectId,
    private_key: pkix::MlDsaPrivateKey<'_>,
    public_key: Option<&[u8]>,
) -> Vec<u8> {
    let mut inner = vec![0; 10_000];
    let len = private_key
        .encode(&mut asn1::Encoder::new(&mut inner))
        .unwrap();
    assert_eq!(private_key.encoded_len(), len);
    let mut out = vec![0; 20_000];
    let der = pkcs8::Key::construct(&inner[..len], public_key, oid.clone(), None)
        .encode(&mut out)
        .unwrap();
    der.to_vec()
}

#[test]
fn ml_dsa_encodings() {
    fn check<P: ParameterSet>(other: &asn1::ObjectId) {
        use crate::ml_dsa::{KeyPair, PublicKey};

        // This compares encodings of the key, so declassifies them.
        let pair = KeyPair::<P>::generate().unwrap();
        let seed: [u8; 32] = pair.to_seed().unwrap().as_ref().try_into().unwrap();
        let seed = low::ct::into_public(seed);
        let seed = asn1::OctetString::new(&seed);
        let sk = low::ct::into_public(pair.inner().secret_key().clone());
        let sk = sk.as_ref();
        let expanded = asn1::OctetString::new(sk);
        let pk = pair.public_key().as_ref();
        let oid = KeyPair::<P>::oid();
        let load = |der: &[u8]| KeyPair::<P>::from_pkcs8(der);
        let seed_form = ml_dsa_pkcs8(oid, pkix::MlDsaPrivateKey::Seed(seed.clone()), None);
        assert_eq!(pair.to_pkcs8().as_ref(), seed_form);

        // Each form loads, and a key without its seed writes the expanded
        // form.
        let both = |expanded| {
            pkix::MlDsaPrivateKey::Both(pkix::MlDsaSeedAndKey {
                seed: seed.clone(),
                expandedKey: expanded,
            })
        };
        let expanded_form = ml_dsa_pkcs8(
            oid,
            pkix::MlDsaPrivateKey::ExpandedKey(expanded.clone()),
            None,
        );
        for (der, has_seed) in [
            (seed_form.clone(), true),
            (expanded_form.clone(), false),
            (ml_dsa_pkcs8(oid, both(expanded.clone()), None), true),
            (ml_dsa_pkcs8(oid, both(expanded.clone()), Some(pk)), true),
        ] {
            let key = load(&der).unwrap();
            assert_eq!(key.public_key().as_ref(), pk);
            assert_eq!(key.to_seed().is_some(), has_seed);
            assert_eq!(key.has_seed(), has_seed);
            let written = key.to_pkcs8();
            let want = if has_seed { &seed_form } else { &expanded_form };
            assert_eq!(written.as_ref(), want);
        }

        // A seed and expanded key that disagree.
        let mut wrong = sk.to_vec();
        wrong[sk.len() - 1] ^= 1;
        let der = ml_dsa_pkcs8(oid, both(asn1::OctetString::new(&wrong)), None);
        assert_eq!(
            rejected(load(&der)),
            KeyFormatError::MismatchedMlDsaSeed.into()
        );
        let der = ml_dsa_pkcs8(oid, both(asn1::OctetString::new(&sk[1..])), None);
        assert_eq!(
            rejected(load(&der)),
            KeyFormatError::MismatchedMlDsaSeed.into()
        );

        // An expanded key whose parts disagree: its `t0`, its `tr`.
        let der = ml_dsa_pkcs8(
            oid,
            pkix::MlDsaPrivateKey::ExpandedKey(asn1::OctetString::new(&wrong)),
            None,
        );
        assert_eq!(rejected(load(&der)), KeyFormatError::MlDsaSecretKey.into());
        let mut wrong = sk.to_vec();
        wrong[2 * 32] ^= 1;
        let der = ml_dsa_pkcs8(
            oid,
            pkix::MlDsaPrivateKey::ExpandedKey(asn1::OctetString::new(&wrong)),
            None,
        );
        assert_eq!(rejected(load(&der)), KeyFormatError::MlDsaSecretKey.into());

        // A public key (v2) that does not match.
        let other_pair = KeyPair::<P>::generate().unwrap();
        let der = ml_dsa_pkcs8(
            oid,
            pkix::MlDsaPrivateKey::Seed(seed.clone()),
            Some(other_pair.public_key().as_ref()),
        );
        assert_eq!(
            rejected(load(&der)),
            KeyFormatError::MismatchedPkcs8PublicKey.into()
        );

        // Lengths, another parameter set, and trailing bytes.
        for bad in [&sk[..31], &[0; 33][..]] {
            let der = ml_dsa_pkcs8(
                oid,
                pkix::MlDsaPrivateKey::Seed(asn1::OctetString::new(bad)),
                None,
            );
            assert_eq!(rejected(load(&der)), KeyFormatError::WrongLength.into());
            assert_eq!(
                rejected(KeyPair::<P>::from_seed(bad)),
                KeyFormatError::WrongLength.into()
            );
        }
        let der = ml_dsa_pkcs8(
            oid,
            pkix::MlDsaPrivateKey::ExpandedKey(asn1::OctetString::new(&sk[1..])),
            None,
        );
        assert_eq!(rejected(load(&der)), KeyFormatError::WrongLength.into());
        let der = ml_dsa_pkcs8(other, pkix::MlDsaPrivateKey::Seed(seed.clone()), None);
        assert_eq!(
            rejected(load(&der)),
            KeyFormatError::MismatchedPkcs8Algorithm.into()
        );
        let mut der = seed_form.clone();
        der.push(0);
        assert!(load(&der).is_err());
        // A private key of another tag, such as an explicit `[0]`.
        let mut der = seed_form.clone();
        let tag = der.len() - 34;
        assert_eq!(der[tag], 0x80);
        der[tag] = 0xa0;
        assert!(load(&der).is_err());

        // Public keys: lengths, and another parameter set's SPKI.
        let spki = pair.public_key().to_spki();
        let parsed = PublicKey::<P>::from_spki(spki.as_ref()).unwrap();
        assert_eq!(parsed.as_ref(), pk);
        for bad in [&pk[1..], &[pk, &[0]].concat()] {
            assert_eq!(
                rejected(PublicKey::<P>::new(bad)),
                KeyFormatError::WrongLength.into()
            );
        }
        let mut out = vec![0; 4096];
        let other_spki = spki::encode(pk, other, None, &mut out).unwrap();
        assert_eq!(
            rejected(PublicKey::<P>::from_spki(other_spki)),
            KeyFormatError::MismatchedSpkiAlgorithm.into()
        );
        let signature = pair.sign(b"message").unwrap();
        parsed.verify(b"message", signature.as_ref()).unwrap();
        assert_eq!(
            parsed.verify(b"other", signature.as_ref()),
            Err(Error::BadSignature)
        );
    }
    check::<MlDsa44>(&asn1::oid::id_ml_dsa_65);
    // The other parameter sets run the same encoding code, too slowly for
    // Miri.
    if !cfg!(miri) {
        check::<MlDsa65>(&asn1::oid::id_ml_dsa_87);
        check::<MlDsa87>(&asn1::oid::id_ml_dsa_44);
    }
}

/// A PKCS#8 SLH-DSA key of `oid` holding `private_key`, and `public_key`
/// if given (v2).
fn slh_dsa_pkcs8(oid: &asn1::ObjectId, private_key: &[u8], public_key: Option<&[u8]>) -> Vec<u8> {
    let mut out = vec![0; 1024];
    let der = pkcs8::Key::construct(private_key, public_key, oid.clone(), None)
        .encode(&mut out)
        .unwrap();
    der.to_vec()
}

#[test]
fn slh_dsa_encodings() {
    // Only the f sets: an s set's key costs a tenth of a second to load
    // in a debug build, and its signature seconds. The differential
    // tests match every set's encodings with RustCrypto's.
    fn check<P: slh_dsa::ParameterSet>(other: &asn1::ObjectId) {
        // This compares encodings of the key, so declassifies them.
        let pair = slh_dsa::KeyPair::<P>::generate().unwrap();
        let sk = low::ct::into_public(pair.inner().secret_key().clone());
        let sk = sk.as_ref();
        let pk = pair.inner().public_key();
        let oid = slh_dsa::KeyPair::<P>::oid();
        let load = |der: &[u8]| slh_dsa::KeyPair::<P>::from_pkcs8(der);
        let v1 = slh_dsa_pkcs8(oid, sk, None);
        assert_eq!(pair.to_pkcs8().as_ref(), v1);
        assert_eq!(pair.public_key().as_ref(), pk);
        for der in [&v1, &slh_dsa_pkcs8(oid, sk, Some(pk))] {
            let key = load(der).unwrap();
            assert_eq!(key.public_key().as_ref(), pk);
            assert_eq!(key.to_pkcs8().as_ref(), v1);
        }

        // A root its seeds do not make, and a public key (v2) that does
        // not match.
        let mut wrong = sk.to_vec();
        wrong[sk.len() - 1] ^= 1;
        assert_eq!(
            rejected(load(&slh_dsa_pkcs8(oid, &wrong, None))),
            KeyFormatError::MismatchedPublicKey.into()
        );
        assert_eq!(
            rejected(load(&slh_dsa_pkcs8(
                oid,
                sk,
                Some(&wrong[wrong.len() / 2..])
            ))),
            KeyFormatError::MismatchedPkcs8PublicKey.into()
        );

        // Lengths, another parameter set, and trailing bytes.
        for bad in [&sk[1..], &[sk, &[0]].concat()] {
            assert_eq!(
                rejected(load(&slh_dsa_pkcs8(oid, bad, None))),
                KeyFormatError::WrongLength.into()
            );
        }
        assert_eq!(
            rejected(load(&slh_dsa_pkcs8(other, sk, None))),
            KeyFormatError::MismatchedPkcs8Algorithm.into()
        );
        let mut der = v1.clone();
        der.push(0);
        assert!(load(&der).is_err());

        // Public keys: lengths and another parameter set's SPKI.
        let spki = pair.public_key().to_spki();
        let parsed = slh_dsa::PublicKey::<P>::from_spki(spki.as_ref()).unwrap();
        assert_eq!(parsed.as_ref(), pk);
        for bad in [&pk[1..], &[pk, &[0]].concat()] {
            assert_eq!(
                rejected(slh_dsa::PublicKey::<P>::new(bad)),
                KeyFormatError::WrongLength.into()
            );
        }
        let mut out = vec![0; 1024];
        let other_spki = spki::encode(pk, other, None, &mut out).unwrap();
        assert_eq!(
            rejected(slh_dsa::PublicKey::<P>::from_spki(other_spki)),
            KeyFormatError::MismatchedSpkiAlgorithm.into()
        );
        // A signature takes Miri half an hour; the native runs sign.
        if cfg!(miri) {
            return;
        }
        let signature = pair.sign(b"message").unwrap();
        assert_eq!(signature.as_ref().len(), P::SIG_LEN);
        parsed.verify(b"message", signature.as_ref()).unwrap();
        assert_eq!(
            parsed.verify(b"massage", signature.as_ref()),
            Err(Error::BadSignature)
        );
    }
    check::<SlhDsaSha2_128f>(&asn1::oid::id_slh_dsa_shake_128f);
    // The other sets run the same encoding code, too slowly for Miri.
    if cfg!(miri) {
        return;
    }
    check::<SlhDsaShake128f>(&asn1::oid::id_slh_dsa_sha2_128f);
    if crate::test::CTGRIND_DEBUG {
        return;
    }
    check::<SlhDsaSha2_192f>(&asn1::oid::id_slh_dsa_sha2_192s);
    check::<SlhDsaSha2_256f>(&asn1::oid::id_slh_dsa_sha2_128f);
    check::<SlhDsaShake192f>(&asn1::oid::id_slh_dsa_shake_256f);
    check::<SlhDsaShake256f>(&asn1::oid::id_slh_dsa_shake_192f);
}

/// RFC 9909's examples: a key pair, and a certificate it signs itself.
#[test]
fn slh_dsa_rfc9909() {
    // Its key is a 128s one, so slow to load under ctgrind's debug build.
    if crate::test::CTGRIND_DEBUG {
        return;
    }
    let read = |name: &str| {
        std::fs::read(format!(
            "{}/../thirdparty/vectors/rfc9909/{name}",
            env!("CARGO_MANIFEST_DIR")
        ))
        .unwrap()
    };
    let (public, private, certificate) = (
        read("public-key.der"),
        read("private-key.der"),
        read("certificate.der"),
    );
    let pair = slh_dsa::KeyPair::<SlhDsaSha2_128s>::from_pkcs8(&private).unwrap();
    assert_eq!(pair.to_pkcs8().as_ref(), private);
    assert_eq!(pair.public_key().to_spki().as_ref(), public);

    // Certificate ::= SEQUENCE { tbsCertificate, signatureAlgorithm,
    // signatureValue BIT STRING }, each long enough for a two-byte
    // length.
    let field = |der: &[u8], tag: u8| -> usize {
        assert_eq!(der[..2], [tag, 0x82]);
        4 + usize::from(u16::from_be_bytes([der[2], der[3]]))
    };
    let body = &certificate[4..field(&certificate, 0x30)];
    let tbs = &body[..field(body, 0x30)];
    let algorithm = &body[tbs.len()..][..13];
    assert_eq!(algorithm[..4], [0x30, 11, 6, 9]);
    let signature = &body[tbs.len() + 13..];
    let signature = &signature[..field(signature, 0x03)][5..];
    let key = slh_dsa::PublicKey::<SlhDsaSha2_128s>::from_spki(&public).unwrap();
    key.verify(tbs, signature).unwrap();
}

#[test]
fn ed25519_seed_and_public_key() {
    use crate::ed25519::KeyPair;

    let seed = [7u8; 32];
    let public = Ed25519SigningKey::from_bytes(&seed)
        .unwrap()
        .public_key()
        .as_bytes();
    let pair = KeyPair::from_seed_and_public_key(&seed, &public).unwrap();
    let encoded = pair.public_key();
    assert_eq!(encoded.as_ref(), public);
    let signature = pair.sign(b"message");
    assert_eq!(signature.as_ref().len(), 64);
    encoded.verify(b"message", signature.as_ref()).unwrap();

    let other = KeyPair::generate().unwrap();
    for public in [other.public_key().as_ref(), &public[..31]] {
        assert_eq!(
            rejected(KeyPair::from_seed_and_public_key(&seed, public)),
            KeyFormatError::MismatchedPublicKey.into()
        );
    }
    for seed in [&seed[..31], &[seed.as_slice(), &[0]].concat()] {
        assert_eq!(
            rejected(KeyPair::from_seed_and_public_key(seed, &public)),
            KeyFormatError::WrongLength.into()
        );
    }
}

#[test]
fn ed25519_seed_round_trips() {
    use crate::ed25519::KeyPair;

    // The seed stays secret, so ctgrind checks the copy out and the load
    // back in.
    let pair = KeyPair::generate().unwrap();
    let seed = pair.to_seed();
    let public = pair.public_key();
    let reloaded = KeyPair::from_seed_and_public_key(seed.as_ref(), public.as_ref()).unwrap();
    assert_eq!(reloaded.to_pkcs8().as_ref(), pair.to_pkcs8().as_ref());
}

#[test]
fn ed25519_seed_loads_alone() {
    use crate::ed25519::KeyPair;

    // The seed stays secret, so ctgrind checks the load and both PKCS#8
    // encodings.
    let pair = KeyPair::generate().unwrap();
    let seed = pair.to_seed();
    let reloaded = KeyPair::from_seed(seed.as_ref()).unwrap();
    assert_eq!(reloaded.public_key().as_ref(), pair.public_key().as_ref());
    assert_eq!(reloaded.to_pkcs8().as_ref(), pair.to_pkcs8().as_ref());

    // v1 is RFC 8410's fixed prefix and the seed, which loads back.
    let v1 = pair.to_pkcs8v1();
    assert_eq!(v1.as_ref().len(), 48);
    assert_eq!(
        v1.as_ref()[..16],
        include_bytes!("../asn1/testdata/ed25519-p8v1.bin")[..16]
    );
    let reloaded = KeyPair::from_pkcs8(v1.as_ref()).unwrap();
    assert_eq!(reloaded.public_key().as_ref(), pair.public_key().as_ref());

    for seed in [&[0; 31][..], &[0; 33]] {
        assert_eq!(
            rejected(KeyPair::from_seed(seed)),
            KeyFormatError::WrongLength.into()
        );
    }
}

#[test]
fn ecdsa_sec1_round_trips() {
    for signing in ECDSA_SIGNING {
        // The key is secret, so ctgrind checks the encoding.
        let pair = ecdsa::KeyPair::generate(signing).unwrap();
        let sec1 = pair.to_sec1();
        let reloaded = ecdsa::KeyPair::from_sec1(signing, sec1.as_ref()).unwrap();
        assert_eq!(reloaded.to_pkcs8().as_ref(), pair.to_pkcs8().as_ref());

        // It names its curve and holds its public key, as the
        // `ECPrivateKey` inside PKCS#8 does, which names neither.
        let decoded = pkix::EcPrivateKey::from_bytes(sec1.as_ref()).unwrap();
        assert_eq!(decoded.parameters.inner(), &Some(signing.curve_oid()));
        assert_eq!(
            decoded
                .publicKey
                .inner()
                .as_ref()
                .map(|key| key.as_octets()),
            Some(pair.public_key().as_ref())
        );
    }
}

#[test]
fn public_keys_round_trip_through_spki() {
    /// Parses an SPKI as one kind of key, returning its encoding.
    type Parse = fn(&[u8]) -> Result<Vec<u8>, Error>;

    let rsa = rsa::KeyPair::from_pkcs1(include_bytes!("../rsa/rsa2048.der")).unwrap();
    let ed25519 = ed25519::KeyPair::generate().unwrap();
    let ml_dsa = ml_dsa::KeyPair::<MlDsa44>::generate().unwrap();
    // Each kind of key: its encoding, its SPKI, and its parser.
    let mut keys: Vec<(String, Vec<u8>, Vec<u8>, Parse)> = vec![
        (
            "RSA".into(),
            rsa.public_key().as_ref().to_vec(),
            rsa.public_key().to_spki().as_ref().to_vec(),
            |der| rsa::PublicKey::from_spki(der).map(|key| key.as_ref().to_vec()),
        ),
        (
            "Ed25519".into(),
            ed25519.public_key().as_ref().to_vec(),
            ed25519.public_key().to_spki().as_ref().to_vec(),
            |der| ed25519::PublicKey::from_spki(der).map(|key| key.as_ref().to_vec()),
        ),
        (
            "ML-DSA-44".into(),
            ml_dsa.public_key().as_ref().to_vec(),
            ml_dsa.public_key().to_spki().as_ref().to_vec(),
            |der| ml_dsa::PublicKey::<MlDsa44>::from_spki(der).map(|key| key.as_ref().to_vec()),
        ),
    ];
    let parsers: [Parse; 3] = [
        |der| {
            ecdsa::PublicKey::from_spki(&ecdsa::verify::P256_SHA256_ASN1, der)
                .map(|key| key.as_ref().to_vec())
        },
        |der| {
            ecdsa::PublicKey::from_spki(&ecdsa::verify::P384_SHA384_ASN1, der)
                .map(|key| key.as_ref().to_vec())
        },
        |der| {
            ecdsa::PublicKey::from_spki(&ecdsa::verify::P521_SHA512_ASN1, der)
                .map(|key| key.as_ref().to_vec())
        },
    ];
    for (signing, parse) in [ECDSA_SIGNING[0], ECDSA_SIGNING[2], ECDSA_SIGNING[4]]
        .into_iter()
        .zip(parsers)
    {
        let pair = ecdsa::KeyPair::generate(signing).unwrap();
        let public = pair.public_key();
        keys.push((
            format!("{signing:?}"),
            public.as_ref().to_vec(),
            public.to_spki().as_ref().to_vec(),
            parse,
        ));
    }

    for (kind, key, spki, parse) in &keys {
        assert_eq!(parse(spki).unwrap(), *key, "{kind}");
        // The bare key is no SPKI.
        assert!(parse(key).is_err(), "{kind}");
        // Nor is another kind's.
        for (other, _, other_spki, _) in &keys {
            assert_eq!(kind == other, parse(other_spki).is_ok(), "{kind} {other}");
        }
    }
}

#[test]
fn ecdsa_spki_decompresses() {
    use crate::ecdsa::{KeyPair, PublicKey};

    for (signing, verification) in [
        (ECDSA_SIGNING[0], ECDSA_VERIFICATION[0]),
        (ECDSA_SIGNING[2], ECDSA_VERIFICATION[2]),
        (ECDSA_SIGNING[4], ECDSA_VERIFICATION[4]),
    ] {
        let pair = KeyPair::generate(signing).unwrap();
        let point = pair.public_key().as_ref();
        let (x, y) = point[1..].split_at(point.len() / 2);
        let curve = Some(asn1::Any::ObjectId(signing.curve_oid()));
        let spki = |key: &[u8]| {
            let mut der = [0; 256];
            let der = spki::encode(key, &asn1::oid::id_ecPublicKey, curve.clone(), &mut der);
            der.unwrap().to_vec()
        };

        let compressed = [&[2 | (y[y.len() - 1] & 1)][..], x].concat();
        let parsed = PublicKey::from_spki(verification, &spki(&compressed)).unwrap();
        assert_eq!(parsed.as_ref(), point);
        let signature = pair.sign(b"message").unwrap();
        parsed.verify(b"message", signature.as_ref()).unwrap();

        // `new` takes it uncompressed only, and a hybrid point is refused
        // either way.
        assert_eq!(
            rejected(PublicKey::new(verification, &compressed)),
            KeyFormatError::Compressed.into()
        );
        let hybrid = [&[6 | (y[y.len() - 1] & 1)][..], &point[1..]].concat();
        assert_eq!(
            rejected(PublicKey::from_spki(verification, &spki(&hybrid))),
            KeyFormatError::PointEncoding.into()
        );

        // `id-ecDH` names an ECDH key, not an ECDSA one.
        let mut der = [0; 256];
        let ecdh = spki::encode(point, &asn1::oid::id_ecDH, curve.clone(), &mut der).unwrap();
        assert_eq!(
            rejected(PublicKey::from_spki(verification, ecdh)),
            KeyFormatError::MismatchedSpkiAlgorithm.into()
        );
    }
}

// The owned encodings are sized for the largest key each loader takes, so
// encoding one must not run out of room.
#[test]
fn encodings_fit_the_largest_keys() {
    let rsa = rsa::KeyPair::from_pkcs1(include_bytes!("../rsa/rsa8192.der")).unwrap();
    let pkcs8 = rsa.to_pkcs8();
    assert_eq!(pkcs8.as_ref(), include_bytes!("../rsa/rsa8192.pkcs8.der"));
    let spki = rsa.public_key().to_spki();
    let parsed = pkix::SubjectPublicKeyInfo::from_bytes(spki.as_ref()).unwrap();
    assert_eq!(
        parsed.subjectPublicKey.as_octets(),
        rsa.public_key().as_ref()
    );
    let signature = rsa.sign(&rsa::sign::PSS_SHA512, b"message").unwrap();
    assert_eq!(signature.as_ref().len(), 1024);
    rsa.public_key()
        .verify(&rsa::verify::PSS_SHA512, b"message", signature.as_ref())
        .unwrap();

    let p521 = include_bytes!("../ecdsa/secp521r1.pkcs8.der");
    let signing = &ecdsa::sign::P521_SHA512_ASN1;
    let ecdsa = ecdsa::KeyPair::from_pkcs8(signing, p521).unwrap();
    let reloaded = ecdsa::KeyPair::from_pkcs8(signing, ecdsa.to_pkcs8().as_ref()).unwrap();
    assert_eq!(reloaded.public_key().as_ref(), ecdsa.public_key().as_ref());
    let spki = ecdsa.public_key().to_spki();
    let parsed = pkix::SubjectPublicKeyInfo::from_bytes(spki.as_ref()).unwrap();
    assert_eq!(
        parsed.subjectPublicKey.as_octets(),
        ecdsa.public_key().as_ref()
    );

    let ml_dsa = ml_dsa::KeyPair::<MlDsa87>::generate().unwrap();
    let spki = ml_dsa.public_key().to_spki();
    let parsed = pkix::SubjectPublicKeyInfo::from_bytes(spki.as_ref()).unwrap();
    assert_eq!(
        parsed.subjectPublicKey.as_octets(),
        ml_dsa.public_key().as_ref()
    );

    let ed25519 = ed25519::KeyPair::generate().unwrap();
    let reloaded = ed25519::KeyPair::from_pkcs8(ed25519.to_pkcs8().as_ref()).unwrap();
    assert_eq!(
        reloaded.public_key().as_ref(),
        ed25519.public_key().as_ref()
    );
    let spki = ed25519.public_key().to_spki();
    let parsed = pkix::SubjectPublicKeyInfo::from_bytes(spki.as_ref()).unwrap();
    assert_eq!(
        parsed.subjectPublicKey.as_octets(),
        ed25519.public_key().as_ref()
    );
}

/// A cloned public key verifies what the original does, with an expansion
/// of its own, and a cloned signature is the same bytes.
#[test]
fn post_quantum_clones_verify() {
    let key = ml_dsa::KeyPair::<MlDsa44>::generate().unwrap();
    let signature = key.sign(b"message").unwrap();
    let copy = signature.clone();
    assert_eq!(copy.as_ref(), signature.as_ref());
    let public_key = key.public_key().clone();
    for _ in 0..2 {
        public_key.verify(b"message", copy.as_ref()).unwrap();
    }
    assert_eq!(public_key.as_ref(), key.public_key().as_ref());
    let clone = public_key.clone();
    clone.verify(b"message", signature.as_ref()).unwrap();

    let key = slh_dsa::KeyPair::<SlhDsaSha2_128f>::generate().unwrap();
    let signature = key.sign(b"message").unwrap();
    let copy = signature.clone();
    assert_eq!(copy.as_ref(), signature.as_ref());
    let public_key = key.public_key().clone();
    assert_eq!(public_key.as_ref(), key.public_key().as_ref());
    public_key.verify(b"message", copy.as_ref()).unwrap();
}

/// Ed25519 and RSA signatures show as their bytes.
#[test]
fn signatures_debug_as_bytes() {
    let key = ed25519::KeyPair::from_seed(&[7; 32]).unwrap();
    let signature = key.sign(b"message");
    assert_eq!(
        format!("{signature:?}"),
        format!("Signature({:?})", signature.as_ref())
    );
    let key = rsa::KeyPair::from_pkcs8(include_bytes!("../rsa/rsa2048.pkcs8.der")).unwrap();
    let signature = key.sign(&rsa::sign::PKCS1_SHA256, b"message").unwrap();
    assert_eq!(
        format!("{signature:?}"),
        format!("Signature({:?})", signature.as_ref())
    );
}
