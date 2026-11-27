//! Differential tests of ECDSA, ECDH, Ed25519, X25519, and PKCS#8 key
//! encodings against aws-lc and independent oracles, which Miri cannot run.
#![cfg(not(any(miri, target_family = "wasm")))]

use aws_lc_rs::signature::Ed25519KeyPair;

mod common;
use common::der;

#[test]
fn ed25519_key_generation() {
    for _ in 0..100 {
        let key = rind::ed25519::KeyPair::generate().unwrap();
        let key_enc = key.to_pkcs8();
        let key_enc = key_enc.as_ref();

        let seed: [u8; 32] = key.to_seed().as_ref().try_into().unwrap();
        assert_eq!(
            key.public_key().as_ref(),
            oracle::ed25519::public_key(&seed),
            "the independent oracle derived another public key"
        );
        let aws = Ed25519KeyPair::from_pkcs8(key_enc)
            .expect("aws-lc-rs rejected an ed25519 key we generated");
        assert_eq!(
            aws.to_pkcs8().unwrap().as_ref(),
            key_enc,
            "aws-lc-rs varied our ed25519 key encoding"
        );
    }
}

#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
#[path = "../src/test/reference.rs"]
mod reference;

/// The independent oracles of the curves and Ed25519, which the fuzz targets
/// share.
mod oracle {
    #[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
    use crate::reference;

    pub(crate) mod ed25519;
    mod nist;
    pub(crate) use nist::*;
}

/// RustCrypto's `pkcs8` reading of a PKCS#8 key: its algorithm's OID and
/// its private key's bytes.
fn rustcrypto_pkcs8(der: &[u8]) -> (String, Vec<u8>) {
    let info = pkcs8::PrivateKeyInfoRef::try_from(der).unwrap();
    (
        info.algorithm.oid.to_string(),
        info.private_key.as_bytes().to_vec(),
    )
}

/// RustCrypto's `spki` reading of an SPKI: its algorithm's OID and its
/// public key's bytes.
fn rustcrypto_spki(der: &[u8]) -> (String, Vec<u8>) {
    let info = pkcs8::SubjectPublicKeyInfoRef::try_from(der).unwrap();
    let key = info.subject_public_key.as_bytes().unwrap();
    (info.algorithm.oid.to_string(), key.to_vec())
}

/// ECDSA and ECDH on one curve: aws-lc-rs and rind accept each other's keys,
/// signatures, and public keys, and so do rind and the curve's independent
/// oracle.
macro_rules! ec_crosschecks {
    ($curve:ident, $oid:literal, $ecdh:ident, $fixed_signing:ident, $fixed:ident, $asn1_signing:ident, $asn1:ident, $ours_fixed:ident, $ours_asn1:ident, $hash:ty) => {
        mod $curve {
            use aws_lc_rs::agreement::{self, $ecdh, EphemeralPrivateKey};
            use aws_lc_rs::encoding::{
                AsBigEndian, AsDer, EcPrivateKeyBin, EcPrivateKeyRfc5915Der,
                EcPublicKeyCompressedBin, Pkcs8V1Der, PublicKeyX509Der,
            };
            use aws_lc_rs::rand::SystemRandom;
            use aws_lc_rs::signature::{
                $asn1, $asn1_signing, $fixed, $fixed_signing, EcdsaKeyPair, KeyPair,
                UnparsedPublicKey,
            };
            use proptest::collection::vec;
            use proptest::prelude::*;
            use rind::ecdsa::{self, sign, verify};

            // Each case generates keys on both sides, which is slow under emulation.
            proptest! {
                #![proptest_config(ProptestConfig::with_cases(32))]

                #[test]
                fn ecdsa(message in vec(any::<u8>(), 0..300)) {
                    // aws-lc-rs accepts our key and derives the same public
                    // key, encodings, and scalar.
                    let ours = ecdsa::KeyPair::generate(&sign::$ours_fixed).unwrap();
                    let encoded = ours.public_key();
                    let public = encoded.as_ref();
                    let theirs_from_ours = EcdsaKeyPair::from_pkcs8(
                        &$fixed_signing,
                        ours.to_pkcs8().as_ref(),
                    )
                    .expect("aws-lc-rs rejected a key we generated");
                    prop_assert_eq!(theirs_from_ours.public_key().as_ref(), public);
                    let spki = theirs_from_ours.public_key().as_der().unwrap();
                    let ours_spki = ours.public_key().to_spki();
                    prop_assert_eq!(spki.as_ref(), ours_spki.as_ref());
                    let scalar = theirs_from_ours.private_key().as_be_bytes().unwrap();
                    let ours_scalar = ours.to_scalar();
                    prop_assert_eq!(ours_scalar.as_ref(), scalar.as_ref());

                    // We load its scalar and point as the same key, and refuse
                    // the scalar with another key's point.
                    let reloaded = ecdsa::KeyPair::from_scalar_and_public_key(
                        &sign::$ours_asn1,
                        scalar.as_ref(),
                        public,
                    )
                    .unwrap();
                    let (reloaded_pkcs8, ours_pkcs8) = (reloaded.to_pkcs8(), ours.to_pkcs8());
                    prop_assert_eq!(reloaded_pkcs8.as_ref(), ours_pkcs8.as_ref());
                    let other = EcdsaKeyPair::generate(&$fixed_signing).unwrap();
                    prop_assert!(ecdsa::KeyPair::from_scalar_and_public_key(
                        &sign::$ours_asn1,
                        scalar.as_ref(),
                        other.public_key().as_ref(),
                    )
                    .is_err());

                    // It verifies our signatures, in both encodings.
                    let theirs_verifier = |alg| UnparsedPublicKey::new(alg, public);
                    let signature = ours.sign(&message).unwrap();
                    theirs_verifier(&$fixed).verify(&message, signature.as_ref()).unwrap();
                    let signature = reloaded.sign(&message).unwrap();
                    theirs_verifier(&$asn1).verify(&message, signature.as_ref()).unwrap();

                    // We verify its signatures, in both encodings, and refuse
                    // one over another message.
                    for (signing, ours_verification) in [
                        (&$fixed_signing, &verify::$ours_fixed),
                        (&$asn1_signing, &verify::$ours_asn1),
                    ] {
                        let theirs = EcdsaKeyPair::generate(signing).unwrap();
                        let signature = theirs.sign(&SystemRandom::new(), &message).unwrap();
                        let verifier =
                            ecdsa::PublicKey::new(ours_verification, theirs.public_key().as_ref())
                                .unwrap();
                        verifier.verify(&message, signature.as_ref()).unwrap();
                        prop_assert!(
                            verifier.verify(&[&message[..], b"!"].concat(), signature.as_ref()).is_err()
                        );
                    }
                }

                /// rind and the independent oracle derive the same public
                /// key, verify each other's signatures and refuse them over
                /// another message, agree on the same secret with a peer's
                /// point, uncompressed or compressed, and refuse it with a
                /// bit of its `y` flipped, off the curve.
                #[test]
                fn ec_oracle(message in vec(any::<u8>(), 0..300), flip in any::<prop::sample::Index>()) {
                    use sha2::Digest;
                    let oracle = crate::oracle::$curve();
                    let ours = ecdsa::KeyPair::generate(&sign::$ours_fixed).unwrap();
                    let scalar = ours.to_scalar();
                    let scalar = scalar.as_ref();
                    let public = ours.public_key();
                    let public = public.as_ref();
                    prop_assert_eq!(&crate::oracle::Nist::public_key(&oracle, scalar)[..], public);

                    let digest = <$hash>::digest(&message);
                    let other = <$hash>::digest([&message[..], b"!"].concat());
                    let signature = ours.sign(&message).unwrap();
                    prop_assert!(crate::oracle::Nist::verify(&oracle, public, &digest, signature.as_ref()));
                    prop_assert!(!crate::oracle::Nist::verify(&oracle, public, &other, signature.as_ref()));
                    let theirs = crate::oracle::Nist::sign(&oracle, scalar, &digest);
                    let verifier = ecdsa::PublicKey::new(&verify::$ours_fixed, public).unwrap();
                    prop_assert!(verifier.verify(&message, &theirs).is_ok());
                    prop_assert!(verifier.verify(&[&message[..], b"!"].concat(), &theirs).is_err());

                    let ecdh = &rind::agreement::$ecdh;
                    let ours = rind::agreement::PrivateKey::from_scalar(ecdh, scalar).unwrap();
                    let peer = rind::agreement::PrivateKey::generate(ecdh).unwrap().to_scalar();
                    let peer_public = crate::oracle::Nist::public_key(&oracle, peer.as_ref());
                    let wanted = crate::oracle::Nist::agree(&oracle, peer.as_ref(), public).unwrap();
                    let secret = ours.agree(&peer_public).unwrap();
                    prop_assert_eq!(secret.as_ref(), &wanted[..]);
                    let len = (peer_public.len() - 1) / 2;
                    let mut compressed = peer_public[..1 + len].to_vec();
                    compressed[0] = 2 | (peer_public[2 * len] & 1);
                    let decompressed = rind::agreement::PublicKey::new(ecdh, &compressed).unwrap();
                    prop_assert_eq!(decompressed.as_ref(), &peer_public[..]);
                    prop_assert_eq!(crate::oracle::Nist::agree(&oracle, scalar, &compressed), Some(wanted));

                    let mut off_curve = peer_public.clone();
                    let bit = flip.index(8 * len);
                    off_curve[1 + len + bit / 8] ^= 1 << (bit % 8);
                    prop_assert!(ours.agree(&off_curve).is_err());
                    prop_assert_eq!(crate::oracle::Nist::agree(&oracle, scalar, &off_curve), None);
                }

                #[test]
                fn ecdh(_case in any::<u8>()) {
                    let ours = rind::agreement::PrivateKey::generate(&rind::agreement::$ecdh)
                        .unwrap();
                    let ours_public = ours.public_key();
                    let theirs = EphemeralPrivateKey::generate(&$ecdh, &SystemRandom::new()).unwrap();
                    let theirs_public = theirs.compute_public_key().unwrap();

                    let ours_secret = ours.agree(theirs_public.as_ref()).unwrap();
                    let theirs_secret = agreement::agree_ephemeral(
                        theirs,
                        agreement::UnparsedPublicKey::new(&$ecdh, ours_public.as_ref()),
                        (),
                        |secret| Ok(secret.to_vec()),
                    )
                    .unwrap();
                    prop_assert_eq!(ours_secret.as_ref(), &theirs_secret[..]);
                }

                /// Each side loads the other's stored key, in each encoding
                /// both write, as the same key, which agrees as the original
                /// does, again and again.
                #[test]
                fn ecdh_stored(_case in any::<u8>()) {
                    use rind::agreement::PrivateKey as Ours;

                    let theirs = agreement::PrivateKey::generate(&$ecdh).unwrap();
                    let theirs_public = theirs.compute_public_key().unwrap();
                    let peer = agreement::PrivateKey::generate(&$ecdh).unwrap();
                    let peer_public = peer.compute_public_key().unwrap();
                    let expected = agreement::agree(
                        &theirs,
                        agreement::UnparsedPublicKey::new(&$ecdh, peer_public.as_ref()),
                        (),
                        |secret| Ok(secret.to_vec()),
                    )
                    .unwrap();

                    let ecdh = &rind::agreement::$ecdh;
                    let scalar = AsBigEndian::<EcPrivateKeyBin<'_>>::as_be_bytes(&theirs).unwrap();
                    let pkcs8 = AsDer::<Pkcs8V1Der<'_>>::as_der(&theirs).unwrap();
                    let sec1 = AsDer::<EcPrivateKeyRfc5915Der<'_>>::as_der(&theirs).unwrap();
                    for ours in [
                        Ours::from_scalar(ecdh, scalar.as_ref()).unwrap(),
                        Ours::from_pkcs8(ecdh, pkcs8.as_ref()).unwrap(),
                        Ours::from_sec1(ecdh, sec1.as_ref()).unwrap(),
                    ] {
                        let ours_public = ours.public_key();
                        prop_assert_eq!(ours_public.as_ref(), theirs_public.as_ref());
                        for _ in 0..2 {
                            let secret = ours.agree(peer_public.as_ref()).unwrap();
                            prop_assert_eq!(secret.as_ref(), &expected[..]);
                        }

                        // Ours export as theirs do, and load back into theirs.
                        let (ours_scalar, ours_pkcs8) = (ours.to_scalar(), ours.to_pkcs8());
                        prop_assert_eq!(ours_scalar.as_ref(), scalar.as_ref());
                        prop_assert_eq!(ours_pkcs8.as_ref(), pkcs8.as_ref());
                        for theirs in [
                            agreement::PrivateKey::from_private_key(&$ecdh, ours_scalar.as_ref()),
                            agreement::PrivateKey::from_private_key_der(&$ecdh, ours_pkcs8.as_ref()),
                        ] {
                            let public = theirs.unwrap().compute_public_key().unwrap();
                            prop_assert_eq!(public.as_ref(), theirs_public.as_ref());
                        }

                        // An ECDSA key pair loads it as the same key.
                        let signing = ecdsa::KeyPair::from_pkcs8(&sign::$ours_asn1, ours_pkcs8.as_ref())
                            .unwrap();
                        let signing_public = signing.public_key();
                        prop_assert_eq!(signing_public.as_ref(), theirs_public.as_ref());
                    }
                }

                /// Each side's encodings of a key are the other's: SEC1 and
                /// SPKI, of key pairs, public keys, and agreement keys, and
                /// a compressed point, raw or in SPKI, which both
                /// decompress and agree with alike.
                #[test]
                fn encodings(_case in any::<u8>()) {
                    let theirs = EcdsaKeyPair::generate(&$asn1_signing).unwrap();
                    let pkcs8 = theirs.to_pkcs8v1().unwrap();
                    let ours = ecdsa::KeyPair::from_pkcs8(&sign::$ours_asn1, pkcs8.as_ref())
                        .unwrap();
                    let sec1 = theirs.private_key().as_der().unwrap();
                    let ours_sec1 = ours.to_sec1();
                    prop_assert_eq!(ours_sec1.as_ref(), sec1.as_ref());

                    let public = theirs.public_key();
                    let point = public.as_ref();
                    let spki = AsDer::<PublicKeyX509Der<'_>>::as_der(public).unwrap();
                    let parsed = ecdsa::PublicKey::from_spki(&verify::$ours_asn1, spki.as_ref())
                        .unwrap();
                    prop_assert_eq!(parsed.as_ref(), point);
                    let ours_spki = parsed.to_spki();
                    prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());

                    // RustCrypto, whose DER is its own, reads each of ours
                    // as the same key.
                    {
                        use ::$curve::elliptic_curve::sec1::ToSec1Point;
                        use ::$curve::pkcs8::{DecodePrivateKey, DecodePublicKey};
                        let scalar = ours.to_scalar();
                        let ours_pkcs8 = ours.to_pkcs8();
                        let from_pkcs8 = ::$curve::SecretKey::from_pkcs8_der(ours_pkcs8.as_ref()).unwrap();
                        prop_assert_eq!(&from_pkcs8.to_bytes()[..], scalar.as_ref());
                        let from_sec1 = ::$curve::SecretKey::from_sec1_der(ours_sec1.as_ref()).unwrap();
                        prop_assert_eq!(&from_sec1.to_bytes()[..], scalar.as_ref());
                        let from_spki = ::$curve::PublicKey::from_public_key_der(ours_spki.as_ref()).unwrap();
                        let from_spki = from_spki.to_sec1_point(false);
                        prop_assert_eq!(from_spki.as_bytes(), point);
                    }

                    let ecdh = &rind::agreement::$ecdh;
                    let agreeing = agreement::PrivateKey::generate(&$ecdh).unwrap();
                    let agreeing_public = agreeing.compute_public_key().unwrap();
                    let agreeing_spki = agreeing_public.as_der().unwrap();
                    let parsed = rind::agreement::PublicKey::from_spki(ecdh, agreeing_spki.as_ref())
                        .unwrap();
                    prop_assert_eq!(parsed.as_ref(), agreeing_public.as_ref());
                    let ours_spki = parsed.to_spki();
                    prop_assert_eq!(ours_spki.as_ref(), agreeing_spki.as_ref());

                    let compressed =
                        AsBigEndian::<EcPublicKeyCompressedBin<'_>>::as_be_bytes(public).unwrap();
                    let compressed = compressed.as_ref();
                    let decompressed = rind::agreement::PublicKey::new(ecdh, compressed).unwrap();
                    prop_assert_eq!(decompressed.as_ref(), point);
                    let compressed_spki = crate::der(0x30, &[
                        &crate::der(0x30, &[
                            &crate::der(0x06, &hex::decode("2a8648ce3d0201").unwrap())[..],
                            &crate::der(0x06, &hex::decode($oid).unwrap()),
                        ].concat())[..],
                        &crate::der(0x03, &[&[0][..], compressed].concat()),
                    ].concat());
                    let parsed = ecdsa::PublicKey::from_spki(&verify::$ours_asn1, &compressed_spki)
                        .unwrap();
                    prop_assert_eq!(parsed.as_ref(), point);

                    let ours_agreeing = rind::agreement::PrivateKey::from_scalar(
                        ecdh,
                        AsBigEndian::<EcPrivateKeyBin<'_>>::as_be_bytes(&agreeing).unwrap().as_ref(),
                    )
                    .unwrap();
                    let ours_secret = ours_agreeing.agree(decompressed.as_ref()).unwrap();
                    let theirs_secret = agreement::agree(
                        &agreeing,
                        agreement::UnparsedPublicKey::new(&$ecdh, compressed),
                        (),
                        |secret| Ok(secret.to_vec()),
                    )
                    .unwrap();
                    prop_assert_eq!(ours_secret.as_ref(), &theirs_secret[..]);
                }

                /// A key pair's public key loads compressed, as aws-lc-rs
                /// takes it, but only with its own `y` parity. A hybrid point
                /// is refused, though aws-lc-rs takes it.
                #[test]
                fn public_key_forms(_case in any::<u8>()) {
                    let key = EcdsaKeyPair::generate(&$asn1_signing).unwrap();
                    let scalar = key.private_key().as_be_bytes().unwrap();
                    let scalar = scalar.as_ref();
                    let public = key.public_key();
                    let point = public.as_ref();
                    let (x, y) = point[1..].split_at(point.len() / 2);
                    let parity = y[y.len() - 1] & 1;

                    for (encoded, ours_takes, theirs_takes) in [
                        ([&[0x02 | parity][..], x].concat(), true, true),
                        ([&[0x03 ^ parity][..], x].concat(), false, false),
                        ([&[0x06 | parity][..], x, y].concat(), false, true),
                    ] {
                        let sec1 = crate::der(0x30, &[
                            &[0x02, 0x01, 0x01][..],
                            &crate::der(0x04, scalar),
                            &crate::der(0xa0, &crate::der(0x06, &hex::decode($oid).unwrap())),
                            &crate::der(0xa1, &crate::der(0x03, &[&[0][..], &encoded].concat())),
                        ].concat());
                        let pkcs8 = crate::der(0x30, &[
                            &[0x02, 0x01, 0x00][..],
                            &crate::der(0x30, &[
                                &crate::der(0x06, &hex::decode("2a8648ce3d0201").unwrap())[..],
                                &crate::der(0x06, &hex::decode($oid).unwrap()),
                            ].concat()),
                            &crate::der(0x04, &sec1),
                        ].concat());

                        let ours = [
                            ecdsa::KeyPair::from_scalar_and_public_key(
                                &sign::$ours_asn1, scalar, &encoded,
                            ),
                            ecdsa::KeyPair::from_sec1(&sign::$ours_asn1, &sec1),
                            ecdsa::KeyPair::from_pkcs8(&sign::$ours_asn1, &pkcs8),
                        ];
                        for ours in ours {
                            prop_assert_eq!(ours.is_ok(), ours_takes, "{:02x?}", encoded);
                            if let Ok(ours) = ours {
                                let ours = ours.public_key();
                                prop_assert_eq!(ours.as_ref(), point);
                            }
                        }
                        let ecdh = &rind::agreement::$ecdh;
                        for ours in [
                            rind::agreement::PrivateKey::from_sec1(ecdh, &sec1),
                            rind::agreement::PrivateKey::from_pkcs8(ecdh, &pkcs8),
                        ] {
                            prop_assert_eq!(ours.is_ok(), ours_takes, "{:02x?}", encoded);
                            if let Ok(ours) = ours {
                                let ours = ours.public_key();
                                prop_assert_eq!(ours.as_ref(), point);
                            }
                        }
                        let theirs = [
                            EcdsaKeyPair::from_private_key_and_public_key(
                                &$asn1_signing, scalar, &encoded,
                            ),
                            EcdsaKeyPair::from_private_key_der(&$asn1_signing, &sec1),
                            EcdsaKeyPair::from_pkcs8(&$asn1_signing, &pkcs8),
                        ];
                        for theirs in theirs {
                            prop_assert_eq!(theirs.is_ok(), theirs_takes, "{:02x?}", encoded);
                        }
                    }
                }
            }
        }
    };
}

ec_crosschecks!(
    p256,
    "2a8648ce3d030107",
    ECDH_P256,
    ECDSA_P256_SHA256_FIXED_SIGNING,
    ECDSA_P256_SHA256_FIXED,
    ECDSA_P256_SHA256_ASN1_SIGNING,
    ECDSA_P256_SHA256_ASN1,
    P256_SHA256_FIXED,
    P256_SHA256_ASN1,
    sha2::Sha256
);

ec_crosschecks!(
    p384,
    "2b81040022",
    ECDH_P384,
    ECDSA_P384_SHA384_FIXED_SIGNING,
    ECDSA_P384_SHA384_FIXED,
    ECDSA_P384_SHA384_ASN1_SIGNING,
    ECDSA_P384_SHA384_ASN1,
    P384_SHA384_FIXED,
    P384_SHA384_ASN1,
    sha2::Sha384
);

ec_crosschecks!(
    p521,
    "2b81040023",
    ECDH_P521,
    ECDSA_P521_SHA512_FIXED_SIGNING,
    ECDSA_P521_SHA512_FIXED,
    ECDSA_P521_SHA512_ASN1_SIGNING,
    ECDSA_P521_SHA512_ASN1,
    P521_SHA512_FIXED,
    P521_SHA512_ASN1,
    sha2::Sha512
);

mod ed25519 {
    use aws_lc_rs::encoding::{AsBigEndian, AsDer};
    use aws_lc_rs::signature::{ED25519, Ed25519KeyPair, KeyPair, UnparsedPublicKey};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use proptest::sample::Index;
    use rind::ed25519 as ours;

    proptest! {
        #[test]
        fn sign_verify(
            seed in any::<[u8; 32]>(),
            message in vec(any::<u8>(), 0..300),
            flip in any::<Option<Index>>(),
        ) {
            // Signing is deterministic, so one seed gives both sides the same
            // public key, encodings, seed, and signatures; loading ours checks
            // the public key matches theirs.
            let theirs = Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
            let public = theirs.public_key().as_ref();
            let seed_public: [u8; 32] = public.try_into().unwrap();
            let ours = ours::KeyPair::from_seed_and_public_key(&seed, public).unwrap();
            let spki = theirs.public_key().as_der().unwrap();
            let ours_spki = ours.public_key().to_spki();
            prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());
            let (ours_pkcs8, theirs_pkcs8) = (ours.to_pkcs8(), theirs.to_pkcs8().unwrap());
            prop_assert_eq!(ours_pkcs8.as_ref(), theirs_pkcs8.as_ref());
            let ours_seed = ours.to_seed();
            let theirs_seed = theirs.seed().unwrap().as_be_bytes().unwrap();
            prop_assert_eq!(ours_seed.as_ref(), theirs_seed.as_ref());
            let signature = ours.sign(&message);
            let theirs_signature = theirs.sign(&message);
            prop_assert_eq!(signature.as_ref(), theirs_signature.as_ref());
            prop_assert_eq!(&crate::oracle::ed25519::public_key(&seed), public);
            prop_assert_eq!(&crate::oracle::ed25519::sign(&seed, &message)[..], signature.as_ref());

            // All three verify it, and refuse it with any one bit flipped.
            let mut signature = signature.as_ref().to_vec();
            if let Some(flip) = flip {
                let bit = flip.index(signature.len() * 8);
                signature[bit / 8] ^= 1 << (bit % 8);
            }
            let ours_result = ours::PublicKey::new(public)
                .unwrap()
                .verify(&message, &signature);
            let theirs_result = UnparsedPublicKey::new(&ED25519, public).verify(&message, &signature);
            prop_assert_eq!(ours_result.is_ok(), flip.is_none());
            prop_assert_eq!(theirs_result.is_ok(), flip.is_none());
            prop_assert_eq!(crate::oracle::ed25519::verify(&seed_public, &message, &signature), flip.is_none());
        }

        /// Both load a seed alone, and encode it as the same PKCS#8 v1, and
        /// the public key as the same SPKI, which each parses.
        #[test]
        fn seed_alone(seed in any::<[u8; 32]>()) {
            let theirs = Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
            let ours = ours::KeyPair::from_seed(&seed).unwrap();
            let public = ours.public_key();
            prop_assert_eq!(public.as_ref(), theirs.public_key().as_ref());
            let (ours_v1, theirs_v1) = (ours.to_pkcs8v1(), theirs.to_pkcs8v1().unwrap());
            prop_assert_eq!(ours_v1.as_ref(), theirs_v1.as_ref());
            Ed25519KeyPair::from_pkcs8(ours_v1.as_ref()).unwrap();
            // RFC 8410 wraps the seed in an OCTET STRING of its own.
            let wrapped = [&[0x04, 0x20][..], &seed].concat();
            prop_assert_eq!(crate::rustcrypto_pkcs8(ours_v1.as_ref()), ("1.3.101.112".into(), wrapped));

            let spki = theirs.public_key().as_der().unwrap();
            let parsed = ours::PublicKey::from_spki(spki.as_ref())
                .unwrap();
            prop_assert_eq!(parsed.as_ref(), public.as_ref());
            let ours_spki = parsed.to_spki();
            prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());
            let wanted = ("1.3.101.112".into(), public.as_ref().to_vec());
            prop_assert_eq!(crate::rustcrypto_spki(ours_spki.as_ref()), wanted);
        }

        #[test]
        fn seed_and_public_key(seed in any::<[u8; 32]>(), other in any::<[u8; 32]>()) {
            // Both load a seed with its public key, and refuse it with another's.
            let public = Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
            let public = public.public_key().as_ref();
            let wrong = Ed25519KeyPair::from_seed_unchecked(&other).unwrap();
            let wrong = wrong.public_key().as_ref();

            ours::KeyPair::from_seed_and_public_key(&seed, public).unwrap();
            Ed25519KeyPair::from_seed_and_public_key(&seed, public).unwrap();
            prop_assert_eq!(
                ours::KeyPair::from_seed_and_public_key(&seed, wrong).is_ok(),
                seed == other
            );
            prop_assert_eq!(
                Ed25519KeyPair::from_seed_and_public_key(&seed, wrong).is_ok(),
                seed == other
            );
        }
    }

    /// libsodium's small-order encodings: each `y` of a small-order point
    /// that fits in 255 bits, with either sign.
    fn small_order() -> impl Iterator<Item = [u8; 32]> {
        [
            "0000000000000000000000000000000000000000000000000000000000000000",
            "0100000000000000000000000000000000000000000000000000000000000000",
            "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05",
            "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a",
            "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
            "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
            "eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        ]
        .into_iter()
        .flat_map(|y| {
            let y: [u8; 32] = hex::decode(y).unwrap().try_into().unwrap();
            [y, {
                let mut negative = y;
                negative[31] |= 0x80;
                negative
            }]
        })
    }

    #[test]
    fn small_order_public_keys() {
        // aws-lc-rs verifies a signature nobody made on each small-order point,
        // `S = 0` with `R = -[k]A`, itself of small order; rind refuses every
        // encoding. With the identity as `A`, `R` is the identity for any
        // message.
        let identity = small_order().nth(2).unwrap();
        let forged = [&identity[..], &[0; 32]].concat();
        UnparsedPublicKey::new(&ED25519, identity)
            .verify(b"any message", &forged)
            .unwrap();

        // `k` depends on `R`, so search the small-order points for one that
        // is `-[k]A`, which each is with odds of one in `A`'s order.
        let points: Vec<_> = small_order().collect();
        for public in small_order() {
            assert_eq!(
                ours::PublicKey::new(&public).unwrap_err().to_string(),
                "a key was rejected: a small-order point"
            );
            let theirs = UnparsedPublicKey::new(&ED25519, public);
            let forged = (0u8..=255).any(|message| {
                points.iter().any(|r| {
                    let forged = [&r[..], &[0; 32]].concat();
                    theirs.verify(&[message], &forged).is_ok()
                })
            });
            // aws-lc-rs verifies nothing on a non-canonical encoding, a sign on
            // `x = 0` or a `y` of `p` or `p + 1`, so the two differ on the eight
            // points alone.
            let canonical = !matches!(
                (public[0], public[31]),
                (0x01 | 0xec, 0x80..) | (0xed | 0xee, _)
            );
            assert_eq!(forged, canonical, "{public:x?}");
        }
    }
}

/// PKCS#8's optional attributes: both sides skip them, uninterpreted, and
/// refuse the same malformed ones, on every key type.
mod pkcs8_attributes {
    use aws_lc_rs::rsa::KeyPair as TheirsRsaKeyPair;
    use aws_lc_rs::signature::{self as theirs, KeyPair as _};
    use rind::{ecdsa, ed25519, rsa};

    /// A PKCS#8 document, and each side's loader for its key type, which
    /// gives the public key.
    struct Key {
        pkcs8: Vec<u8>,
        /// Whether the document is v2, ending in a public key.
        v2: bool,
        ours: fn(&[u8]) -> Option<Vec<u8>>,
        theirs: fn(&[u8]) -> Option<Vec<u8>>,
    }

    macro_rules! ecdsa {
        ($ours:ident, $theirs:ident) => {
            Key {
                pkcs8: ecdsa::KeyPair::generate(&ecdsa::sign::$ours)
                    .unwrap()
                    .to_pkcs8()
                    .as_ref()
                    .to_vec(),
                v2: false,
                ours: |der| {
                    let key = ecdsa::KeyPair::from_pkcs8(&ecdsa::sign::$ours, der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
                theirs: |der| {
                    let key = theirs::EcdsaKeyPair::from_pkcs8(&theirs::$theirs, der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
            }
        };
    }

    fn keys() -> [Key; 5] {
        [
            ecdsa!(P256_SHA256_ASN1, ECDSA_P256_SHA256_ASN1_SIGNING),
            ecdsa!(P384_SHA384_ASN1, ECDSA_P384_SHA384_ASN1_SIGNING),
            ecdsa!(P521_SHA512_ASN1, ECDSA_P521_SHA512_ASN1_SIGNING),
            Key {
                pkcs8: include_bytes!("../src/high/rsa/rsa2056.pkcs8.der").to_vec(),
                v2: false,
                ours: |der| {
                    let key = rsa::KeyPair::from_pkcs8(der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
                theirs: |der| {
                    let key = TheirsRsaKeyPair::from_pkcs8(der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
            },
            Key {
                pkcs8: ed25519::KeyPair::generate()
                    .unwrap()
                    .to_pkcs8()
                    .as_ref()
                    .to_vec(),
                v2: true,
                ours: |der| {
                    let key = ed25519::KeyPair::from_pkcs8(der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
                theirs: |der| {
                    let key = theirs::Ed25519KeyPair::from_pkcs8(der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
            },
        ]
    }

    /// The header and body lengths of the DER element starting `der`.
    fn element(der: &[u8]) -> (usize, usize) {
        match der[1] {
            len @ 0..=0x7f => (2, usize::from(len)),
            0x81 => (3, usize::from(der[2])),
            0x82 => (4, usize::from(u16::from_be_bytes([der[2], der[3]]))),
            _ => unreachable!("no test document is that long"),
        }
    }

    /// `pkcs8` with `fields` inserted after its first `after` fields.
    fn insert(pkcs8: &[u8], after: usize, fields: &[u8]) -> Vec<u8> {
        let (header, len) = element(pkcs8);
        let mut body = pkcs8[header..header + len].to_vec();
        let mut at = 0;
        for _ in 0..after {
            let (header, len) = element(&body[at..]);
            at += header + len;
        }
        body.splice(at..at, fields.iter().copied());

        let header = match body.len() {
            len @ 0..=0x7f => vec![0x30, len as u8],
            len @ 0x80..=0xff => vec![0x30, 0x81, len as u8],
            len => [
                &[0x30, 0x82][..],
                &u16::try_from(len).unwrap().to_be_bytes(),
            ]
            .concat(),
        };
        [header, body].concat()
    }

    /// Both sides refuse an ECDSA or RSA v2 document with its public key, which
    /// would go unchecked. Ed25519 checks it.
    #[test]
    fn ecdsa_and_rsa_refuse_v2() {
        for key in keys() {
            let public = (key.ours)(&key.pkcs8).unwrap();
            let v2 = match key.v2 {
                true => key.pkcs8.clone(),
                false => {
                    let field = crate::der(0x81, &[&[0][..], &public].concat());
                    let mut v2 = insert(&key.pkcs8, 3, &field);
                    let (header, _) = element(&v2);
                    assert_eq!(v2[header..header + 3], [0x02, 0x01, 0x00]);
                    v2[header + 2] = 0x01;
                    v2
                }
            };
            let expected = key.v2.then_some(&public[..]);
            assert_eq!((key.ours)(&v2).as_deref(), expected, "{v2:02x?}");
            assert_eq!((key.theirs)(&v2).as_deref(), expected, "{v2:02x?}");
        }
    }

    /// `pkcs8`, a v1 document, as version 2 without a public key.
    fn as_v2(pkcs8: &[u8]) -> Vec<u8> {
        let mut v2 = pkcs8.to_vec();
        let (header, _) = element(&v2);
        assert_eq!(v2[header..header + 3], [0x02, 0x01, 0x00]);
        v2[header + 2] = 0x01;
        v2
    }

    /// RFC 5958 makes a v2 document's public key optional, and both sides
    /// take one without it, for every key type.
    #[test]
    fn v2_without_public_key() {
        use aws_lc_rs::signature::{ML_DSA_44_SIGNING, PqdsaKeyPair};
        use rind::ml_dsa::{KeyPair as MlDsaKeyPair, MlDsa44};

        for key in keys() {
            let v1 = match key.v2 {
                // Drop the Ed25519 document's trailing 32-byte public key.
                true => {
                    let mut body = key.pkcs8[2..key.pkcs8.len() - 35].to_vec();
                    body[2] = 0x00;
                    [&[0x30, body.len() as u8][..], &body].concat()
                }
                false => key.pkcs8.clone(),
            };
            let public = (key.ours)(&v1).unwrap();
            let v2 = as_v2(&v1);
            assert_eq!((key.ours)(&v2).as_deref(), Some(&public[..]), "{v2:02x?}");
            assert_eq!((key.theirs)(&v2).as_deref(), Some(&public[..]), "{v2:02x?}");
        }

        let ours = MlDsaKeyPair::<MlDsa44>::from_seed(&[7; 32]).unwrap();
        let v2 = as_v2(ours.to_pkcs8().as_ref());
        let theirs = PqdsaKeyPair::from_pkcs8(&ML_DSA_44_SIGNING, &v2).unwrap();
        let ours = MlDsaKeyPair::<MlDsa44>::from_pkcs8(&v2).unwrap();
        assert_eq!(ours.public_key().as_ref(), theirs.public_key().as_ref());

        let private = [9; 32];
        let ours =
            rind::agreement::PrivateKey::from_scalar(&rind::agreement::X25519, &private).unwrap();
        let v2 = as_v2(ours.to_pkcs8().as_ref());
        assert_eq!(crate::ecdh_scalars::aws_lc_x25519_from_pkcs8(&v2), private);
        let loaded =
            rind::agreement::PrivateKey::from_pkcs8(&rind::agreement::X25519, &v2).unwrap();
        assert_eq!(loaded.public_key().as_ref(), ours.public_key().as_ref());
    }

    #[test]
    fn attributes() {
        // RFC 8410's example, and contents that are not DER at all.
        let rfc_8410 =
            hex::decode("a01f301d060a2a864886f70d01090914310f0c0d437572646c6520436861697273")
                .unwrap();
        let skipped: [&[u8]; 3] = [&[0xa0, 0x00], &rfc_8410, &[0xa0, 0x03, 0xff, 0xff, 0xff]];
        let refused: [&[u8]; 5] = [
            &[0xa0, 0x7f, 0x31, 0x00], // truncated
            &[0x80, 0x00],             // primitive
            &[0xa2, 0x00],             // another tag
            &[0xa0, 0x00, 0x05, 0x00], // trailing garbage
            &[0xa0, 0x00, 0xa0, 0x00], // twice
        ];

        for key in keys() {
            let plain = (key.ours)(&key.pkcs8).unwrap();
            let check = |pkcs8: &[u8], expected: Option<&[u8]>| {
                let (ours, theirs) = ((key.ours)(pkcs8), (key.theirs)(pkcs8));
                assert_eq!(ours.as_deref(), expected, "{pkcs8:02x?}");
                assert_eq!(theirs.as_deref(), expected, "{pkcs8:02x?}");
            };

            // After the version, algorithm, and private key.
            for fields in skipped {
                check(&insert(&key.pkcs8, 3, fields), Some(&plain));
            }
            for fields in refused {
                check(&insert(&key.pkcs8, 3, fields), None);
            }
            // Following a v2 document's public key, out of order.
            if key.v2 {
                check(&insert(&key.pkcs8, 4, &[0xa0, 0x00]), None);
            }
        }
    }
}

mod ecdh_scalars {
    use aws_lc_rs::agreement::{self, ECDH_P256, PrivateKey, UnparsedPublicKey, X25519};
    use aws_lc_rs::encoding::{AsBigEndian, AsDer, Curve25519SeedBin};
    use proptest::prelude::*;
    use rind::agreement as ours;

    /// n - 1, the largest P-256 private key.
    const N_MINUS_1: [u8; 32] = [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63,
        0x25, 0x50,
    ];

    /// (n - 1) / 2, the largest scalar `p256_scalarmul` leaves unnegated.
    const HALF_N: [u8; 32] = [
        0x7f, 0xff, 0xff, 0xff, 0x80, 0x00, 0x00, 0x00, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xde, 0x73, 0x7d, 0x56, 0xd3, 0x8b, 0xcf, 0x42, 0x79, 0xdc, 0xe5, 0x61, 0x7e, 0x31,
        0x92, 0xa8,
    ];

    /// `x + d`, for a last byte that neither carries nor borrows.
    fn add_small(mut x: [u8; 32], d: i8) -> [u8; 32] {
        x[31] = x[31].checked_add_signed(d).unwrap();
        x
    }

    /// A P-256 private key, biased to 1, n - 1, and either side of n / 2,
    /// where the scalar multiplication negates it.
    fn p256_scalar() -> impl Strategy<Value = [u8; 32]> {
        let small = |k| add_small([0; 32], k);
        prop_oneof![
            // Below n, as its first byte is.
            4 => any::<[u8; 32]>().prop_map(|mut k| {
                k[0] %= 0xff;
                k
            }),
            1 => prop_oneof![
                Just(small(1)),
                Just(small(2)),
                Just(add_small(N_MINUS_1, -1)),
                Just(N_MINUS_1),
                Just(HALF_N),
                Just(add_small(HALF_N, 1)),
            ],
        ]
    }

    // Any 32 bytes is a private key or a peer's u-coordinate, including
    // coordinates at or above the field prime. The fixed peers have small
    // order, which both sides refuse for the all-zero secret they give.
    fn x25519_peer() -> impl Strategy<Value = [u8; 32]> {
        let mut one = [0u8; 32];
        one[0] = 1;
        prop_oneof![
            8 => any::<[u8; 32]>(),
            1 => Just([0u8; 32]),
            1 => Just(one),
        ]
    }

    /// Both sides load `private` and agree with `peer`, which is an encoded
    /// public key for `ecdh`; both refuse it, or give the same secret.
    fn check(
        ours_alg: &'static ours::Algorithm,
        theirs_alg: &'static agreement::Algorithm,
        private: &[u8],
        peer: &[u8],
    ) -> Result<(), TestCaseError> {
        let ours = ours::PrivateKey::from_scalar(ours_alg, private).unwrap();
        let theirs = PrivateKey::from_private_key(theirs_alg, private).unwrap();
        let theirs_public = theirs.compute_public_key().unwrap();
        let ours_public = ours.public_key();
        prop_assert_eq!(ours_public.as_ref(), theirs_public.as_ref());

        let ours_secret = ours.agree(peer).map(|secret| secret.as_ref().to_vec());
        let theirs_secret = agreement::agree(
            &theirs,
            UnparsedPublicKey::new(theirs_alg, peer),
            (),
            |secret| Ok(secret.to_vec()),
        );
        match (ours_secret, theirs_secret) {
            (Ok(ours), Ok(theirs)) => prop_assert_eq!(ours, theirs),
            (Err(_), Err(())) => {}
            (ours, theirs) => prop_assert!(
                false,
                "rind gave {:?}, aws-lc-rs {:?}",
                ours.err(),
                theirs.err()
            ),
        }
        Ok(())
    }

    proptest! {
        #[test]
        fn p256(private in p256_scalar(), peer_scalar in p256_scalar()) {
            let peer = PrivateKey::from_private_key(&ECDH_P256, &peer_scalar)
                .unwrap()
                .compute_public_key()
                .unwrap();
            check(&ours::ECDH_P256, &ECDH_P256, &private, peer.as_ref())?;

            // The independent oracle agrees on the edge-case scalars too.
            use crate::oracle::Nist;
            let oracle = crate::oracle::p256();
            let ours = ours::PrivateKey::from_scalar(&ours::ECDH_P256, &private).unwrap();
            let public = ours.public_key();
            prop_assert_eq!(&oracle.public_key(&private)[..], public.as_ref());
            let secret = ours.agree(&oracle.public_key(&peer_scalar)).unwrap();
            prop_assert_eq!(Some(secret.as_ref().to_vec()), oracle.agree(&peer_scalar, public.as_ref()));
        }

        #[test]
        fn x25519(private in any::<[u8; 32]>(), peer in x25519_peer()) {
            check(&ours::X25519, &X25519, &private, &peer)?;

            // libcrux's X25519, HACL*'s, which rind runs nowhere, derives the
            // same public key, and refuses the same peers or agrees alike.
            let key = ours::PrivateKey::from_scalar(&ours::X25519, &private).unwrap();
            let mut public = [0u8; 32];
            libcrux_curve25519::secret_to_public(&mut public, &private);
            prop_assert_eq!(key.public_key().as_ref(), &public[..]);
            let mut secret = [0u8; 32];
            let independent = libcrux_curve25519::ecdh(&mut secret, &peer, &private).map(|()| secret);
            let ours_secret = key.agree(&peer).map(|secret| <[u8; 32]>::try_from(secret.as_ref()).unwrap());
            prop_assert_eq!(ours_secret.ok(), independent.ok());

            // Both encode the public key as the same SPKI, which ours parses.
            let theirs = PrivateKey::from_private_key(&X25519, &private).unwrap();
            let theirs_public = theirs.compute_public_key().unwrap();
            let spki = theirs_public.as_der().unwrap();
            let parsed = ours::PublicKey::from_spki(&ours::X25519, spki.as_ref()).unwrap();
            prop_assert_eq!(parsed.as_ref(), theirs_public.as_ref());
            let ours_spki = parsed.to_spki();
            prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());
            let wanted = ("1.3.101.110".into(), theirs_public.as_ref().to_vec());
            prop_assert_eq!(crate::rustcrypto_spki(ours_spki.as_ref()), wanted);

            // Both keep the 32 bytes as given, unclamped.
            let theirs = PrivateKey::from_private_key(&X25519, &private).unwrap();
            let theirs = AsBigEndian::<Curve25519SeedBin<'_>>::as_be_bytes(&theirs).unwrap();
            let ours = ours::PrivateKey::from_scalar(&ours::X25519, &private)
                .unwrap()
                .to_scalar();
            prop_assert_eq!(ours.as_ref(), theirs.as_ref());
        }

        /// aws-lc-rs's agreement API has no X25519 PKCS#8, so this checks
        /// ours against aws-lc's `EVP` encoding of the same key, each way.
        #[test]
        fn x25519_pkcs8(private in any::<[u8; 32]>()) {
            let ours = ours::PrivateKey::from_scalar(&ours::X25519, &private).unwrap();
            let ours_pkcs8 = ours.to_pkcs8();
            let theirs_pkcs8 = aws_lc_x25519_pkcs8(&private);
            prop_assert_eq!(ours_pkcs8.as_ref(), &theirs_pkcs8[..]);
            let wrapped = [&[0x04, 0x20][..], &private].concat();
            prop_assert_eq!(crate::rustcrypto_pkcs8(ours_pkcs8.as_ref()), ("1.3.101.110".into(), wrapped));
            let loaded = ours::PrivateKey::from_pkcs8(&ours::X25519, &theirs_pkcs8).unwrap();
            let (loaded, ours) = (loaded.public_key(), ours.public_key());
            prop_assert_eq!(loaded.as_ref(), ours.as_ref());
            prop_assert_eq!(aws_lc_x25519_from_pkcs8(ours_pkcs8.as_ref()), private);
        }
    }

    /// aws-lc's PKCS#8 encoding of the X25519 key `private`.
    fn aws_lc_x25519_pkcs8(private: &[u8; 32]) -> Vec<u8> {
        use aws_lc_sys::*;
        // SAFETY: each pointer and length describes a live buffer, and each
        // allocation is freed once, after its last use.
        unsafe {
            let key = EVP_PKEY_new_raw_private_key(
                EVP_PKEY_X25519,
                core::ptr::null_mut(),
                private.as_ptr(),
                private.len(),
            );
            assert!(!key.is_null());
            let mut cbb = core::mem::zeroed::<CBB>();
            assert_eq!(CBB_init(&mut cbb, 64), 1);
            assert_eq!(EVP_marshal_private_key(&mut cbb, key), 1);
            let (mut out, mut len) = (core::ptr::null_mut(), 0);
            assert_eq!(CBB_finish(&mut cbb, &mut out, &mut len), 1);
            let der = core::slice::from_raw_parts(out, len).to_vec();
            OPENSSL_free(out.cast());
            EVP_PKEY_free(key);
            der
        }
    }

    /// The X25519 key aws-lc parses from PKCS#8 `der`.
    pub(crate) fn aws_lc_x25519_from_pkcs8(der: &[u8]) -> [u8; 32] {
        use aws_lc_sys::*;
        // SAFETY: as `aws_lc_x25519_pkcs8`.
        unsafe {
            let mut cbs = core::mem::zeroed::<CBS>();
            CBS_init(&mut cbs, der.as_ptr(), der.len());
            let key = EVP_parse_private_key(&mut cbs);
            assert!(!key.is_null());
            assert_eq!(EVP_PKEY_id(key), EVP_PKEY_X25519);
            let mut private = [0u8; 32];
            let mut len = private.len();
            assert_eq!(
                EVP_PKEY_get_raw_private_key(key, private.as_mut_ptr(), &mut len),
                1
            );
            EVP_PKEY_free(key);
            assert_eq!(len, 32);
            private
        }
    }
}

/// ECDSA over a digest: aws-lc-rs verifies what rind signs over each curve,
/// hash, and encoding it has an algorithm for, and rind verifies what
/// aws-lc-rs signs over a digest, with an algorithm whose hash is not the
/// digest's, since the digest names its hash.
mod ecdsa_digest {
    use aws_lc_rs::digest as theirs_digest;
    use aws_lc_rs::rand::SystemRandom;
    use aws_lc_rs::signature::{self as theirs, KeyPair, UnparsedPublicKey};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::digest::{self, SHA256, SHA384, SHA512};
    use rind::ecdsa::{self, sign, verify};

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(8))]

        #[test]
        fn theirs_verify_ours(message in vec(any::<u8>(), 0..300)) {
            type Oracle = Option<fn() -> Box<dyn crate::oracle::Nist>>;
            let p256: Oracle = Some(|| Box::new(crate::oracle::p256()));
            let p384: Oracle = Some(|| Box::new(crate::oracle::p384()));
            let p521: Oracle = Some(|| Box::new(crate::oracle::p521()));
            let cases: [(_, _, &'static theirs::EcdsaVerificationAlgorithm, Oracle); 14] = [
                (&sign::P256_SHA256_ASN1, &SHA256, &theirs::ECDSA_P256_SHA256_ASN1, None),
                (&sign::P256_SHA256_ASN1, &SHA384, &theirs::ECDSA_P256_SHA384_ASN1, None),
                (&sign::P256_SHA256_ASN1, &SHA512, &theirs::ECDSA_P256_SHA512_ASN1, None),
                (&sign::P256_SHA256_FIXED, &SHA256, &theirs::ECDSA_P256_SHA256_FIXED, p256),
                (&sign::P384_SHA384_ASN1, &SHA256, &theirs::ECDSA_P384_SHA256_ASN1, None),
                (&sign::P384_SHA384_ASN1, &SHA384, &theirs::ECDSA_P384_SHA384_ASN1, None),
                (&sign::P384_SHA384_ASN1, &SHA512, &theirs::ECDSA_P384_SHA512_ASN1, None),
                (&sign::P384_SHA384_FIXED, &SHA384, &theirs::ECDSA_P384_SHA384_FIXED, p384),
                (&sign::P521_SHA512_ASN1, &SHA256, &theirs::ECDSA_P521_SHA256_ASN1, None),
                (&sign::P521_SHA512_ASN1, &SHA384, &theirs::ECDSA_P521_SHA384_ASN1, None),
                (&sign::P521_SHA512_ASN1, &SHA512, &theirs::ECDSA_P521_SHA512_ASN1, None),
                (&sign::P521_SHA512_FIXED, &SHA256, &theirs::ECDSA_P521_SHA256_FIXED, p521),
                (&sign::P521_SHA512_FIXED, &SHA384, &theirs::ECDSA_P521_SHA384_FIXED, p521),
                (&sign::P521_SHA512_FIXED, &SHA512, &theirs::ECDSA_P521_SHA512_FIXED, p521),
            ];
            for (signing, hash, theirs, oracle) in cases {
                let ours = ecdsa::KeyPair::generate(signing).unwrap();
                let digest = digest::digest(hash, &message);
                let signature = ours.sign_digest(&digest).unwrap();
                let public_key = ours.public_key();
                let verifier = UnparsedPublicKey::new(theirs, public_key.as_ref());
                prop_assert!(
                    verifier.verify(&message, signature.as_ref()).is_ok(),
                    "{:?} {:?}", signing, hash
                );
                prop_assert!(verifier.verify(b"other", signature.as_ref()).is_err());

                // The independent oracle takes fixed-width signatures.
                if let Some(oracle) = oracle.map(|oracle| oracle()) {
                    prop_assert!(oracle.verify(public_key.as_ref(), digest.as_ref(), signature.as_ref()));
                    let other = digest::digest(hash, b"other");
                    prop_assert!(!oracle.verify(public_key.as_ref(), other.as_ref(), signature.as_ref()));
                }
            }
        }

        #[test]
        fn ours_verify_theirs(message in vec(any::<u8>(), 0..300)) {
            let cases: [(&'static theirs::EcdsaSigningAlgorithm, _, _, _); 10] = [
                (&theirs::ECDSA_P256_SHA256_ASN1_SIGNING, &theirs_digest::SHA256, &SHA256, &verify::P256_SHA256_ASN1),
                (&theirs::ECDSA_P256_SHA256_FIXED_SIGNING, &theirs_digest::SHA256, &SHA256, &verify::P256_SHA256_FIXED),
                (&theirs::ECDSA_P384_SHA384_ASN1_SIGNING, &theirs_digest::SHA384, &SHA384, &verify::P384_SHA384_ASN1),
                (&theirs::ECDSA_P384_SHA384_FIXED_SIGNING, &theirs_digest::SHA384, &SHA384, &verify::P384_SHA384_FIXED),
                (&theirs::ECDSA_P521_SHA256_ASN1_SIGNING, &theirs_digest::SHA256, &SHA256, &verify::P521_SHA512_ASN1),
                (&theirs::ECDSA_P521_SHA256_FIXED_SIGNING, &theirs_digest::SHA256, &SHA256, &verify::P521_SHA512_FIXED),
                (&theirs::ECDSA_P521_SHA384_ASN1_SIGNING, &theirs_digest::SHA384, &SHA384, &verify::P521_SHA512_ASN1),
                (&theirs::ECDSA_P521_SHA384_FIXED_SIGNING, &theirs_digest::SHA384, &SHA384, &verify::P521_SHA512_FIXED),
                (&theirs::ECDSA_P521_SHA512_ASN1_SIGNING, &theirs_digest::SHA512, &SHA512, &verify::P521_SHA512_ASN1),
                (&theirs::ECDSA_P521_SHA512_FIXED_SIGNING, &theirs_digest::SHA512, &SHA512, &verify::P521_SHA512_FIXED),
            ];
            for (signing, theirs_hash, ours_hash, verification) in cases {
                let theirs = theirs::EcdsaKeyPair::generate(signing).unwrap();
                let signature = theirs
                    .sign_digest(&theirs_digest::digest(theirs_hash, &message))
                    .unwrap();
                // A signature over the message is one over its digest too.
                let over_message = theirs.sign(&SystemRandom::new(), &message).unwrap();
                let verifier =
                    ecdsa::PublicKey::new(verification, theirs.public_key().as_ref()).unwrap();
                let digest = digest::digest(ours_hash, &message);
                for signature in [signature.as_ref(), over_message.as_ref()] {
                    prop_assert!(
                        verifier.verify_digest(&digest, signature).is_ok(),
                        "{:?}", signing
                    );
                    let other = digest::digest(ours_hash, b"other");
                    prop_assert!(verifier.verify_digest(&other, signature).is_err());
                }
            }
        }
    }
}
