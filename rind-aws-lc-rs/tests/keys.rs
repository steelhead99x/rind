//! rind-aws-lc-rs's keys checked against aws-lc-rs's: each loads the other's
//! encodings, verifies the other's signatures, and agrees on the same
//! secrets.

use std::sync::OnceLock;

use aws_lc_rs as theirs;
use ours::encoding::{AsBigEndian as _, AsDer as _};
use ours::signature::KeyPair as _;
use proptest::collection::vec;
use proptest::prelude::*;
use rind_aws_lc_rs as ours;
use theirs::encoding::{AsBigEndian as _, AsDer as _};
use theirs::signature::KeyPair as _;

macro_rules! agreement_algorithms {
    ($c:ident) => {
        [
            &$c::agreement::X25519,
            &$c::agreement::ECDH_P256,
            &$c::agreement::ECDH_P384,
            &$c::agreement::ECDH_P521,
        ]
    };
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(16))]

    // Each side agrees with the other's public key, in every form each
    // parses, and the same private key gives the same public key.
    #[test]
    fn agreement(algorithm in 0..4usize) {
        let ours_alg = agreement_algorithms!(ours)[algorithm];
        let theirs_alg = agreement_algorithms!(theirs)[algorithm];
        let ours_key = ours::agreement::PrivateKey::generate(ours_alg).unwrap();
        let theirs_key = theirs::agreement::PrivateKey::generate(theirs_alg).unwrap();
        let ours_public = ours_key.compute_public_key().unwrap();
        let theirs_public = theirs_key.compute_public_key().unwrap();

        let ours_secret = |peer: &[u8]| {
            ours::agreement::agree(
                &ours_key,
                ours::agreement::UnparsedPublicKey::new(ours_alg, peer),
                (),
                |secret| Ok(secret.to_vec()),
            )
        };
        let theirs_secret = |peer: &[u8]| {
            theirs::agreement::agree(
                &theirs_key,
                theirs::agreement::UnparsedPublicKey::new(theirs_alg, peer),
                (),
                |secret| Ok(secret.to_vec()),
            )
        };
        let expected = theirs_secret(ours_public.as_ref()).unwrap();
        prop_assert_eq!(ours_secret(theirs_public.as_ref()).unwrap(), expected.clone());

        // X.509, and a NIST curve's compressed point.
        let spki = theirs_public.as_der().unwrap();
        prop_assert_eq!(ours_secret(spki.as_ref()).unwrap(), expected.clone());
        let ours_spki = ours_public.as_der().unwrap();
        prop_assert_eq!(theirs_secret(ours_spki.as_ref()).unwrap(), expected.clone());
        let compressed: Result<theirs::encoding::EcPublicKeyCompressedBin, _> =
            theirs_public.as_be_bytes();
        let ours_compressed: Result<ours::encoding::EcPublicKeyCompressedBin, _> =
            ours_public.as_be_bytes();
        prop_assert_eq!(compressed.is_ok(), ours_compressed.is_ok());
        if let (Ok(compressed), Ok(ours_compressed)) = (compressed, ours_compressed) {
            prop_assert_eq!(ours_secret(compressed.as_ref()).unwrap(), expected.clone());
            prop_assert_eq!(theirs_secret(ours_compressed.as_ref()).unwrap(), expected);
        }

        // The same private key, as its bytes and as DER.
        let scalar = match algorithm {
            0 => {
                let seed: theirs::encoding::Curve25519SeedBin = theirs_key.as_be_bytes().unwrap();
                seed.as_ref().to_vec()
            }
            _ => {
                let scalar: theirs::encoding::EcPrivateKeyBin = theirs_key.as_be_bytes().unwrap();
                scalar.as_ref().to_vec()
            }
        };
        let loaded = ours::agreement::PrivateKey::from_private_key(ours_alg, &scalar).unwrap();
        prop_assert_eq!(loaded.compute_public_key().unwrap().as_ref().to_vec(), theirs_public.as_ref());
        if algorithm != 0 {
            for der in [
                theirs::encoding::AsDer::<theirs::encoding::Pkcs8V1Der>::as_der(&theirs_key).unwrap().as_ref().to_vec(),
                theirs::encoding::AsDer::<theirs::encoding::EcPrivateKeyRfc5915Der>::as_der(&theirs_key)
                    .unwrap()
                    .as_ref()
                    .to_vec(),
            ] {
                let loaded = ours::agreement::PrivateKey::from_private_key_der(ours_alg, &der).unwrap();
                prop_assert_eq!(loaded.compute_public_key().unwrap().as_ref().to_vec(), theirs_public.as_ref());
            }
            for der in [
                ours::encoding::AsDer::<ours::encoding::Pkcs8V1Der>::as_der(&ours_key).unwrap().as_ref().to_vec(),
                ours::encoding::AsDer::<ours::encoding::EcPrivateKeyRfc5915Der>::as_der(&ours_key)
                    .unwrap()
                    .as_ref()
                    .to_vec(),
            ] {
                let loaded = theirs::agreement::PrivateKey::from_private_key_der(theirs_alg, &der).unwrap();
                prop_assert_eq!(loaded.compute_public_key().unwrap().as_ref().to_vec(), ours_public.as_ref());
            }
        }
    }

    // Each verifies the other's signatures, over the message and its digest,
    // with the public key in each form, and loads the other's PKCS#8.
    #[test]
    fn ecdsa(algorithm in 0..10usize, msg in vec(any::<u8>(), 0..100)) {
        macro_rules! algorithms {
            ($c:ident) => {
                [
                    (&$c::signature::ECDSA_P256_SHA256_ASN1_SIGNING, &$c::signature::ECDSA_P256_SHA256_ASN1, &$c::digest::SHA256),
                    (&$c::signature::ECDSA_P256_SHA256_FIXED_SIGNING, &$c::signature::ECDSA_P256_SHA256_FIXED, &$c::digest::SHA256),
                    (&$c::signature::ECDSA_P384_SHA384_ASN1_SIGNING, &$c::signature::ECDSA_P384_SHA384_ASN1, &$c::digest::SHA384),
                    (&$c::signature::ECDSA_P384_SHA384_FIXED_SIGNING, &$c::signature::ECDSA_P384_SHA384_FIXED, &$c::digest::SHA384),
                    (&$c::signature::ECDSA_P521_SHA256_ASN1_SIGNING, &$c::signature::ECDSA_P521_SHA256_ASN1, &$c::digest::SHA256),
                    (&$c::signature::ECDSA_P521_SHA256_FIXED_SIGNING, &$c::signature::ECDSA_P521_SHA256_FIXED, &$c::digest::SHA256),
                    (&$c::signature::ECDSA_P521_SHA384_ASN1_SIGNING, &$c::signature::ECDSA_P521_SHA384_ASN1, &$c::digest::SHA384),
                    (&$c::signature::ECDSA_P521_SHA384_FIXED_SIGNING, &$c::signature::ECDSA_P521_SHA384_FIXED, &$c::digest::SHA384),
                    (&$c::signature::ECDSA_P521_SHA512_ASN1_SIGNING, &$c::signature::ECDSA_P521_SHA512_ASN1, &$c::digest::SHA512),
                    (&$c::signature::ECDSA_P521_SHA512_FIXED_SIGNING, &$c::signature::ECDSA_P521_SHA512_FIXED, &$c::digest::SHA512),
                ]
            };
        }
        let (ours_sign, ours_verify, ours_hash) = algorithms!(ours)[algorithm];
        let (theirs_sign, theirs_verify, _) = algorithms!(theirs)[algorithm];
        let ours_rng = ours::rand::SystemRandom::new();
        let theirs_rng = theirs::rand::SystemRandom::new();

        let ours_pkcs8 = ours::signature::EcdsaKeyPair::generate_pkcs8(ours_sign, &ours_rng).unwrap();
        let theirs_pkcs8 = theirs::signature::EcdsaKeyPair::generate_pkcs8(theirs_sign, &theirs_rng).unwrap();
        let ours_pair = ours::signature::EcdsaKeyPair::from_pkcs8(ours_sign, theirs_pkcs8.as_ref()).unwrap();
        let theirs_pair = theirs::signature::EcdsaKeyPair::from_pkcs8(theirs_sign, ours_pkcs8.as_ref()).unwrap();
        let ours_mirror = ours::signature::EcdsaKeyPair::from_pkcs8(ours_sign, ours_pkcs8.as_ref()).unwrap();
        prop_assert_eq!(ours_mirror.public_key().as_ref(), theirs_pair.public_key().as_ref());

        // rind's signatures, verified by aws-lc-rs.
        let theirs_public = ours_mirror.public_key().as_ref().to_vec();
        let ours_signature = ours_mirror.sign(&ours_rng, &msg).unwrap();
        let ours_digest_signature = ours_mirror
            .sign_digest(&ours::digest::digest(ours_hash, &msg))
            .unwrap();
        let spki = ours_mirror.public_key().as_der().unwrap();
        let compressed: ours::encoding::EcPublicKeyCompressedBin = ours_mirror.public_key().as_be_bytes().unwrap();
        for key in [&theirs_public[..], spki.as_ref(), compressed.as_ref()] {
            let key = theirs::signature::UnparsedPublicKey::new(theirs_verify, key);
            prop_assert!(key.verify(&msg, ours_signature.as_ref()).is_ok());
            prop_assert!(key.verify(&msg, ours_digest_signature.as_ref()).is_ok());
        }

        // aws-lc-rs's signatures, verified by rind, as bytes, X.509, and
        // compressed, and over the digest.
        let theirs_signature = theirs_pair.sign(&theirs_rng, &msg).unwrap();
        let spki = theirs_pair.public_key().as_der().unwrap();
        let compressed: theirs::encoding::EcPublicKeyCompressedBin = theirs_pair.public_key().as_be_bytes().unwrap();
        let digest = ours::digest::digest(ours_hash, &msg);
        for key in [theirs_pair.public_key().as_ref(), spki.as_ref(), compressed.as_ref()] {
            let key = ours::signature::UnparsedPublicKey::new(ours_verify, key);
            prop_assert!(key.verify(&msg, theirs_signature.as_ref()).is_ok());
            prop_assert!(key.verify_digest(&digest, theirs_signature.as_ref()).is_ok());
            let parsed = key.parse().unwrap();
            prop_assert!(parsed.verify_sig(&msg, theirs_signature.as_ref()).is_ok());
            prop_assert!(parsed.verify_digest_sig(&digest, theirs_signature.as_ref()).is_ok());
            prop_assert!(key.verify(b"other", theirs_signature.as_ref()).is_err());
        }

        // The private key's other encodings.
        let scalar: theirs::encoding::EcPrivateKeyBin = theirs_pair.private_key().as_be_bytes().unwrap();
        let loaded = ours::signature::EcdsaKeyPair::from_private_key_and_public_key(
            ours_sign,
            scalar.as_ref(),
            theirs_pair.public_key().as_ref(),
        )
        .unwrap();
        prop_assert_eq!(loaded.public_key().as_ref(), theirs_pair.public_key().as_ref());
        let sec1: theirs::encoding::EcPrivateKeyRfc5915Der = theirs_pair.private_key().as_der().unwrap();
        let loaded = ours::signature::EcdsaKeyPair::from_private_key_der(ours_sign, sec1.as_ref()).unwrap();
        prop_assert_eq!(loaded.public_key().as_ref(), theirs_pair.public_key().as_ref());
        let sec1: ours::encoding::EcPrivateKeyRfc5915Der = ours_pair.private_key().as_der().unwrap();
        let loaded = theirs::signature::EcdsaKeyPair::from_private_key_der(theirs_sign, sec1.as_ref()).unwrap();
        prop_assert_eq!(loaded.public_key().as_ref(), ours_pair.public_key().as_ref());
        let scalar: ours::encoding::EcPrivateKeyBin = ours_pair.private_key().as_be_bytes().unwrap();
        prop_assert_eq!(scalar.as_ref(), {
            let theirs_scalar: theirs::encoding::EcPrivateKeyBin = loaded.private_key().as_be_bytes().unwrap();
            theirs_scalar.as_ref().to_vec()
        });
    }

    // Ed25519 signs deterministically, so both sign alike from one seed.
    #[test]
    fn ed25519(seed in any::<[u8; 32]>(), msg in vec(any::<u8>(), 0..100)) {
        let ours_pair = ours::signature::Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
        let theirs_pair = theirs::signature::Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
        prop_assert_eq!(ours_pair.public_key().as_ref(), theirs_pair.public_key().as_ref());
        prop_assert_eq!(ours_pair.sign(&msg).as_ref().to_vec(), theirs_pair.sign(&msg).as_ref().to_vec());
        prop_assert_eq!(
            ours_pair.public_key().as_der().unwrap().as_ref().to_vec(),
            theirs_pair.public_key().as_der().unwrap().as_ref().to_vec()
        );

        for (ours_doc, theirs_doc) in [
            (ours_pair.to_pkcs8().unwrap(), theirs_pair.to_pkcs8().unwrap()),
            (ours_pair.to_pkcs8v1().unwrap(), theirs_pair.to_pkcs8v1().unwrap()),
        ] {
            prop_assert_eq!(ours_doc.as_ref(), theirs_doc.as_ref());
            let loaded = ours::signature::Ed25519KeyPair::from_pkcs8_maybe_unchecked(theirs_doc.as_ref()).unwrap();
            prop_assert_eq!(loaded.public_key().as_ref(), theirs_pair.public_key().as_ref());
        }

        let signature = theirs_pair.sign(&msg);
        let spki = theirs_pair.public_key().as_der().unwrap();
        for key in [theirs_pair.public_key().as_ref(), spki.as_ref()] {
            let key = ours::signature::UnparsedPublicKey::new(&ours::signature::ED25519, key);
            prop_assert!(key.verify(&msg, signature.as_ref()).is_ok());
            prop_assert!(key.verify(b"other", signature.as_ref()).is_err());
        }
        let seed_bin: ours::encoding::Curve25519SeedBin = ours_pair.seed().unwrap().as_be_bytes().unwrap();
        prop_assert_eq!(seed_bin.as_ref(), &seed[..]);
    }

    #[test]
    fn kem(_case in any::<u8>()) {
        let ours_key = ours::kem::DecapsulationKey::generate(&ours::kem::ML_KEM_768).unwrap();
        let theirs_key = theirs::kem::DecapsulationKey::generate(&theirs::kem::ML_KEM_768).unwrap();

        let ours_public = ours_key.encapsulation_key().unwrap().key_bytes().unwrap();
        let peer = theirs::kem::EncapsulationKey::new(&theirs::kem::ML_KEM_768, ours_public.as_ref()).unwrap();
        let (ciphertext, secret) = peer.encapsulate().unwrap();
        let ours_secret = ours_key.decapsulate(ours::kem::Ciphertext::from(ciphertext.as_ref())).unwrap();
        prop_assert_eq!(ours_secret.as_ref(), secret.as_ref());

        let theirs_public = theirs_key.encapsulation_key().unwrap().key_bytes().unwrap();
        let peer = ours::kem::EncapsulationKey::new(&ours::kem::ML_KEM_768, theirs_public.as_ref()).unwrap();
        let (ciphertext, secret) = peer.encapsulate().unwrap();
        let theirs_secret = theirs_key
            .decapsulate(theirs::kem::Ciphertext::from(ciphertext.as_ref()))
            .unwrap();
        prop_assert_eq!(theirs_secret.as_ref(), secret.as_ref());

        use ours::kem::AlgorithmIdentifier as _;
        use theirs::kem::AlgorithmIdentifier as _;
        prop_assert_eq!(ours::kem::ML_KEM_768.id().nid(), theirs::kem::ML_KEM_768.id().nid());
    }
}

/// One RSA key, as PKCS#8, generated once by aws-lc-rs.
fn rsa_pkcs8() -> &'static [u8] {
    static PKCS8: OnceLock<Vec<u8>> = OnceLock::new();
    PKCS8.get_or_init(|| {
        let key = theirs::rsa::KeyPair::generate(theirs::rsa::KeySize::Rsa2048).unwrap();
        let der: theirs::encoding::Pkcs8V1Der = key.as_der().unwrap();
        der.as_ref().to_vec()
    })
}

const OURS_PSS_MAX: ours::signature::RsaSignatureEncoding =
    ours::signature::RSA_PSS_SHA384.with_pss_salt_length(ours::signature::RsaPssSaltLength::Max);
const THEIRS_PSS_MAX: theirs::rsa::RsaParameters = theirs::signature::RSA_PSS_2048_8192_SHA384
    .with_pss_salt_length(theirs::rsa::RsaPssSaltLength::Max);
const THEIRS_PSS_20: theirs::signature::RsaSignatureEncoding = theirs::signature::RSA_PSS_SHA256
    .with_pss_salt_length(theirs::rsa::RsaPssSaltLength::Custom(20));
const OURS_PSS_20: ours::rsa::RsaParameters = ours::signature::RSA_PSS_2048_8192_SHA256
    .with_pss_salt_length(ours::rsa::RsaPssSaltLength::Custom(20));

proptest! {
    #![proptest_config(ProptestConfig::with_cases(8))]

    // PKCS#1 v1.5 signs deterministically, so both sign alike; PSS
    // signatures, with any salt length, verify across.
    #[test]
    fn rsa(msg in vec(any::<u8>(), 0..100)) {
        let ours_pair = ours::rsa::KeyPair::from_pkcs8(rsa_pkcs8()).unwrap();
        let theirs_pair = theirs::rsa::KeyPair::from_pkcs8(rsa_pkcs8()).unwrap();
        prop_assert_eq!(ours_pair.public_key().as_ref(), theirs_pair.public_key().as_ref());
        prop_assert_eq!(ours_pair.public_modulus_len(), theirs_pair.public_modulus_len());
        #[cfg(feature = "ring-io")]
        prop_assert_eq!(
            ours_pair.public_key().modulus().big_endian_without_leading_zero(),
            theirs_pair.public_key().modulus().big_endian_without_leading_zero()
        );
        prop_assert_eq!(
            ours_pair.public_key().as_der().unwrap().as_ref().to_vec(),
            theirs_pair.public_key().as_der().unwrap().as_ref().to_vec()
        );
        let ours_rng = ours::rand::SystemRandom::new();
        let theirs_rng = theirs::rand::SystemRandom::new();
        let len = ours_pair.public_modulus_len();

        for (ours_enc, theirs_enc) in [
            (&ours::signature::RSA_PKCS1_SHA256, &theirs::signature::RSA_PKCS1_SHA256),
            (&ours::signature::RSA_PKCS1_SHA384, &theirs::signature::RSA_PKCS1_SHA384),
            (&ours::signature::RSA_PKCS1_SHA512, &theirs::signature::RSA_PKCS1_SHA512),
        ] {
            let mut ours_sig = vec![0; len];
            ours_pair.sign(ours_enc, &ours_rng, &msg, &mut ours_sig).unwrap();
            let mut theirs_sig = vec![0; len];
            theirs_pair.sign(theirs_enc, &theirs_rng, &msg, &mut theirs_sig).unwrap();
            prop_assert_eq!(ours_sig, theirs_sig);
        }

        // rind's PSS, verified by aws-lc-rs, and the reverse.
        let public = ours_pair.public_key().as_ref();
        for (ours_enc, theirs_params) in [
            (&ours::signature::RSA_PSS_SHA256, &theirs::signature::RSA_PSS_2048_8192_SHA256),
            (&ours::signature::RSA_PSS_SHA512, &theirs::signature::RSA_PSS_2048_8192_SHA512),
            (&OURS_PSS_MAX, &THEIRS_PSS_MAX),
        ] {
            let mut sig = vec![0; len];
            ours_pair.sign(ours_enc, &ours_rng, &msg, &mut sig).unwrap();
            let key = theirs::signature::UnparsedPublicKey::new(theirs_params, public);
            prop_assert!(key.verify(&msg, &sig).is_ok());
        }
        let spki = theirs_pair.public_key().as_der().unwrap();
        for (theirs_enc, ours_params) in [
            (&theirs::signature::RSA_PSS_SHA384, &ours::signature::RSA_PSS_2048_8192_SHA384),
            (&THEIRS_PSS_20, &OURS_PSS_20),
        ] {
            let mut sig = vec![0; len];
            theirs_pair.sign(theirs_enc, &theirs_rng, &msg, &mut sig).unwrap();
            for key in [public, spki.as_ref()] {
                let key = ours::signature::UnparsedPublicKey::new(ours_params, key);
                prop_assert!(key.verify(&msg, &sig).is_ok());
                prop_assert!(key.verify(b"other", &sig).is_err());
            }
            #[cfg(feature = "ring-io")]
            {
                let components: ours::rsa::PublicKeyComponents<Vec<u8>> = ours_pair.public_key().into();
                prop_assert!(components.verify(ours_params, &msg, &sig).is_ok());
            }
        }
    }

    // RSA-OAEP: each decrypts the other's ciphertexts, with every hash and a
    // label or none.
    #[test]
    fn oaep(algorithm in 0..4usize, msg in vec(any::<u8>(), 0..100), label in proptest::option::of(vec(any::<u8>(), 0..20))) {
        macro_rules! algorithms {
            ($c:ident) => {
                [
                    &$c::rsa::OAEP_SHA1_MGF1SHA1,
                    &$c::rsa::OAEP_SHA256_MGF1SHA256,
                    &$c::rsa::OAEP_SHA384_MGF1SHA384,
                    &$c::rsa::OAEP_SHA512_MGF1SHA512,
                ]
            };
        }
        let ours_alg = algorithms!(ours)[algorithm];
        let theirs_alg = algorithms!(theirs)[algorithm];
        let label = label.as_deref();

        let ours_private = ours::rsa::PrivateDecryptingKey::from_pkcs8(rsa_pkcs8()).unwrap();
        let theirs_private = theirs::rsa::PrivateDecryptingKey::from_pkcs8(rsa_pkcs8()).unwrap();
        let spki = theirs_private.public_key().as_der().unwrap();
        prop_assert_eq!(ours_private.public_key().as_der().unwrap().as_ref().to_vec(), spki.as_ref());
        let ours_public = ours::rsa::OaepPublicEncryptingKey::new(
            ours::rsa::PublicEncryptingKey::from_der(spki.as_ref()).unwrap(),
        )
        .unwrap();
        let theirs_public = theirs::rsa::OaepPublicEncryptingKey::new(theirs_private.public_key()).unwrap();
        prop_assert_eq!(ours_public.max_plaintext_size(ours_alg), theirs_public.max_plaintext_size(theirs_alg));
        prop_assert_eq!(ours_public.ciphertext_size(), theirs_public.ciphertext_size());
        let ours_private = ours::rsa::OaepPrivateDecryptingKey::new(ours_private).unwrap();
        let theirs_private = theirs::rsa::OaepPrivateDecryptingKey::new(theirs_private).unwrap();

        let mut ciphertext = vec![0; ours_public.ciphertext_size()];
        let ciphertext = ours_public.encrypt(ours_alg, &msg, &mut ciphertext, label).unwrap();
        let mut plaintext = vec![0; theirs_private.min_output_size()];
        prop_assert_eq!(
            theirs_private.decrypt(theirs_alg, ciphertext, &mut plaintext, label).unwrap(),
            &msg[..]
        );

        let mut ciphertext = vec![0; theirs_public.ciphertext_size()];
        let ciphertext = theirs_public.encrypt(theirs_alg, &msg, &mut ciphertext, label).unwrap();
        let mut plaintext = vec![0; ours_private.min_output_size()];
        prop_assert_eq!(
            ours_private.decrypt(ours_alg, ciphertext, &mut plaintext, label).unwrap(),
            &msg[..]
        );
        // Longer than any label generated above.
        let mut plaintext = vec![0; ours_private.min_output_size()];
        let wrong = [0xff; 21];
        prop_assert!(ours_private.decrypt(ours_alg, ciphertext, &mut plaintext, Some(&wrong)).is_err());
    }
}

/// Malformed keys are refused by both.
#[test]
fn refused() {
    let pkcs8 = rsa_pkcs8();
    let truncated = &pkcs8[..pkcs8.len() - 1];
    assert!(ours::rsa::KeyPair::from_pkcs8(truncated).is_err());
    assert!(theirs::rsa::KeyPair::from_pkcs8(truncated).is_err());
    assert!(ours::signature::Ed25519KeyPair::from_seed_unchecked(&[0; 31]).is_err());
    assert!(theirs::signature::Ed25519KeyPair::from_seed_unchecked(&[0; 31]).is_err());
    for alg in 0..4 {
        let ours_key =
            ours::agreement::PrivateKey::generate(agreement_algorithms!(ours)[alg]).unwrap();
        let peer =
            ours::agreement::UnparsedPublicKey::new(agreement_algorithms!(ours)[alg], [4u8; 5]);
        assert!(ours::agreement::agree(&ours_key, peer, (), |_| Ok(())).is_err());
    }
}

/// PKCS#8 v1 whose algorithm is `oid`, with `parameters` appended to the
/// algorithm identifier when present, and `private_key` as the private key.
fn pkcs8_private_key(oid: &[u8], parameters: Option<&[u8]>, private_key: &[u8]) -> Vec<u8> {
    let mut algorithm = der(0x06, oid);
    if let Some(parameters) = parameters {
        algorithm.extend_from_slice(parameters);
    }
    der(
        0x30,
        &[
            der(0x02, &[0]),
            der(0x30, &algorithm),
            der(0x04, private_key),
        ]
        .concat(),
    )
}

/// A DER element tagged `tag` holding `contents`.
fn der(tag: u8, contents: &[u8]) -> Vec<u8> {
    let len = contents.len();
    let mut out = vec![tag];
    match len {
        0..=0x7f => out.push(len as u8),
        0x80..=0xff => out.extend([0x81, len as u8]),
        _ => out.extend([0x82, (len >> 8) as u8, len as u8]),
    }
    out.extend_from_slice(contents);
    out
}

#[test]
fn rsa_public_keys() {
    let key = theirs::rsa::KeyPair::from_pkcs8(rsa_pkcs8()).unwrap();
    let pkcs1 = key.public_key().as_ref().to_vec();

    // Both load the key as PKCS#1, and in an SPKI whose `rsaEncryption`
    // omits its NULL parameters.
    const RSA_ENCRYPTION: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01];
    let bits = [&[0][..], &pkcs1].concat();
    let spki = der(
        0x30,
        &[der(0x30, &der(0x06, RSA_ENCRYPTION)), der(0x03, &bits)].concat(),
    );
    for input in [&pkcs1, &spki] {
        let ours = ours::rsa::PublicKey::from_der(input).unwrap();
        let theirs = theirs::rsa::PublicKey::from_der(input).unwrap();
        assert_eq!(ours.as_ref(), theirs.as_ref());
    }

    // Both refuse an even modulus. e = 65537 is the last five bytes, so the
    // modulus ends just before them.
    let mut even = pkcs1.clone();
    let last = even.len() - 6;
    even[last] &= 0xfe;
    assert!(ours::rsa::PublicKey::from_der(&even).is_err());
    assert!(theirs::rsa::PublicKey::from_der(&even).is_err());
    assert!(ours::rsa::RsaParameters::public_modulus_len(&even).is_err());
    assert!(theirs::rsa::RsaParameters::public_modulus_len(&even).is_err());

    // A modulus too long for DER's two-byte lengths fails to encode.
    let mut n = vec![0xff; 65536];
    n[65535] = 0xfb;
    let components = ours::rsa::PublicKeyComponents {
        n,
        e: vec![1, 0, 1],
    };
    assert!(
        ours::encoding::AsDer::<ours::encoding::PublicKeyX509Der<'static>>::as_der(&components)
            .is_err()
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4))]

    #[test]
    fn ml_dsa(seed in any::<[u8; 32]>(), msg in vec(any::<u8>(), 0..80)) {
        ml_dsa_set(
            &ours::signature::ML_DSA_44_SIGNING,
            &ours::signature::ML_DSA_44,
            &theirs::signature::ML_DSA_44_SIGNING,
            &theirs::signature::ML_DSA_44,
            &seed,
            &msg,
        );
        ml_dsa_set(
            &ours::signature::ML_DSA_65_SIGNING,
            &ours::signature::ML_DSA_65,
            &theirs::signature::ML_DSA_65_SIGNING,
            &theirs::signature::ML_DSA_65,
            &seed,
            &msg,
        );
        ml_dsa_set(
            &ours::signature::ML_DSA_87_SIGNING,
            &ours::signature::ML_DSA_87,
            &theirs::signature::ML_DSA_87_SIGNING,
            &theirs::signature::ML_DSA_87,
            &seed,
            &msg,
        );
    }
}

fn ml_dsa_set(
    ours_sign: &'static ours::signature::PqdsaSigningAlgorithm,
    ours_verify: &'static ours::signature::PqdsaVerificationAlgorithm,
    theirs_sign: &'static theirs::signature::PqdsaSigningAlgorithm,
    theirs_verify: &'static theirs::signature::PqdsaVerificationAlgorithm,
    seed: &[u8; 32],
    msg: &[u8],
) {
    use theirs::encoding::AsRawBytes;

    assert_eq!(ours_sign.signature_len(), theirs_sign.signature_len());
    assert_eq!(ours_sign.public_key_len(), theirs_sign.public_key_len());
    assert_eq!(ours_sign.seed_len(), theirs_sign.seed_len());
    assert_eq!(format!("{ours_sign:?}"), format!("{theirs_sign:?}"));
    assert_eq!(format!("{ours_verify:?}"), format!("{theirs_verify:?}"));

    let ours = ours::signature::PqdsaKeyPair::from_seed(ours_sign, seed).unwrap();
    let theirs = theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, seed).unwrap();
    assert_eq!(ours.algorithm(), ours_sign);
    assert_eq!(theirs.algorithm(), theirs_sign);
    assert_eq!(ours.public_key().as_ref(), theirs.public_key().as_ref());
    assert_eq!(
        format!("{:?}", ours.public_key()),
        format!("{:?}", theirs.public_key())
    );
    assert_eq!(format!("{ours:?}"), format!("{theirs:?}"));
    assert_eq!(
        format!("{:?}", ours.private_key()),
        format!("{:?}", theirs.private_key())
    );

    let ours_pkcs8 = ours.to_pkcs8v1().unwrap();
    let theirs_pkcs8 = theirs.to_pkcs8v1().unwrap();
    assert_eq!(ours_pkcs8.as_ref(), theirs_pkcs8.as_ref());
    let ours_der =
        ours::encoding::AsDer::<ours::encoding::Pkcs8V1Der>::as_der(&ours.private_key()).unwrap();
    let theirs_der =
        theirs::encoding::AsDer::<theirs::encoding::Pkcs8V1Der>::as_der(&theirs.private_key())
            .unwrap();
    assert_eq!(ours_der.as_ref(), theirs_pkcs8.as_ref());
    assert_eq!(theirs_der.as_ref(), theirs_pkcs8.as_ref());
    assert_eq!(
        ours.public_key().as_der().unwrap().as_ref(),
        theirs.public_key().as_der().unwrap().as_ref()
    );

    let reloaded =
        ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, theirs_pkcs8.as_ref()).unwrap();
    assert_eq!(reloaded.public_key().as_ref(), theirs.public_key().as_ref());
    assert_eq!(
        reloaded.to_pkcs8v1().unwrap().as_ref(),
        theirs_pkcs8.as_ref()
    );
    let reloaded =
        theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, ours_pkcs8.as_ref()).unwrap();
    assert_eq!(reloaded.public_key().as_ref(), ours.public_key().as_ref());

    // Hedged signatures verify across, as raw keys and as SPKI, parsed once.
    let mut ours_sig = vec![0x5a; ours_sign.signature_len() + 4];
    assert!(
        ours.sign(msg, &mut ours_sig[..ours_sign.signature_len() - 1])
            .is_err()
    );
    let ours_len = ours.sign(msg, &mut ours_sig).unwrap();
    assert_eq!(ours_len, ours_sign.signature_len());
    assert_eq!(&ours_sig[ours_len..], &[0x5a; 4]);
    let mut theirs_sig = vec![0u8; theirs_sign.signature_len()];
    assert_eq!(theirs.sign(msg, &mut theirs_sig).unwrap(), theirs_sig.len());

    let ours_spki = ours.public_key().as_der().unwrap();
    let theirs_spki = theirs.public_key().as_der().unwrap();
    for key in [theirs.public_key().as_ref(), theirs_spki.as_ref()] {
        let key = ours::signature::UnparsedPublicKey::new(ours_verify, key);
        assert!(key.verify(msg, &theirs_sig).is_ok());
        assert!(key.verify(b"other message", &theirs_sig).is_err());
        assert!(key.verify_digest(&digest(msg), &theirs_sig).is_err());
        let parsed = key.parse().unwrap();
        assert!(parsed.verify_sig(msg, &theirs_sig).is_ok());
        assert!(parsed.verify_digest_sig(&digest(msg), &theirs_sig).is_err());
    }
    for key in [ours.public_key().as_ref(), ours_spki.as_ref()] {
        let key = theirs::signature::UnparsedPublicKey::new(theirs_verify, key);
        assert!(key.verify(msg, &ours_sig[..ours_len]).is_ok());
        assert!(key.verify(b"other message", &ours_sig[..ours_len]).is_err());
    }
    let mut flipped = theirs_sig.clone();
    flipped[0] ^= 0x01;
    assert!(
        ours::signature::UnparsedPublicKey::new(ours_verify, theirs.public_key().as_ref())
            .verify(msg, &flipped)
            .is_err()
    );

    // The expanded private key has no seed, so PKCS#8 export fails on both,
    // and `from_raw_private_key` loads it.
    let raw = theirs.private_key().as_raw_bytes().unwrap();
    let ours_expanded =
        ours::signature::PqdsaKeyPair::from_raw_private_key(ours_sign, raw.as_ref()).unwrap();
    let theirs_expanded =
        theirs::signature::PqdsaKeyPair::from_raw_private_key(theirs_sign, raw.as_ref()).unwrap();
    assert_eq!(
        ours_expanded.public_key().as_ref(),
        theirs.public_key().as_ref()
    );
    assert_eq!(
        theirs_expanded.public_key().as_ref(),
        theirs.public_key().as_ref()
    );
    assert!(ours_expanded.to_pkcs8v1().is_err());
    assert!(theirs_expanded.to_pkcs8v1().is_err());
    assert!(
        ours::encoding::AsDer::<ours::encoding::Pkcs8V1Der>::as_der(&ours_expanded.private_key())
            .is_err()
    );
    assert!(
        theirs::encoding::AsDer::<theirs::encoding::Pkcs8V1Der>::as_der(
            &theirs_expanded.private_key()
        )
        .is_err()
    );
    let mut expanded_sig = vec![0; ours_sign.signature_len()];
    ours_expanded.sign(msg, &mut expanded_sig).unwrap();
    assert!(
        theirs::signature::UnparsedPublicKey::new(theirs_verify, theirs.public_key().as_ref())
            .verify(msg, &expanded_sig)
            .is_ok()
    );

    let expanded_pkcs8 = ml_dsa_expanded_pkcs8(theirs_pkcs8.as_ref(), raw.as_ref());
    let from_expanded =
        ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &expanded_pkcs8).unwrap();
    let from_expanded_theirs =
        theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &expanded_pkcs8).unwrap();
    assert_eq!(
        from_expanded.public_key().as_ref(),
        theirs.public_key().as_ref()
    );
    assert_eq!(
        from_expanded_theirs.public_key().as_ref(),
        theirs.public_key().as_ref()
    );
    assert!(from_expanded.to_pkcs8v1().is_err());
    assert!(from_expanded_theirs.to_pkcs8v1().is_err());

    let both = ml_dsa_both_pkcs8(theirs_pkcs8.as_ref(), seed, raw.as_ref());
    let from_both = ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &both).unwrap();
    let from_both_theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &both).unwrap();
    assert_eq!(
        from_both.public_key().as_ref(),
        theirs.public_key().as_ref()
    );
    assert_eq!(
        from_both_theirs.public_key().as_ref(),
        theirs.public_key().as_ref()
    );
    assert_eq!(
        from_both.to_pkcs8v1().unwrap().as_ref(),
        theirs_pkcs8.as_ref()
    );

    let mut disagree = raw.as_ref().to_vec();
    let last = disagree.len() - 1;
    disagree[last] ^= 0x01;
    let bad_both = ml_dsa_both_pkcs8(theirs_pkcs8.as_ref(), seed, &disagree);
    same_rejection(
        ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &bad_both),
        theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &bad_both),
    );
}

fn digest(msg: &[u8]) -> ours::digest::Digest {
    ours::digest::digest(&ours::digest::SHA256, msg)
}

fn same_rejection<T, U>(
    ours: Result<T, ours::error::KeyRejected>,
    theirs: Result<U, theirs::error::KeyRejected>,
) {
    match (ours, theirs) {
        (Err(ours), Err(theirs)) => assert_eq!(
            ours.description_(),
            theirs.description_(),
            "{ours} vs {theirs}"
        ),
        (ours, theirs) => panic!(
            "expected both to fail, got ok {} {}",
            ours.is_ok(),
            theirs.is_ok()
        ),
    }
}

/// The PKCS#8 header of a seed-form key: version and algorithm identifier.
fn ml_dsa_pkcs8_header(seed_form: &[u8]) -> &[u8] {
    &seed_form[2..2 + 3 + 13]
}

fn ml_dsa_expanded_pkcs8(seed_form: &[u8], raw: &[u8]) -> Vec<u8> {
    let inner = der(0x04, raw);
    der(
        0x30,
        &[ml_dsa_pkcs8_header(seed_form), &der(0x04, &inner)].concat(),
    )
}

fn ml_dsa_both_pkcs8(seed_form: &[u8], seed: &[u8], raw: &[u8]) -> Vec<u8> {
    let choice = der(0x30, &[der(0x04, seed), der(0x04, raw)].concat());
    der(
        0x30,
        &[ml_dsa_pkcs8_header(seed_form), &der(0x04, &choice)].concat(),
    )
}

/// Length and algorithm mismatches aws-lc-rs names the same way.
#[test]
fn ml_dsa_rejected() {
    use theirs::encoding::AsRawBytes;

    let algs = [
        (
            &ours::signature::ML_DSA_44_SIGNING,
            &theirs::signature::ML_DSA_44_SIGNING,
            &ours::signature::ML_DSA_65_SIGNING,
            &theirs::signature::ML_DSA_65_SIGNING,
        ),
        (
            &ours::signature::ML_DSA_65_SIGNING,
            &theirs::signature::ML_DSA_65_SIGNING,
            &ours::signature::ML_DSA_87_SIGNING,
            &theirs::signature::ML_DSA_87_SIGNING,
        ),
        (
            &ours::signature::ML_DSA_87_SIGNING,
            &theirs::signature::ML_DSA_87_SIGNING,
            &ours::signature::ML_DSA_44_SIGNING,
            &theirs::signature::ML_DSA_44_SIGNING,
        ),
    ];
    for (ours_sign, theirs_sign, ours_other, theirs_other) in algs {
        same_rejection(
            ours::signature::PqdsaKeyPair::from_seed(ours_sign, &[0; 31]),
            theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, &[0; 31]),
        );
        same_rejection(
            ours::signature::PqdsaKeyPair::from_seed(ours_sign, &[0; 33]),
            theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, &[0; 33]),
        );
        same_rejection(
            ours::signature::PqdsaKeyPair::from_seed(ours_sign, &[]),
            theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, &[]),
        );
        same_rejection(
            ours::signature::PqdsaKeyPair::from_raw_private_key(ours_sign, &[7; 32]),
            theirs::signature::PqdsaKeyPair::from_raw_private_key(theirs_sign, &[7; 32]),
        );
        same_rejection(
            ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &[]),
            theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &[]),
        );

        let seed = [4u8; 32];
        let other = theirs::signature::PqdsaKeyPair::from_seed(theirs_other, &seed).unwrap();
        let raw = other.private_key().as_raw_bytes().unwrap();
        same_rejection(
            ours::signature::PqdsaKeyPair::from_raw_private_key(ours_sign, raw.as_ref()),
            theirs::signature::PqdsaKeyPair::from_raw_private_key(theirs_sign, raw.as_ref()),
        );
        let pkcs8 = other.to_pkcs8v1().unwrap();
        same_rejection(
            ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, pkcs8.as_ref()),
            theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, pkcs8.as_ref()),
        );
        // The other parameter set still loads its own key.
        assert!(ours::signature::PqdsaKeyPair::from_pkcs8(ours_other, pkcs8.as_ref()).is_ok());

        // A correctly sized expanded key whose parts no longer agree.
        let good = theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, &[6; 32]).unwrap();
        let raw = good.private_key().as_raw_bytes().unwrap();
        let raw = raw.as_ref();
        let mut flipped_tr = raw.to_vec();
        flipped_tr[64] ^= 0x01;
        let mut zero_rho = raw.to_vec();
        zero_rho[..32].fill(0);
        // s1 starts after rho, K, and tr. s2 follows s1. 0xff is outside eta's range.
        let s1 = 128;
        let s2 = s1
            + match ours_sign.public_key_len() {
                1312 => 4 * 96,  // ML-DSA-44: L polynomials, eta 2
                1952 => 5 * 128, // ML-DSA-65: L polynomials, eta 4
                2592 => 7 * 96,  // ML-DSA-87: L polynomials, eta 2
                len => panic!("unexpected ML-DSA public key length {len}"),
            };
        let mut bad_s1 = raw.to_vec();
        bad_s1[s1] = 0xff;
        let mut bad_s2 = raw.to_vec();
        bad_s2[s2] = 0xff;
        for corrupted in [&flipped_tr, &zero_rho, &bad_s1, &bad_s2] {
            same_rejection(
                ours::signature::PqdsaKeyPair::from_raw_private_key(ours_sign, corrupted),
                theirs::signature::PqdsaKeyPair::from_raw_private_key(theirs_sign, corrupted),
            );
        }
    }

    let ed25519 = theirs::signature::Ed25519KeyPair::from_seed_unchecked(&[3; 32]).unwrap();
    for doc in [ed25519.to_pkcs8v1().unwrap(), ed25519.to_pkcs8().unwrap()] {
        same_rejection(
            ours::signature::PqdsaKeyPair::from_pkcs8(
                &ours::signature::ML_DSA_65_SIGNING,
                doc.as_ref(),
            ),
            theirs::signature::PqdsaKeyPair::from_pkcs8(
                &theirs::signature::ML_DSA_65_SIGNING,
                doc.as_ref(),
            ),
        );
    }
    // v2 whose public key does not match. Both refuse it, so this is
    // InvalidEncoding rather than WrongAlgorithm.
    let mut mismatched = ed25519.to_pkcs8().unwrap().as_ref().to_vec();
    let last = mismatched.len() - 1;
    mismatched[last] ^= 0x01;
    same_rejection(
        ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_65_SIGNING, &mismatched),
        theirs::signature::PqdsaKeyPair::from_pkcs8(
            &theirs::signature::ML_DSA_65_SIGNING,
            &mismatched,
        ),
    );

    let as_ml_dsa = |pkcs8: &[u8]| {
        same_rejection(
            ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_44_SIGNING, pkcs8),
            theirs::signature::PqdsaKeyPair::from_pkcs8(
                &theirs::signature::ML_DSA_44_SIGNING,
                pkcs8,
            ),
        );
    };
    // RFC 8410 X25519. aws-lc-rs does not encode one, so this is that document.
    as_ml_dsa(&pkcs8_private_key(
        &[0x2b, 0x65, 0x6e],
        None,
        &der(0x04, &[0x11; 32]),
    ));
    let rng = theirs::rand::SystemRandom::new();
    for algorithm in [
        &theirs::signature::ECDSA_P256_SHA256_ASN1_SIGNING,
        &theirs::signature::ECDSA_P384_SHA384_ASN1_SIGNING,
        &theirs::signature::ECDSA_P521_SHA512_ASN1_SIGNING,
    ] {
        let doc = theirs::signature::EcdsaKeyPair::generate_pkcs8(algorithm, &rng).unwrap();
        as_ml_dsa(doc.as_ref());
    }
    as_ml_dsa(rsa_pkcs8());

    // secp256k1 parses in aws-lc-rs. rind has no parser for it, so the
    // refusal names differ; the README lists that. A key aws-lc-rs also
    // rejects still agrees.
    let scalar = [0u8; 31].into_iter().chain([1u8]).collect::<Vec<_>>();
    let public = [
        0x04, 0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62, 0x95, 0xce, 0x87,
        0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16,
        0xf8, 0x17, 0x98, 0x48, 0x3a, 0xda, 0x77, 0x26, 0xa3, 0xc4, 0x65, 0x5d, 0xa4, 0xfb, 0xfc,
        0x0e, 0x11, 0x08, 0xa8, 0xfd, 0x17, 0xb4, 0x48, 0xa6, 0x85, 0x54, 0x19, 0x9c, 0x47, 0xd0,
        0x8f, 0xfb, 0x10, 0xd4, 0xb8,
    ];
    let secp256k1 = |scalar: &[u8], public: Option<&[u8]>| {
        let mut ec = [der(0x02, &[1]), der(0x04, scalar)].concat();
        if let Some(public) = public {
            ec.extend(der(0xa1, &der(0x03, &[&[0], public].concat())));
        }
        pkcs8_private_key(
            &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01],
            Some(&der(0x06, &[0x2b, 0x81, 0x04, 0x00, 0x0a])),
            &der(0x30, &ec),
        )
    };
    for pkcs8 in [secp256k1(&scalar, Some(&public)), secp256k1(&scalar, None)] {
        let ours =
            ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_44_SIGNING, &pkcs8)
                .unwrap_err();
        let theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(
            &theirs::signature::ML_DSA_44_SIGNING,
            &pkcs8,
        )
        .unwrap_err();
        assert_eq!(ours.description_(), "InvalidEncoding");
        assert_eq!(theirs.description_(), "WrongAlgorithm");
    }
    as_ml_dsa(&secp256k1(&[0; 32], Some(&public)));
    let mut bad_public = public;
    bad_public[10] ^= 1;
    as_ml_dsa(&secp256k1(&scalar, Some(&bad_public)));

    // aws-lc parses these. rind has no implementation, so the names differ
    // and the README lists each one.
    let differs = |pkcs8: &[u8]| {
        let ours =
            ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_44_SIGNING, pkcs8)
                .unwrap_err();
        let theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(
            &theirs::signature::ML_DSA_44_SIGNING,
            pkcs8,
        )
        .unwrap_err();
        assert_eq!(ours.description_(), "InvalidEncoding");
        assert_eq!(theirs.description_(), "WrongAlgorithm");
    };
    let ec_on = |curve: &[u8], scalar: &[u8]| {
        let ec = der(0x30, &[der(0x02, &[1]), der(0x04, scalar)].concat());
        pkcs8_private_key(
            &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01],
            Some(&der(0x06, curve)),
            &ec,
        )
    };
    let mut p224 = vec![0u8; 28];
    p224[27] = 1;
    differs(&ec_on(&[0x2b, 0x81, 0x04, 0x00, 0x21], &p224));
    as_ml_dsa(&ec_on(&[0x2b, 0x81, 0x04, 0x00, 0x21], &[0; 28]));
    let mut brainpool = vec![0u8; 32];
    brainpool[31] = 1;
    differs(&ec_on(
        &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x07],
        &brainpool,
    ));
    let k1 = theirs::signature::EcdsaKeyPair::generate_pkcs8(
        &theirs::signature::ECDSA_P256K1_SHA256_ASN1_SIGNING,
        &rng,
    )
    .unwrap();
    differs(k1.as_ref());

    let (_, body, _) = der_split(rsa_pkcs8()).unwrap();
    let (_, _, body) = der_split(body).unwrap();
    let (_, _, body) = der_split(body).unwrap();
    let (_, pkcs1, _) = der_split(body).unwrap();
    let rsa_as = |oid: &[u8], parameters: Option<&[u8]>| pkcs8_private_key(oid, parameters, pkcs1);
    let pss = [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a];
    as_ml_dsa(&rsa_as(&pss, None));
    as_ml_dsa(&rsa_as(&pss, Some(&[0x30, 0x00])));
    as_ml_dsa(&rsa_as(&pss, Some(&[0x05, 0x00])));
    as_ml_dsa(&rsa_as(
        &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x07],
        Some(&[0x05, 0x00]),
    ));
    as_ml_dsa(&rsa_as(&[0x55, 0x08, 0x01, 0x01], Some(&[0x05, 0x00])));
    let sha256 = der(
        0x30,
        &[
            der(
                0x06,
                &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01],
            ),
            vec![0x05, 0x00],
        ]
        .concat(),
    );
    differs(&rsa_as(&pss, Some(&der(0x30, &der(0xa0, &sha256)))));

    let kem512 = [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x01];
    let seed = der(0x80, &[0x5a; 64]);
    for oid in [
        kem512,
        [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x02],
        [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x03],
    ] {
        as_ml_dsa(&pkcs8_private_key(&oid, None, &seed));
    }
    as_ml_dsa(&pkcs8_private_key(&kem512, None, &der(0x80, &[0x5a; 63])));
    as_ml_dsa(&pkcs8_private_key(&kem512, Some(&[0x05, 0x00]), &seed));
    as_ml_dsa(&pkcs8_private_key(
        &kem512,
        None,
        &der(0x04, &vec![0x11; 1632]),
    ));
    as_ml_dsa(&pkcs8_private_key(
        &kem512,
        None,
        &der(0x04, &vec![0x11; 1631]),
    ));

    let q = der_uint(
        &[0x80]
            .into_iter()
            .chain([0u8; 18])
            .chain([1])
            .collect::<Vec<_>>(),
    );
    let p = der_uint(
        &[0x01]
            .into_iter()
            .chain([0u8; 19])
            .chain([1])
            .collect::<Vec<_>>(),
    );
    let dsa = [0x2a, 0x86, 0x48, 0xce, 0x38, 0x04, 0x01];
    let params = der(0x30, &[p, q, der_uint(&[2])].concat());
    differs(&pkcs8_private_key(&dsa, Some(&params), &der_uint(&[1])));
    let tiny = der(
        0x30,
        &[
            der_uint(
                &[0x01]
                    .into_iter()
                    .chain([0u8; 19])
                    .chain([1])
                    .collect::<Vec<_>>(),
            ),
            der_uint(&[3]),
            der_uint(&[2]),
        ]
        .concat(),
    );
    as_ml_dsa(&pkcs8_private_key(&dsa, Some(&tiny), &der_uint(&[1])));
    as_ml_dsa(&pkcs8_private_key(
        &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x03, 0x01],
        Some(&params),
        &der_uint(&[1]),
    ));
}

/// Signatures that are not a parameter set's encoding, checked both before
/// and after the public key is parsed.
#[test]
fn ml_dsa_hostile_signatures() {
    let sets = [
        (
            &ours::signature::ML_DSA_44_SIGNING,
            &ours::signature::ML_DSA_44,
            &theirs::signature::ML_DSA_44_SIGNING,
            &theirs::signature::ML_DSA_44,
        ),
        (
            &ours::signature::ML_DSA_65_SIGNING,
            &ours::signature::ML_DSA_65,
            &theirs::signature::ML_DSA_65_SIGNING,
            &theirs::signature::ML_DSA_65,
        ),
        (
            &ours::signature::ML_DSA_87_SIGNING,
            &ours::signature::ML_DSA_87,
            &theirs::signature::ML_DSA_87_SIGNING,
            &theirs::signature::ML_DSA_87,
        ),
    ];
    let message = b"hostile";
    for (ours_sign, ours_verify, theirs_sign, theirs_verify) in sets {
        let ours = ours::signature::PqdsaKeyPair::from_seed(ours_sign, &[2; 32]).unwrap();
        let theirs = theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, &[2; 32]).unwrap();
        let pk = ours.public_key().as_ref();
        assert_eq!(pk, theirs.public_key().as_ref());
        let len = ours_sign.signature_len();
        let mut signatures: Vec<Vec<u8>> = vec![
            vec![],
            vec![0; len - 1],
            vec![0; len + 1],
            vec![0; len],
            vec![0xff; len],
        ];
        // An ML-DSA-65-length signature under a key of another set.
        let len65 = theirs::signature::ML_DSA_65_SIGNING.signature_len();
        if len != len65 {
            signatures.push(vec![0; len65]);
        }
        let ours_parsed = ours::signature::ParsedPublicKey::new(ours_verify, pk).unwrap();
        let theirs_parsed = theirs::signature::ParsedPublicKey::new(theirs_verify, pk).unwrap();
        for signature in &signatures {
            let ours_unparsed =
                ours::signature::UnparsedPublicKey::new(ours_verify, pk).verify(message, signature);
            let theirs_unparsed = theirs::signature::UnparsedPublicKey::new(theirs_verify, pk)
                .verify(message, signature);
            assert_eq!(
                ours_unparsed.is_ok(),
                theirs_unparsed.is_ok(),
                "unparsed len {}",
                signature.len()
            );
            assert_eq!(
                ours_parsed.verify_sig(message, signature).is_ok(),
                theirs_parsed.verify_sig(message, signature).is_ok(),
                "parsed len {}",
                signature.len()
            );
        }
    }
}

/// Public keys aws-lc-rs refuses, with the same `KeyRejected` name.
#[test]
fn ml_dsa_hostile_keys() {
    let ours_key =
        ours::signature::PqdsaKeyPair::from_seed(&ours::signature::ML_DSA_44_SIGNING, &[5; 32])
            .unwrap();
    let theirs_key =
        theirs::signature::PqdsaKeyPair::from_seed(&theirs::signature::ML_DSA_44_SIGNING, &[5; 32])
            .unwrap();
    assert_eq!(
        ours_key.public_key().as_ref(),
        theirs_key.public_key().as_ref()
    );
    let pk = theirs_key.public_key().as_ref().to_vec();
    let other =
        theirs::signature::PqdsaKeyPair::from_seed(&theirs::signature::ML_DSA_65_SIGNING, &[5; 32])
            .unwrap()
            .public_key()
            .as_ref()
            .to_vec();
    let truncated = pk[..pk.len() - 1].to_vec();
    let mut longer = pk.clone();
    longer.push(0);
    let mut wrong_oid = theirs_key.public_key().as_der().unwrap().as_ref().to_vec();
    let id44 = [
        0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x11,
    ];
    let id65 = [
        0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12,
    ];
    let at = wrong_oid
        .windows(id44.len())
        .position(|window| window == id44)
        .unwrap();
    wrong_oid[at..at + id44.len()].copy_from_slice(&id65);
    let ed25519 = theirs::signature::Ed25519KeyPair::from_seed_unchecked(&[3; 32])
        .unwrap()
        .public_key()
        .as_der()
        .unwrap();
    for (name, key) in [
        ("truncated", truncated.as_slice()),
        ("longer", longer.as_slice()),
        ("empty", &[][..]),
        ("wrong_oid", wrong_oid.as_slice()),
        ("ed25519", ed25519.as_ref()),
        ("other_raw", other.as_slice()),
    ] {
        let ours = ours::signature::ParsedPublicKey::new(&ours::signature::ML_DSA_44, key);
        let theirs = theirs::signature::ParsedPublicKey::new(&theirs::signature::ML_DSA_44, key);
        match (&ours, &theirs) {
            (Err(ours), Err(theirs)) if ours.description_() == theirs.description_() => {}
            _ => panic!(
                "{name} len {} ours {} ({}) theirs {} ({})",
                key.len(),
                ours.as_ref()
                    .err()
                    .map(|e| e.description_())
                    .unwrap_or("ok"),
                ours.as_ref()
                    .err()
                    .map(|e| e.to_string())
                    .unwrap_or_default(),
                theirs
                    .as_ref()
                    .err()
                    .map(|e| e.description_())
                    .unwrap_or("ok"),
                theirs
                    .as_ref()
                    .err()
                    .map(|e| e.to_string())
                    .unwrap_or_default(),
            ),
        }
        same_rejection(ours, theirs);
        same_rejection(
            ours::signature::UnparsedPublicKey::new(&ours::signature::ML_DSA_44, key).parse(),
            theirs::signature::UnparsedPublicKey::new(&theirs::signature::ML_DSA_44, key).parse(),
        );
    }
}

/// The deprecated alias matches `to_pkcs8v1`, as aws-lc-rs's does.
#[cfg(feature = "unstable")]
#[allow(deprecated)]
#[test]
fn ml_dsa_to_pkcs8_alias() {
    let key =
        ours::signature::PqdsaKeyPair::from_seed(&ours::signature::ML_DSA_44_SIGNING, &[8; 32])
            .unwrap();
    assert_eq!(
        key.to_pkcs8().unwrap().as_ref(),
        key.to_pkcs8v1().unwrap().as_ref()
    );
}

/// Generated keys, and malformed or mismatched inputs, against aws-lc-rs:
/// wrong-length public keys, SPKIs, and signatures, another parameter set's
/// keys and signatures, and a PKCS#8 v2 whose public key does not match.
///
/// Two refusals are rind's own, as the README lists: an SPKI or a PKCS#8
/// document with a byte after it, and a PKCS#8 v2 key whose public key does
/// not match, all of which aws-lc-rs accepts.
#[test]
fn ml_dsa_malformed() {
    use theirs::encoding::AsDer as _;

    let sets = [
        (
            &ours::signature::ML_DSA_44_SIGNING,
            &ours::signature::ML_DSA_44,
            &theirs::signature::ML_DSA_44_SIGNING,
            &theirs::signature::ML_DSA_44,
        ),
        (
            &ours::signature::ML_DSA_65_SIGNING,
            &ours::signature::ML_DSA_65,
            &theirs::signature::ML_DSA_65_SIGNING,
            &theirs::signature::ML_DSA_65,
        ),
        (
            &ours::signature::ML_DSA_87_SIGNING,
            &ours::signature::ML_DSA_87,
            &theirs::signature::ML_DSA_87_SIGNING,
            &theirs::signature::ML_DSA_87,
        ),
    ];
    let msg = b"malformed";

    // Each set's generated key pair, its raw public key, SPKI, signature,
    // and seed-form PKCS#8, from both sides.
    let keys: Vec<_> = sets
        .iter()
        .map(|&(ours_sign, _, theirs_sign, _)| {
            let ours = ours::signature::PqdsaKeyPair::generate(ours_sign).unwrap();
            let theirs = theirs::signature::PqdsaKeyPair::generate(theirs_sign).unwrap();
            assert_eq!(ours.public_key().as_ref().len(), ours_sign.public_key_len());
            assert_eq!(
                theirs.public_key().as_ref().len(),
                theirs_sign.public_key_len()
            );
            assert_ne!(ours.public_key().as_ref(), theirs.public_key().as_ref());

            // Each side's generated key loads on the other, with the same
            // public key.
            let ours_pkcs8 = ours.to_pkcs8v1().unwrap();
            let theirs_pkcs8 = theirs.to_pkcs8v1().unwrap();
            let loaded =
                theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, ours_pkcs8.as_ref())
                    .unwrap();
            assert_eq!(loaded.public_key().as_ref(), ours.public_key().as_ref());
            let loaded =
                ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, theirs_pkcs8.as_ref())
                    .unwrap();
            assert_eq!(loaded.public_key().as_ref(), theirs.public_key().as_ref());

            let mut sig = vec![0; ours_sign.signature_len()];
            assert_eq!(ours.sign(msg, &mut sig).unwrap(), sig.len());
            // A short output buffer is refused on both sides.
            let mut short = vec![0; ours_sign.signature_len() - 1];
            assert!(ours.sign(msg, &mut short).is_err());
            assert!(theirs.sign(msg, &mut short).is_err());

            let public = ours.public_key().as_ref().to_vec();
            let spki = ours.public_key().as_der().unwrap().as_ref().to_vec();
            let theirs_spki = theirs.public_key().as_der().unwrap().as_ref().to_vec();
            assert_eq!(
                ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, theirs_pkcs8.as_ref())
                    .unwrap()
                    .public_key()
                    .as_der()
                    .unwrap()
                    .as_ref(),
                &theirs_spki[..]
            );
            (public, spki, sig, theirs_pkcs8.as_ref().to_vec(), theirs)
        })
        .collect();

    for (i, &(ours_sign, ours_verify, theirs_sign, theirs_verify)) in sets.iter().enumerate() {
        let (public, spki, sig, _, _) = &keys[i];
        let verifies = |key: &[u8], sig: &[u8]| {
            let ours = ours::signature::UnparsedPublicKey::new(ours_verify, key).verify(msg, sig);
            let theirs =
                theirs::signature::UnparsedPublicKey::new(theirs_verify, key).verify(msg, sig);
            (ours.is_ok(), theirs.is_ok())
        };
        let agree = |key: &[u8], sig: &[u8]| {
            let (ours, theirs) = verifies(key, sig);
            assert_eq!(ours, theirs, "key {} sig {}", key.len(), sig.len());
            ours
        };

        assert!(agree(public, sig));
        assert!(agree(spki, sig));

        // Public keys and SPKIs a byte short, a raw key a byte long, or an
        // empty key.
        for key in [public, spki] {
            assert!(!agree(&key[..key.len() - 1], sig));
        }
        assert!(!agree(&[public, &[0][..]].concat(), sig));
        assert!(!agree(&[], sig));
        // aws-lc-rs ignores a byte after the SPKI; rind refuses it.
        assert_eq!(verifies(&[spki, &[0][..]].concat(), sig), (false, true));

        // Signatures a byte short or long, or empty.
        assert!(!agree(public, &sig[..sig.len() - 1]));
        assert!(!agree(public, &[&sig[..], &[0]].concat()));
        assert!(!agree(public, &[]));

        // Another parameter set's public key, SPKI, and signature.
        for (j, (other_public, other_spki, other_sig, other_pkcs8, other_key)) in
            keys.iter().enumerate()
        {
            if j == i {
                continue;
            }
            assert!(!agree(other_public, sig));
            assert!(!agree(other_spki, sig));
            assert!(!agree(public, other_sig));
            assert!(!agree(other_public, other_sig));
            assert!(!agree(other_spki, other_sig));

            // PKCS#8 v2: the key with its own public key loads on both.
            let (_, _, _, own_pkcs8, own_key) = &keys[i];
            let v2 = ml_dsa_pkcs8_v2(own_pkcs8, own_key.public_key().as_ref());
            let ours = ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &v2).unwrap();
            let theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &v2).unwrap();
            assert_eq!(ours.public_key().as_ref(), theirs.public_key().as_ref());
            assert_eq!(ours.public_key().as_ref(), own_key.public_key().as_ref());

            // With another key's public key, aws-lc-rs ignores it and loads
            // the private key; rind refuses the mismatch.
            let v2 = ml_dsa_pkcs8_v2(own_pkcs8, other_key.public_key().as_ref());
            let ours = ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &v2).unwrap_err();
            assert_eq!(ours.description_(), "InvalidEncoding");
            assert_eq!(ours.to_string(), "mismatched PKCS#8 public key");
            assert!(theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &v2).is_ok());

            // Another parameter set's key, with its own public key, is
            // refused on both, as in seed form.
            let v2 = ml_dsa_pkcs8_v2(other_pkcs8, other_key.public_key().as_ref());
            same_rejection(
                ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &v2),
                theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &v2),
            );

            // Another parameter set's PKCS#8 whose seed is a byte short, and
            // one cut off inside its header, are refused for the same reason.
            let short = ml_dsa_short_seed(other_pkcs8);
            for pkcs8 in [&short[..], &other_pkcs8[..10]] {
                same_rejection(
                    ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, pkcs8),
                    theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, pkcs8),
                );
            }
        }
    }

    // An Ed25519 OID whose key is one byte short, an unknown OID, and a
    // truncated ML-DSA OID. aws-lc-rs has not parsed a key, so these are
    // `InvalidEncoding`, not `WrongAlgorithm`.
    let oid_key = |oid: &[u8], private_key: &[u8]| {
        der(
            0x30,
            &[
                der(0x02, &[0]),
                der(0x30, &der(0x06, oid)),
                der(0x04, private_key),
            ]
            .concat(),
        )
    };
    let ed25519_oid = [0x2b, 0x65, 0x70];
    let mldsa_oid_prefix = [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03];
    for pkcs8 in [
        oid_key(&ed25519_oid, &der(0x04, &[0; 31])),
        oid_key(
            &[&mldsa_oid_prefix[..], &[0x7f]].concat(),
            &der(0x04, &[0; 32]),
        ),
        oid_key(&mldsa_oid_prefix, &der(0x04, &[0; 32])),
    ] {
        same_rejection(
            ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_44_SIGNING, &pkcs8),
            theirs::signature::PqdsaKeyPair::from_pkcs8(
                &theirs::signature::ML_DSA_44_SIGNING,
                &pkcs8,
            ),
        );
    }

    // A byte after a complete document. aws-lc-rs ignores it.
    let (_, _, _, pkcs8_44, _) = &keys[0];
    let trailed = [pkcs8_44.as_slice(), &[0]].concat();
    assert_eq!(
        (
            ours::signature::PqdsaKeyPair::from_pkcs8(
                &ours::signature::ML_DSA_44_SIGNING,
                &trailed
            )
            .is_ok(),
            theirs::signature::PqdsaKeyPair::from_pkcs8(
                &theirs::signature::ML_DSA_44_SIGNING,
                &trailed
            )
            .is_ok(),
        ),
        (false, true)
    );
    // The same trailing byte on ML-DSA-65, loaded as ML-DSA-44. aws-lc-rs
    // still parses the key and then refuses the size. rind refuses the
    // trailing byte first.
    let (_, _, _, pkcs8_65, _) = &keys[1];
    let trailed = [pkcs8_65.as_slice(), &[0]].concat();
    let ours =
        ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_44_SIGNING, &trailed)
            .unwrap_err();
    let theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(
        &theirs::signature::ML_DSA_44_SIGNING,
        &trailed,
    )
    .unwrap_err();
    assert_eq!(ours.description_(), "InvalidEncoding");
    assert_eq!(theirs.description_(), "Unspecified");
}

/// A seed-form PKCS#8 v1 document with its 32-byte seed cut to 31.
fn ml_dsa_short_seed(seed_form: &[u8]) -> Vec<u8> {
    let header = ml_dsa_pkcs8_header(seed_form);
    let seed = &seed_form[seed_form.len() - 32..];
    let choice = der(0x80, &seed[..31]);
    der(0x30, &[header, &der(0x04, &choice)].concat())
}

/// A positive INTEGER whose magnitude is `mag`.
fn der_uint(mag: &[u8]) -> Vec<u8> {
    let body = if mag.first().is_some_and(|b| *b >= 0x80) {
        [&[0u8][..], mag].concat()
    } else {
        mag.to_vec()
    };
    der(0x02, &body)
}

fn der_split(input: &[u8]) -> Option<(u8, &[u8], &[u8])> {
    let (len, header) = match *input.get(1)? {
        n @ 0..=0x7f => (usize::from(n), 2),
        0x81 => (usize::from(*input.get(2)?), 3),
        0x82 => (
            usize::from(u16::from_be_bytes([*input.get(2)?, *input.get(3)?])),
            4,
        ),
        _ => return None,
    };
    let rest = input.get(header..)?;
    let (body, rest) = rest.split_at_checked(len)?;
    Some((input[0], body, rest))
}

/// A seed-form PKCS#8 v1 document rewritten as v2 (RFC 5958) carrying
/// `public_key`.
fn ml_dsa_pkcs8_v2(seed_form: &[u8], public_key: &[u8]) -> Vec<u8> {
    // The v1 body after its version: the algorithm identifier and the
    // private key.
    let rest = &seed_form[2 + 3..];
    let public_key = der(0x81, &[&[0][..], public_key].concat());
    der(0x30, &[&[0x02, 0x01, 0x01][..], rest, &public_key].concat())
}
