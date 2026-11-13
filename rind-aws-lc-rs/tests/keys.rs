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
