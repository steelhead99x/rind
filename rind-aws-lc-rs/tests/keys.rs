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

    // Each side loads the other's ML-DSA keys, from a seed, PKCS#8, or the
    // expanded key, and verifies the other's signatures. ML-DSA hedges its
    // signatures with fresh randomness, so they differ.
    #[test]
    fn ml_dsa(set in 0..3usize, seed in any::<[u8; 32]>(), msg in vec(any::<u8>(), 0..100)) {
        let ours_sign = [&ours::signature::ML_DSA_44_SIGNING, &ours::signature::ML_DSA_65_SIGNING, &ours::signature::ML_DSA_87_SIGNING][set];
        let theirs_sign = [&theirs::signature::ML_DSA_44_SIGNING, &theirs::signature::ML_DSA_65_SIGNING, &theirs::signature::ML_DSA_87_SIGNING][set];
        let ours_verify = [&ours::signature::ML_DSA_44, &ours::signature::ML_DSA_65, &ours::signature::ML_DSA_87][set];
        let theirs_verify = [&theirs::signature::ML_DSA_44, &theirs::signature::ML_DSA_65, &theirs::signature::ML_DSA_87][set];
        prop_assert_eq!(ours_sign.signature_len(), theirs_sign.signature_len());
        prop_assert_eq!(ours_sign.public_key_len(), theirs_sign.public_key_len());
        prop_assert_eq!(ours_sign.seed_len(), theirs_sign.seed_len());

        let ours_pair = ours::signature::PqdsaKeyPair::from_seed(ours_sign, &seed).unwrap();
        let theirs_pair = theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, &seed).unwrap();
        prop_assert_eq!(ours_pair.public_key().as_ref(), theirs_pair.public_key().as_ref());
        prop_assert_eq!(
            ours_pair.public_key().as_der().unwrap().as_ref().to_vec(),
            theirs_pair.public_key().as_der().unwrap().as_ref().to_vec()
        );
        let theirs_doc = theirs_pair.to_pkcs8v1().unwrap();
        let ours_doc = ours_pair.to_pkcs8v1().unwrap();
        prop_assert_eq!(ours_doc.as_ref(), theirs_doc.as_ref());
        let loaded = ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, theirs_doc.as_ref()).unwrap();
        prop_assert_eq!(loaded.public_key().as_ref(), theirs_pair.public_key().as_ref());
        let other = [&ours::signature::ML_DSA_44_SIGNING, &ours::signature::ML_DSA_65_SIGNING, &ours::signature::ML_DSA_87_SIGNING][(set + 1) % 3];
        prop_assert!(ours::signature::PqdsaKeyPair::from_pkcs8(other, theirs_doc.as_ref()).is_err());

        // The expanded key loads without its seed, so neither encodes it.
        let raw: theirs::encoding::PqdsaPrivateKeyRaw = theirs::encoding::AsRawBytes::as_raw_bytes(&theirs_pair.private_key()).unwrap();
        let ours_raw = ours::signature::PqdsaKeyPair::from_raw_private_key(ours_sign, raw.as_ref()).unwrap();
        let theirs_raw = theirs::signature::PqdsaKeyPair::from_raw_private_key(theirs_sign, raw.as_ref()).unwrap();
        prop_assert_eq!(ours_raw.public_key().as_ref(), theirs_pair.public_key().as_ref());
        prop_assert!(ours_raw.to_pkcs8v1().is_err());
        prop_assert!(theirs_raw.to_pkcs8v1().is_err());
        prop_assert!(ours::signature::PqdsaKeyPair::from_raw_private_key(ours_sign, &raw.as_ref()[1..]).is_err());

        let spki = theirs_pair.public_key().as_der().unwrap();
        for signer in [&ours_pair, &ours_raw] {
            let mut sig = vec![0; ours_sign.signature_len() + 1];
            prop_assert_eq!(signer.sign(&msg, &mut sig).unwrap(), ours_sign.signature_len());
            let sig = &sig[..ours_sign.signature_len()];
            for key in [theirs_pair.public_key().as_ref(), spki.as_ref()] {
                let key = theirs::signature::UnparsedPublicKey::new(theirs_verify, key);
                prop_assert!(key.verify(&msg, sig).is_ok());
                prop_assert!(key.verify(b"other", sig).is_err());
            }
        }
        prop_assert!(ours_pair.sign(&msg, &mut vec![0; ours_sign.signature_len() - 1]).is_err());

        let mut sig = vec![0; theirs_sign.signature_len()];
        theirs_pair.sign(&msg, &mut sig).unwrap();
        for key in [theirs_pair.public_key().as_ref(), spki.as_ref()] {
            let key = ours::signature::UnparsedPublicKey::new(ours_verify, key);
            prop_assert!(key.verify(&msg, &sig).is_ok());
            prop_assert!(key.verify(b"other", &sig).is_err());
            prop_assert!(key.verify(&msg, &sig[1..]).is_err());
            let parsed = key.parse().unwrap();
            prop_assert!(parsed.verify_sig(&msg, &sig).is_ok());
            let digest = ours::digest::digest(&ours::digest::SHA256, &msg);
            prop_assert!(parsed.verify_digest_sig(&digest, &sig).is_err());
        }
        prop_assert!(ours::signature::ParsedPublicKey::new(ours_verify, &theirs_pair.public_key().as_ref()[1..]).is_err());
    }

    #[test]
    fn kem(set in 0..3usize) {
        let (ours_alg, theirs_alg) = [
            (&ours::kem::ML_KEM_512, &theirs::kem::ML_KEM_512),
            (&ours::kem::ML_KEM_768, &theirs::kem::ML_KEM_768),
            (&ours::kem::ML_KEM_1024, &theirs::kem::ML_KEM_1024),
        ][set];
        let ours_key = ours::kem::DecapsulationKey::generate(ours_alg).unwrap();
        let theirs_key = theirs::kem::DecapsulationKey::generate(theirs_alg).unwrap();

        let ours_public = ours_key.encapsulation_key().unwrap().key_bytes().unwrap();
        let peer = theirs::kem::EncapsulationKey::new(theirs_alg, ours_public.as_ref()).unwrap();
        let (ciphertext, secret) = peer.encapsulate().unwrap();
        let ours_secret = ours_key.decapsulate(ours::kem::Ciphertext::from(ciphertext.as_ref())).unwrap();
        prop_assert_eq!(ours_secret.as_ref(), secret.as_ref());

        let theirs_public = theirs_key.encapsulation_key().unwrap().key_bytes().unwrap();
        let peer = ours::kem::EncapsulationKey::new(ours_alg, theirs_public.as_ref()).unwrap();
        let (ciphertext, secret) = peer.encapsulate().unwrap();
        let theirs_secret = theirs_key
            .decapsulate(theirs::kem::Ciphertext::from(ciphertext.as_ref()))
            .unwrap();
        prop_assert_eq!(theirs_secret.as_ref(), secret.as_ref());

        use ours::kem::AlgorithmIdentifier as _;
        use theirs::kem::AlgorithmIdentifier as _;
        prop_assert_eq!(ours_alg.id().nid(), theirs_alg.id().nid());
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
    for len in [0, 31, 33] {
        let seed = vec![0; len];
        assert!(
            ours::signature::PqdsaKeyPair::from_seed(&ours::signature::ML_DSA_65_SIGNING, &seed)
                .is_err()
        );
        assert!(
            theirs::signature::PqdsaKeyPair::from_seed(
                &theirs::signature::ML_DSA_65_SIGNING,
                &seed
            )
            .is_err()
        );
    }
    for alg in 0..4 {
        let ours_key =
            ours::agreement::PrivateKey::generate(agreement_algorithms!(ours)[alg]).unwrap();
        let peer =
            ours::agreement::UnparsedPublicKey::new(agreement_algorithms!(ours)[alg], [4u8; 5]);
        assert!(ours::agreement::agree(&ours_key, peer, (), |_| Ok(())).is_err());
    }
    // A compressed ECDSA public key whose x is no field element, or that is
    // too short, which both refuse to decompress.
    for (ours_alg, theirs_alg, len) in [
        (
            &ours::signature::ECDSA_P256_SHA256_ASN1,
            &theirs::signature::ECDSA_P256_SHA256_ASN1,
            32,
        ),
        (
            &ours::signature::ECDSA_P384_SHA384_ASN1,
            &theirs::signature::ECDSA_P384_SHA384_ASN1,
            48,
        ),
        (
            &ours::signature::ECDSA_P521_SHA512_ASN1,
            &theirs::signature::ECDSA_P521_SHA512_ASN1,
            66,
        ),
    ] {
        for prefix in [0x02, 0x03] {
            for key in [[&[prefix][..], &vec![0xff; len]].concat(), vec![prefix, 1]] {
                assert!(ours::signature::ParsedPublicKey::new(ours_alg, &key).is_err());
                assert!(theirs::signature::ParsedPublicKey::new(theirs_alg, &key).is_err());
            }
        }
    }
}

/// ML-DSA refusal names aws-lc-rs 1.19.0 uses, beyond the `is_err` checks in
/// `ml_dsa` and `refused`.
#[cfg(not(any(miri, target_family = "wasm")))]
#[test]
fn ml_dsa_refusal_kind() {
    use theirs::encoding::AsRawBytes;

    fn same<T: core::fmt::Debug, U: core::fmt::Debug>(
        ours: Result<T, ours::error::KeyRejected>,
        theirs: Result<U, theirs::error::KeyRejected>,
    ) {
        assert_eq!(
            ours.unwrap_err().description_(),
            theirs.unwrap_err().description_()
        );
    }
    let ours_sign = &ours::signature::ML_DSA_44_SIGNING;
    let theirs_sign = &theirs::signature::ML_DSA_44_SIGNING;
    let other =
        theirs::signature::PqdsaKeyPair::from_seed(&theirs::signature::ML_DSA_65_SIGNING, &[4; 32])
            .unwrap();
    let pkcs8 = other.to_pkcs8v1().unwrap();
    same(
        ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, pkcs8.as_ref()),
        theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, pkcs8.as_ref()),
    );
    let raw = AsRawBytes::as_raw_bytes(&other.private_key()).unwrap();
    same(
        ours::signature::PqdsaKeyPair::from_raw_private_key(ours_sign, raw.as_ref()),
        theirs::signature::PqdsaKeyPair::from_raw_private_key(theirs_sign, raw.as_ref()),
    );
    let public = other.public_key().as_ref();
    let short = &public[..public.len() - 1];
    same(
        ours::signature::ParsedPublicKey::new(&ours::signature::ML_DSA_65, short),
        theirs::signature::ParsedPublicKey::new(&theirs::signature::ML_DSA_65, short),
    );
    let ed = theirs::signature::Ed25519KeyPair::from_seed_unchecked(&[3; 32])
        .unwrap()
        .to_pkcs8v1()
        .unwrap();
    same(
        ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, ed.as_ref()),
        theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, ed.as_ref()),
    );
    let oid65 = [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12];
    let short_seed = der(
        0x30,
        &[
            der(0x02, &[0]),
            der(0x30, &der(0x06, &oid65)),
            der(0x04, &der(0x80, &[0; 31])),
        ]
        .concat(),
    );
    same(
        ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &short_seed),
        theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &short_seed),
    );
    let good = theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, &[6; 32]).unwrap();
    let good_raw = AsRawBytes::as_raw_bytes(&good.private_key()).unwrap();
    let mut bad = good_raw.as_ref().to_vec();
    bad[..32].fill(0);
    same(
        ours::signature::PqdsaKeyPair::from_raw_private_key(ours_sign, &bad),
        theirs::signature::PqdsaKeyPair::from_raw_private_key(theirs_sign, &bad),
    );
    let mut trailed = pkcs8.as_ref().to_vec();
    trailed.push(0);
    // Bytes after the document are unread. The key is another parameter set,
    // so both then report `Unspecified`.
    same(
        ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &trailed),
        theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &trailed),
    );
    assert_eq!(
        theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &trailed)
            .unwrap_err()
            .description_(),
        "Unspecified"
    );
}

/// Every ML-DSA refusal aws-lc-rs 1.19.0 names for a key that is not the
/// requested parameter set, including the cases that used to differ.
#[cfg(not(any(miri, target_family = "wasm")))]
#[test]
fn ml_dsa_every_refusal() {
    let ours44 = &ours::signature::ML_DSA_44_SIGNING;
    let theirs44 = &theirs::signature::ML_DSA_44_SIGNING;
    let ours65 = &ours::signature::ML_DSA_65_SIGNING;
    let theirs65 = &theirs::signature::ML_DSA_65_SIGNING;
    let seed = [9u8; 32];

    let kind = |doc: &[u8], ours_alg, theirs_alg, expected: &str| {
        let ours = ours::signature::PqdsaKeyPair::from_pkcs8(ours_alg, doc).unwrap_err();
        let theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_alg, doc).unwrap_err();
        assert_eq!(theirs.description_(), expected, "aws-lc-rs");
        assert_eq!(ours.description_(), expected, "rind");
    };
    // A key of a type rind cannot back is refused from its OID alone, so a
    // malformed one is `WrongAlgorithm` where aws-lc-rs may name a parse error.
    let unbacked = |doc: &[u8], theirs_expected: &str| {
        let ours = ours::signature::PqdsaKeyPair::from_pkcs8(ours44, doc).unwrap_err();
        let theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(theirs44, doc).unwrap_err();
        assert_eq!(theirs.description_(), theirs_expected, "aws-lc-rs");
        assert_eq!(ours.description_(), "WrongAlgorithm", "rind");
    };
    let loaded = |doc: &[u8], ours_alg, theirs_alg| {
        let ours = ours::signature::PqdsaKeyPair::from_pkcs8(ours_alg, doc).unwrap();
        let theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_alg, doc).unwrap();
        assert_eq!(ours.public_key().as_ref(), theirs.public_key().as_ref());
    };

    // ML-DSA-65 seed plus a trailing byte. As its own set, aws-lc loads it.
    // As ML-DSA-44, both report `Unspecified`.
    let oid65 = [0x60u8, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12];
    let trailed_seed = [der(0x80, &seed), vec![0x00]].concat();
    let seed_tail = pkcs8_doc(0, &oid65, &[], &trailed_seed, None);
    loaded(&seed_tail, ours65, theirs65);
    kind(&seed_tail, ours44, theirs44, "Unspecified");
    let mut after_doc = seed_tail.clone();
    after_doc.push(0);
    loaded(&after_doc, ours65, theirs65);
    kind(&after_doc, ours44, theirs44, "Unspecified");

    // A v2 public key is ignored, matched or not.
    let v2 = pkcs8_doc(1, &oid65, &[], &der(0x80, &seed), Some(&[0x00, 0x01]));
    loaded(&v2, ours65, theirs65);

    // A byte after a SubjectPublicKeyInfo is unread.
    let public = theirs::signature::PqdsaKeyPair::from_seed(theirs65, &seed)
        .unwrap()
        .public_key()
        .as_ref()
        .to_vec();
    let mut spki = der(
        0x30,
        &[
            der(0x30, &der(0x06, &oid65)),
            der(0x03, &[&[0], public.as_slice()].concat()),
        ]
        .concat(),
    );
    spki.push(0);
    ours::signature::ParsedPublicKey::new(&ours::signature::ML_DSA_65, &spki).unwrap();
    theirs::signature::ParsedPublicKey::new(&theirs::signature::ML_DSA_65, &spki).unwrap();

    // RSA-1024 from Wycheproof, below the 2048 bits rind can back. Consistent
    // components are `WrongAlgorithm` in both. A corrupted coefficient is
    // `InvalidEncoding` in aws-lc-rs, and `WrongAlgorithm` here, decided from
    // the modulus length.
    let rsa = rsa1024_pkcs8();
    kind(&rsa, ours44, theirs44, "WrongAlgorithm");
    let mut bad_rsa = pkcs1_of(&rsa);
    let last = bad_rsa.len() - 1;
    bad_rsa[last] ^= 0xff;
    let bad_rsa = pkcs8_doc(
        0,
        &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01],
        &[0x05, 0x00],
        &bad_rsa,
        None,
    );
    unbacked(&bad_rsa, "InvalidEncoding");
    let v2_rsa = pkcs8_doc(
        1,
        &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01],
        &[0x05, 0x00],
        &pkcs1_of(&rsa),
        Some(&[0x00, 0xff]),
    );
    kind(&v2_rsa, ours44, theirs44, "InvalidEncoding");

    // RSASSA-PSS. NULL parameters do not parse. An explicit SHA-256 does.
    // A v2 public key is ignored. An inconsistent key does not parse in
    // aws-lc-rs; this 1024-bit one is refused from its modulus length here.
    let pss_oid = [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a];
    let pkcs1 = pkcs1_of(&rsa);
    kind(
        &pkcs8_doc(0, &pss_oid, &[0x05, 0x00], &pkcs1, None),
        ours44,
        theirs44,
        "InvalidEncoding",
    );
    let sha256 = der(
        0x30,
        &[
            der(
                0x06,
                &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01],
            ),
            der(0x05, &[]),
        ]
        .concat(),
    );
    let pss_params = der(0x30, &der(0xa0, &sha256));
    kind(
        &pkcs8_doc(0, &pss_oid, &pss_params, &pkcs1, None),
        ours44,
        theirs44,
        "WrongAlgorithm",
    );
    kind(
        &pkcs8_doc(1, &pss_oid, &pss_params, &pkcs1, Some(&[0x00, 0x01])),
        ours44,
        theirs44,
        "WrongAlgorithm",
    );
    let mut bad_pss = pkcs1.clone();
    let last = bad_pss.len() - 1;
    bad_pss[last] ^= 0xff;
    unbacked(
        &pkcs8_doc(0, &pss_oid, &pss_params, &bad_pss, None),
        "InvalidEncoding",
    );

    // P-256. A 31-byte scalar is in range. The order is not. A public point
    // other than scalar * G is not.
    let p256 = [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07];
    kind(
        &ec_pkcs8(&p256, &[0x01; 31], None),
        ours44,
        theirs44,
        "WrongAlgorithm",
    );
    let order = [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63,
        0x25, 0x51,
    ];
    kind(
        &ec_pkcs8(&p256, &order, None),
        ours44,
        theirs44,
        "InvalidEncoding",
    );
    let generated = theirs::signature::EcdsaKeyPair::generate(
        &theirs::signature::ECDSA_P256_SHA256_FIXED_SIGNING,
    )
    .unwrap()
    .to_pkcs8v1()
    .unwrap();
    let mut mismatched = generated.as_ref().to_vec();
    let last = mismatched.len() - 1;
    mismatched[last] ^= 0xff;
    kind(&mismatched, ours44, theirs44, "InvalidEncoding");

    // Curves aws-lc parses and rind cannot back.
    let k1_g = [
        0x04, 0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62, 0x95, 0xce, 0x87,
        0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16,
        0xf8, 0x17, 0x98, 0x48, 0x3a, 0xda, 0x77, 0x26, 0xa3, 0xc4, 0x65, 0x5d, 0xa4, 0xfb, 0xfc,
        0x0e, 0x11, 0x08, 0xa8, 0xfd, 0x17, 0xb4, 0x48, 0xa6, 0x85, 0x54, 0x19, 0x9c, 0x47, 0xd0,
        0x8f, 0xfb, 0x10, 0xd4, 0xb8,
    ];
    kind(
        &ec_pkcs8(&[0x2b, 0x81, 0x04, 0x00, 0x0a], &[1], Some(&k1_g)),
        ours44,
        theirs44,
        "WrongAlgorithm",
    );
    let mut off = k1_g;
    off[1] ^= 0xff;
    unbacked(
        &ec_pkcs8(&[0x2b, 0x81, 0x04, 0x00, 0x0a], &[1], Some(&off)),
        "InvalidEncoding",
    );
    unbacked(
        &ec_pkcs8(&[0x2b, 0x81, 0x04, 0x00, 0x0a], &[2], Some(&k1_g)),
        "InvalidEncoding",
    );
    let mut compressed = vec![0x02];
    compressed.extend_from_slice(&k1_g[1..33]);
    kind(
        &ec_pkcs8(&[0x2b, 0x81, 0x04, 0x00, 0x0a], &[1], Some(&compressed)),
        ours44,
        theirs44,
        "WrongAlgorithm",
    );
    let p224_g = [
        0x04, 0xb7, 0x0e, 0x0c, 0xbd, 0x6b, 0xb4, 0xbf, 0x7f, 0x32, 0x13, 0x90, 0xb9, 0x4a, 0x03,
        0xc1, 0xd3, 0x56, 0xc2, 0x11, 0x22, 0x34, 0x32, 0x80, 0xd6, 0x11, 0x5c, 0x1d, 0x21, 0xbd,
        0x37, 0x63, 0x88, 0xb5, 0xf7, 0x23, 0xfb, 0x4c, 0x22, 0xdf, 0xe6, 0xcd, 0x43, 0x75, 0xa0,
        0x5a, 0x07, 0x47, 0x64, 0x44, 0xd5, 0x81, 0x99, 0x85, 0x00, 0x7e, 0x34,
    ];
    kind(
        &ec_pkcs8(&[0x2b, 0x81, 0x04, 0x00, 0x21], &[1], Some(&p224_g)),
        ours44,
        theirs44,
        "WrongAlgorithm",
    );
    let bp_g = [
        0x04, 0x8b, 0xd2, 0xae, 0xb9, 0xcb, 0x7e, 0x57, 0xcb, 0x2c, 0x4b, 0x48, 0x2f, 0xfc, 0x81,
        0xb7, 0xaf, 0xb9, 0xde, 0x27, 0xe1, 0xe3, 0xbd, 0x23, 0xc2, 0x3a, 0x44, 0x53, 0xbd, 0x9a,
        0xce, 0x32, 0x62, 0x54, 0x7e, 0xf8, 0x35, 0xc3, 0xda, 0xc4, 0xfd, 0x97, 0xf8, 0x46, 0x1a,
        0x14, 0x61, 0x1d, 0xc9, 0xc2, 0x77, 0x45, 0x13, 0x2d, 0xed, 0x8e, 0x54, 0x5c, 0x1d, 0x54,
        0xc7, 0x2f, 0x04, 0x69, 0x97,
    ];
    kind(
        &ec_pkcs8(
            &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x07],
            &[1],
            Some(&bp_g),
        ),
        ours44,
        theirs44,
        "WrongAlgorithm",
    );

    // DSA, which rind cannot back. aws-lc checks bounds, not primality:
    // x = 0 and x = q are out of range there.
    kind(&dsa_pkcs8(&[1]), ours44, theirs44, "WrongAlgorithm");
    unbacked(&dsa_pkcs8(&[0]), "InvalidEncoding");
    let mut q = vec![0x00, 0x80];
    q.extend_from_slice(&[0; 18]);
    q.push(0x01);
    unbacked(&dsa_pkcs8(&q), "InvalidEncoding");

    // An Ed25519 document with a trailing byte still parses.
    let ed = theirs::signature::Ed25519KeyPair::from_seed_unchecked(&[3; 32])
        .unwrap()
        .to_pkcs8v1()
        .unwrap();
    let mut ed = ed.as_ref().to_vec();
    ed.push(0);
    kind(&ed, ours44, theirs44, "WrongAlgorithm");
}

fn pkcs8_doc(
    version: u8,
    oid: &[u8],
    parameters: &[u8],
    private_key: &[u8],
    public_key: Option<&[u8]>,
) -> Vec<u8> {
    let mut body = der(0x02, &[version]);
    body.extend(der(0x30, &[der(0x06, oid), parameters.to_vec()].concat()));
    body.extend(der(0x04, private_key));
    if let Some(public_key) = public_key {
        body.extend(der(0x81, public_key));
    }
    der(0x30, &body)
}

fn ec_pkcs8(curve: &[u8], scalar: &[u8], point: Option<&[u8]>) -> Vec<u8> {
    let mut sec1 = der(0x02, &[1]);
    sec1.extend(der(0x04, scalar));
    if let Some(point) = point {
        sec1.extend(der(0xa1, &der(0x03, &[&[0], point].concat())));
    }
    pkcs8_doc(
        0,
        &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01],
        &der(0x06, curve),
        &der(0x30, &sec1),
        None,
    )
}

fn dsa_pkcs8(x: &[u8]) -> Vec<u8> {
    let mut p = vec![0u8; 128];
    p[0] = 0x80;
    p[127] = 0x01;
    let mut q = vec![0u8; 20];
    q[0] = 0x80;
    q[19] = 0x01;
    // A magnitude whose top bit is set needs a leading zero so the INTEGER
    // is positive.
    let params = der(
        0x30,
        &[
            der(0x02, &[&[0], p.as_slice()].concat()),
            der(0x02, &[&[0], q.as_slice()].concat()),
            der(0x02, &[2]),
        ]
        .concat(),
    );
    pkcs8_doc(
        0,
        &[0x2a, 0x86, 0x48, 0xce, 0x38, 0x04, 0x01],
        &params,
        &der(0x02, x),
        None,
    )
}

fn rsa1024_pkcs8() -> Vec<u8> {
    let path = format!(
        "{}/../thirdparty/vectors/wycheproof/testvectors_v1/rsa_pkcs1_1024_sig_gen_test.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let value: serde_json::Value =
        serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
    hex::decode(value["testGroups"][0]["privateKeyPkcs8"].as_str().unwrap()).unwrap()
}

fn pkcs1_of(pkcs8: &[u8]) -> Vec<u8> {
    let (_, body, _) = tlv(pkcs8).unwrap();
    let (_, _, rest) = tlv(body).unwrap();
    let (_, _, rest) = tlv(rest).unwrap();
    let (tag, key, _) = tlv(rest).unwrap();
    assert_eq!(tag, 0x04);
    key.to_vec()
}

fn tlv(input: &[u8]) -> Option<(u8, &[u8], &[u8])> {
    let tag = *input.first()?;
    let (len, header): (usize, usize) = match *input.get(1)? {
        len @ 0..=0x7f => (len as usize, 2),
        0x81 => ((*input.get(2)?) as usize, 3),
        0x82 => {
            let bytes = input.get(2..4)?;
            (u16::from_be_bytes([bytes[0], bytes[1]]) as usize, 4)
        }
        _ => return None,
    };
    let end = header.checked_add(len)?;
    Some((tag, input.get(header..end)?, input.get(end..)?))
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
