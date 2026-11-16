#![no_main]

//! Signing against aws-lc: Ed25519 from any seed, ECDSA from any scalar, and
//! RSA under every scheme and any PSS salt length, each over any message.
//!
//! Ed25519 and RSA PKCS#1 v1.5 signatures must match aws-lc-rs's byte for
//! byte. ECDSA and PSS signatures are randomized, so aws-lc verifies them;
//! PSS through aws-lc-sys, since aws-lc-rs takes a salt length only in a
//! `'static` algorithm. The RSA keys are the test keys and one rind generates
//! as the target starts, which aws-lc-rs must load as the same key.

use std::sync::LazyLock;

use aws_lc_rs::rand::SystemRandom;
use aws_lc_rs::signature::{self as theirs, KeyPair as _, UnparsedPublicKey};
use aws_lc_rs::{agreement, digest};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::rsa::{PssSaltLength, SigningAlgorithm as RsaSigningAlgorithm};
use rind::{ecdsa, ed25519, rsa as our_rsa};

#[derive(Arbitrary, Debug)]
enum Input {
    Ed25519 {
        seed: [u8; 32],
        message: Vec<u8>,
    },
    /// The case `case` indexes in [`ECDSA`], and the first bytes of `scalar`
    /// its curve's scalar takes.
    Ecdsa {
        case: u8,
        scalar: [u8; 66],
        message: Vec<u8>,
    },
    /// The key `key` indexes in [`RSA_KEYS`].
    Rsa {
        key: u8,
        scheme: RsaScheme,
        message: Vec<u8>,
    },
}

#[derive(Arbitrary, Debug)]
enum RsaScheme {
    Pkcs1(Hash),
    Pss(Hash, Salt),
}

#[derive(Arbitrary, Debug, Clone, Copy)]
enum Hash {
    Sha256,
    Sha384,
    Sha512,
}

/// A PSS salt length.
#[derive(Arbitrary, Debug)]
enum Salt {
    /// The hash's length, as the `rsa::sign::PSS_*` constants use.
    Hash,
    Max,
    Custom(u16),
}

fuzz_target!(|input: Input| match input {
    Input::Ed25519 { seed, message } => {
        let theirs = theirs::Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
        let ours = ed25519::KeyPair::from_seed(&seed).unwrap();
        assert_eq!(ours.public_key().as_ref(), theirs.public_key().as_ref());
        assert_eq!(ours.sign(&message).as_ref(), theirs.sign(&message).as_ref());
    }
    Input::Ecdsa {
        case,
        mut scalar,
        message,
    } => ecdsa(
        &ECDSA[usize::from(case) % ECDSA.len()],
        &mut scalar,
        &message
    ),
    Input::Rsa {
        key,
        scheme,
        message,
    } => rsa(
        &RSA_KEYS[usize::from(key) % RSA_KEYS.len()],
        &scheme,
        &message
    ),
});

/// An ECDSA signing algorithm, the hash `sign_digest` takes the message's
/// digest under, or `None` to sign the message, and aws-lc-rs's verification
/// algorithm for the two.
struct EcdsaCase {
    curve: Curve,
    ours: &'static ecdsa::SigningAlgorithm,
    digest: Option<&'static rind::digest::Algorithm>,
    theirs: &'static theirs::EcdsaVerificationAlgorithm,
}

/// aws-lc-rs's agreement algorithm on a curve, which computes a scalar's
/// public key, and the scalar's length.
type Curve = (&'static agreement::Algorithm, usize);

const P256: Curve = (&agreement::ECDH_P256, 32);
const P384: Curve = (&agreement::ECDH_P384, 48);
const P521: Curve = (&agreement::ECDH_P521, 66);

macro_rules! ecdsa {
    ($curve:ident, $ours:ident, $digest:expr, $theirs:ident) => {
        EcdsaCase {
            curve: $curve,
            ours: &ecdsa::sign::$ours,
            digest: $digest,
            theirs: &theirs::$theirs,
        }
    };
}

const ECDSA: [EcdsaCase; 20] = {
    use rind::digest::{SHA256, SHA384, SHA512};
    [
        ecdsa!(P256, P256_SHA256_ASN1, None, ECDSA_P256_SHA256_ASN1),
        ecdsa!(P256, P256_SHA256_FIXED, None, ECDSA_P256_SHA256_FIXED),
        ecdsa!(P384, P384_SHA384_ASN1, None, ECDSA_P384_SHA384_ASN1),
        ecdsa!(P384, P384_SHA384_FIXED, None, ECDSA_P384_SHA384_FIXED),
        ecdsa!(P521, P521_SHA512_ASN1, None, ECDSA_P521_SHA512_ASN1),
        ecdsa!(P521, P521_SHA512_FIXED, None, ECDSA_P521_SHA512_FIXED),
        // aws-lc-rs verifies a fixed-width P-256 or P-384 signature only
        // under the curve's own hash.
        ecdsa!(
            P256,
            P256_SHA256_ASN1,
            Some(&SHA256),
            ECDSA_P256_SHA256_ASN1
        ),
        ecdsa!(
            P256,
            P256_SHA256_ASN1,
            Some(&SHA384),
            ECDSA_P256_SHA384_ASN1
        ),
        ecdsa!(
            P256,
            P256_SHA256_ASN1,
            Some(&SHA512),
            ECDSA_P256_SHA512_ASN1
        ),
        ecdsa!(
            P256,
            P256_SHA256_FIXED,
            Some(&SHA256),
            ECDSA_P256_SHA256_FIXED
        ),
        ecdsa!(
            P384,
            P384_SHA384_ASN1,
            Some(&SHA256),
            ECDSA_P384_SHA256_ASN1
        ),
        ecdsa!(
            P384,
            P384_SHA384_ASN1,
            Some(&SHA384),
            ECDSA_P384_SHA384_ASN1
        ),
        ecdsa!(
            P384,
            P384_SHA384_ASN1,
            Some(&SHA512),
            ECDSA_P384_SHA512_ASN1
        ),
        ecdsa!(
            P384,
            P384_SHA384_FIXED,
            Some(&SHA384),
            ECDSA_P384_SHA384_FIXED
        ),
        ecdsa!(
            P521,
            P521_SHA512_ASN1,
            Some(&SHA256),
            ECDSA_P521_SHA256_ASN1
        ),
        ecdsa!(
            P521,
            P521_SHA512_ASN1,
            Some(&SHA384),
            ECDSA_P521_SHA384_ASN1
        ),
        ecdsa!(
            P521,
            P521_SHA512_ASN1,
            Some(&SHA512),
            ECDSA_P521_SHA512_ASN1
        ),
        ecdsa!(
            P521,
            P521_SHA512_FIXED,
            Some(&SHA256),
            ECDSA_P521_SHA256_FIXED
        ),
        ecdsa!(
            P521,
            P521_SHA512_FIXED,
            Some(&SHA384),
            ECDSA_P521_SHA384_FIXED
        ),
        ecdsa!(
            P521,
            P521_SHA512_FIXED,
            Some(&SHA512),
            ECDSA_P521_SHA512_FIXED
        ),
    ]
};

/// rind signs `message` with the key of `scalar`, whose public key aws-lc
/// computes, and aws-lc-rs verifies the signature.
fn ecdsa(case: &EcdsaCase, scalar: &mut [u8; 66], message: &[u8]) {
    let (curve, scalar_len) = case.curve;
    let scalar = &mut scalar[..scalar_len];
    // P-521's order is under 2^521, so clearing the top byte's other seven
    // bits keeps most scalars in range.
    if scalar_len == 66 {
        scalar[0] &= 1;
    }
    // `fuzz::keys` checks that both refuse the same scalars.
    let Ok(theirs) = agreement::PrivateKey::from_private_key(curve, scalar) else {
        return;
    };
    let point = theirs.compute_public_key().unwrap();
    let ours = ecdsa::KeyPair::from_scalar_and_public_key(case.ours, scalar, point.as_ref())
        .expect("refused a key with aws-lc's public key");
    let signature = match case.digest {
        None => ours.sign(message),
        Some(hash) => ours.sign_digest(&rind::digest::digest(hash, message)),
    }
    .unwrap();
    UnparsedPublicKey::new(case.theirs, point.as_ref())
        .verify(message, signature.as_ref())
        .expect("aws-lc-rs refused rind's signature");
}

/// A test key, loaded by both.
struct RsaKey {
    name: String,
    ours: our_rsa::KeyPair,
    theirs: aws_lc_rs::rsa::KeyPair,
}

static RSA_KEYS: LazyLock<Vec<RsaKey>> = LazyLock::new(|| {
    let pkcs8 = |name: &str, der: &[u8]| RsaKey {
        name: name.into(),
        ours: our_rsa::KeyPair::from_pkcs8(der).unwrap(),
        theirs: aws_lc_rs::rsa::KeyPair::from_pkcs8(der).unwrap(),
    };
    let pkcs1 = |name: &str, der: &[u8]| RsaKey {
        name: name.into(),
        ours: our_rsa::KeyPair::from_pkcs1(der).unwrap(),
        theirs: aws_lc_rs::rsa::KeyPair::from_der(der).unwrap(),
    };
    macro_rules! key {
        ($load:ident, $file:literal) => {
            $load(
                $file,
                include_bytes!(concat!("../../rind/src/high/rsa/", $file)),
            )
        };
    }

    let generated = our_rsa::KeyPair::generate(rind::rsa::KeySize::Rsa2048).unwrap();
    let der = generated.to_pkcs8();
    let name = format!("generated: {}", hex(der.as_ref()));
    let theirs = aws_lc_rs::rsa::KeyPair::from_pkcs8(der.as_ref())
        .unwrap_or_else(|e| panic!("aws-lc-rs refused the key rind {name}: {e:?}"));

    let keys = vec![
        RsaKey {
            name,
            ours: generated,
            theirs,
        },
        key!(pkcs8, "rsa2048.pkcs8.der"),
        key!(pkcs8, "rsa2048-e33.pkcs8.der"),
        key!(pkcs8, "rsa2049.pkcs8.der"),
        key!(pkcs8, "rsa2050.pkcs8.der"),
        key!(pkcs8, "rsa2056.pkcs8.der"),
        key!(pkcs8, "rsa2560.pkcs8.der"),
        key!(pkcs8, "rsa3072.pkcs8.der"),
        key!(pkcs8, "rsa4096.pkcs8.der"),
        key!(pkcs8, "rsa6144.pkcs8.der"),
        key!(pkcs8, "rsa8192.pkcs8.der"),
        key!(pkcs1, "rsa2048-q-above-p.der"),
        key!(pkcs1, "rsa2086-unbalanced.der"),
    ];
    for key in &keys {
        let public = key.ours.public_key();
        assert_eq!(
            public.as_ref(),
            key.theirs.public_key().as_ref(),
            "{}",
            key.name
        );
    }
    keys
});

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// rind signs `message` with `key`: as aws-lc-rs does under PKCS#1 v1.5,
/// and a signature aws-lc verifies with the salt length under PSS, refusing
/// one longer than the modulus allows.
fn rsa(key: &RsaKey, scheme: &RsaScheme, message: &[u8]) {
    let name = &key.name;
    let (hash, salt) = match *scheme {
        RsaScheme::Pkcs1(hash) => {
            let (ours, theirs) = match hash {
                Hash::Sha256 => (&our_rsa::sign::PKCS1_SHA256, &theirs::RSA_PKCS1_SHA256),
                Hash::Sha384 => (&our_rsa::sign::PKCS1_SHA384, &theirs::RSA_PKCS1_SHA384),
                Hash::Sha512 => (&our_rsa::sign::PKCS1_SHA512, &theirs::RSA_PKCS1_SHA512),
            };
            let signature = key.ours.sign(ours, message).unwrap();
            let mut wanted = vec![0; key.theirs.public_modulus_len()];
            key.theirs
                .sign(theirs, &SystemRandom::new(), message, &mut wanted)
                .unwrap();
            assert_eq!(signature.as_ref(), wanted, "{name}");
            return;
        }
        RsaScheme::Pss(hash, ref salt) => (hash, salt),
    };

    type Md = unsafe extern "C" fn() -> *const aws_lc_sys::EVP_MD;
    let (constant, with_salt, theirs_hash, md): (_, fn(_) -> _, _, Md) = match hash {
        Hash::Sha256 => (
            &our_rsa::sign::PSS_SHA256,
            RsaSigningAlgorithm::pss_sha256,
            &digest::SHA256,
            aws_lc_sys::EVP_sha256,
        ),
        Hash::Sha384 => (
            &our_rsa::sign::PSS_SHA384,
            RsaSigningAlgorithm::pss_sha384,
            &digest::SHA384,
            aws_lc_sys::EVP_sha384,
        ),
        Hash::Sha512 => (
            &our_rsa::sign::PSS_SHA512,
            RsaSigningAlgorithm::pss_sha512,
            &digest::SHA512,
            aws_lc_sys::EVP_sha512,
        ),
    };
    let hash_len = theirs_hash.output_len();
    let public = key.theirs.public_key().as_ref();
    // SAFETY: `public` is `public.len()` readable bytes, and the key is
    // freed once, after its last use.
    let rsa = unsafe { aws_lc_sys::RSA_public_key_from_bytes(public.as_ptr(), public.len()) };
    assert!(!rsa.is_null());
    // SAFETY: `rsa` is a live key.
    let bits = unsafe { aws_lc_sys::RSA_bits(rsa) } as usize;
    // RFC 8017 section 9.1.1's `emLen - hLen - 2`.
    let max = (bits - 1).div_ceil(8) - hash_len - 2;
    let (signature, salt_len) = match *salt {
        Salt::Hash => (key.ours.sign(constant, message), hash_len),
        Salt::Max => (key.ours.sign(&with_salt(PssSaltLength::Max), message), max),
        Salt::Custom(len) => (
            key.ours
                .sign(&with_salt(PssSaltLength::Custom(len)), message),
            usize::from(len),
        ),
    };
    let verified = match signature {
        Err(_) if salt_len > max => None,
        Err(e) => panic!("{name}: refused a salt of {salt_len} bytes: {e:?}"),
        Ok(signature) => {
            assert!(
                salt_len <= max,
                "{name}: signed with a salt past the modulus"
            );
            let digest = digest::digest(theirs_hash, message);
            let digest = digest.as_ref();
            let signature = signature.as_ref();
            // SAFETY: each pointer is valid for its length, and `rsa` is live.
            Some(unsafe {
                aws_lc_sys::RSA_verify_pss_mgf1(
                    rsa,
                    digest.as_ptr(),
                    digest.len(),
                    md(),
                    md(),
                    salt_len as i32,
                    signature.as_ptr(),
                    signature.len(),
                )
            })
        }
    };
    // SAFETY: `rsa` is freed once, after its last use.
    unsafe { aws_lc_sys::RSA_free(rsa) };
    if let Some(verified) = verified {
        assert_eq!(verified, 1, "{name}: aws-lc refused rind's signature");
    }
}
