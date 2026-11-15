#![no_main]

//! Signature verification under every algorithm against aws-lc-rs's, for any
//! public key, signature, and message.
//!
//! The first byte picks the algorithm, and the rest is the key and the
//! signature, each after a big-endian 16-bit length, then the message.
//! rind must never accept a signature aws-lc-rs refuses, and refuses one it
//! accepts only for a key it refuses by design. RSA-PSS with any salt length,
//! which aws-lc-rs does not expose, is checked against aws-lc's, and SLH-DSA,
//! which aws-lc lacks, against RustCrypto's.

use aws_lc_rs::digest;
use aws_lc_rs::signature::{self as theirs, UnparsedPublicKey};
use curve25519_dalek::edwards::CompressedEdwardsY;
use der::{spki_parameters, trailing};
use libfuzzer_sys::fuzz_target;
use rind::signature::{
    PublicKey, RsaPssSaltLength, RsaVerificationAlgorithm, VerificationAlgorithm, verify,
};

mod der;

fuzz_target!(|data: &[u8]| {
    let Some((&selector, rest)) = data.split_first() else {
        return;
    };
    let Some((key, rest)) = split(rest) else {
        return;
    };
    let Some((signature, message)) = split(rest) else {
        return;
    };
    let Some((ours, theirs, kind)) = algorithm(selector) else {
        return;
    };

    let accepted = match theirs {
        Theirs::Rs(theirs) => UnparsedPublicKey::new(theirs, key)
            .verify(message, signature)
            .is_ok(),
        Theirs::PssAnySalt(hash, md) => pss_any_salt(hash, md, key, message, signature),
        Theirs::SlhDsa(verify) => verify(key, message, signature),
    };
    match PublicKey::new(ours, key) {
        Ok(key) => assert_eq!(key.verify(message, signature).is_ok(), accepted),
        Err(e) => assert!(
            !accepted || refused(kind, key),
            "refused a key aws-lc-rs verifies with: {e:?}"
        ),
    }
});

/// Splits `input` after a leading big-endian 16-bit length.
fn split(input: &[u8]) -> Option<(&[u8], &[u8])> {
    let (len, rest) = input.split_first_chunk::<2>()?;
    rest.split_at_checked(usize::from(u16::from_be_bytes(*len)))
}

/// The reference each algorithm is checked against.
enum Theirs {
    /// aws-lc-rs's algorithm of the same name.
    Rs(&'static dyn theirs::VerificationAlgorithm),
    /// aws-lc's RSA-PSS with `RSA_PSS_SALTLEN_AUTO`, on this hash.
    PssAnySalt(
        &'static digest::Algorithm,
        unsafe extern "C" fn() -> *const aws_lc_sys::EVP_MD,
    ),
    /// RustCrypto's SLH-DSA, pure with the empty context: `(key, message,
    /// signature)`.
    SlhDsa(fn(&[u8], &[u8], &[u8]) -> bool),
}

/// Whether RustCrypto verifies `signature` with SLH-DSA parameter set `P`.
fn slh_dsa<P: slh_dsa::ParameterSet>(key: &[u8], message: &[u8], signature: &[u8]) -> bool {
    use slh_dsa::signature::Verifier;
    let key = slh_dsa::VerifyingKey::<P>::try_from(key);
    let signature = slh_dsa::Signature::<P>::try_from(signature);
    let (Ok(key), Ok(signature)) = (key, signature) else {
        return false;
    };
    key.verify(message, &signature).is_ok()
}

/// Whether aws-lc verifies `signature` with RSA-PSS and any salt length,
/// parsing the key and bounding its modulus as aws-lc-rs's
/// `RSA_PSS_2048_8192_*` do.
fn pss_any_salt(
    hash: &'static digest::Algorithm,
    md: unsafe extern "C" fn() -> *const aws_lc_sys::EVP_MD,
    key: &[u8],
    message: &[u8],
    signature: &[u8],
) -> bool {
    let digest = digest::digest(hash, message);
    let digest = digest.as_ref();
    // SAFETY: each pointer is valid for its length, and the key, which
    // `parse_rsa` allocates, is freed once.
    unsafe {
        let rsa = parse_rsa(key);
        if rsa.is_null() {
            return false;
        }
        let accepted = (2048..=8192).contains(&aws_lc_sys::RSA_bits(rsa))
            && aws_lc_sys::RSA_verify_pss_mgf1(
                rsa,
                digest.as_ptr(),
                digest.len(),
                md(),
                md(),
                aws_lc_sys::RSA_PSS_SALTLEN_AUTO,
                signature.as_ptr(),
                signature.len(),
            ) == 1;
        aws_lc_sys::RSA_free(rsa);
        accepted
    }
}

/// aws-lc-rs's `parse_rsa_public_key`: an `RSAPublicKey`, or else a
/// `SubjectPublicKeyInfo` of an RSA or RSA-PSS key; null if neither.
///
/// # Safety
///
/// The caller frees a key this returns with `RSA_free`.
unsafe fn parse_rsa(key: &[u8]) -> *mut aws_lc_sys::RSA {
    let rsa = aws_lc_sys::RSA_public_key_from_bytes(key.as_ptr(), key.len());
    if !rsa.is_null() {
        return rsa;
    }
    let mut cbs = std::mem::MaybeUninit::uninit();
    aws_lc_sys::CBS_init(cbs.as_mut_ptr(), key.as_ptr(), key.len());
    let pkey = aws_lc_sys::EVP_parse_public_key(cbs.as_mut_ptr());
    if pkey.is_null() {
        return std::ptr::null_mut();
    }
    let rsa = match aws_lc_sys::EVP_PKEY_id(pkey) {
        aws_lc_sys::EVP_PKEY_RSA | aws_lc_sys::EVP_PKEY_RSA_PSS => {
            aws_lc_sys::EVP_PKEY_get1_RSA(pkey)
        }
        _ => std::ptr::null_mut(),
    };
    aws_lc_sys::EVP_PKEY_free(pkey);
    rsa
}

#[derive(Clone, Copy)]
enum Kind {
    Ecdsa,
    Rsa,
    Ed25519,
    /// ML-DSA, with its parameter set's public key length.
    MlDsa(usize),
    SlhDsa,
}

/// The algorithm `selector` picks on each side, and its key type.
fn algorithm(selector: u8) -> Option<(&'static VerificationAlgorithm, Theirs, Kind)> {
    use verify::legacy;
    Some(match selector {
        0 => (
            &verify::ED25519,
            Theirs::Rs(&theirs::ED25519),
            Kind::Ed25519,
        ),
        1 => (
            &verify::ECDSA_P256_SHA256_ASN1,
            Theirs::Rs(&theirs::ECDSA_P256_SHA256_ASN1),
            Kind::Ecdsa,
        ),
        2 => (
            &verify::ECDSA_P256_SHA384_ASN1,
            Theirs::Rs(&theirs::ECDSA_P256_SHA384_ASN1),
            Kind::Ecdsa,
        ),
        3 => (
            &verify::ECDSA_P256_SHA512_ASN1,
            Theirs::Rs(&theirs::ECDSA_P256_SHA512_ASN1),
            Kind::Ecdsa,
        ),
        4 => (
            &verify::ECDSA_P384_SHA256_ASN1,
            Theirs::Rs(&theirs::ECDSA_P384_SHA256_ASN1),
            Kind::Ecdsa,
        ),
        5 => (
            &verify::ECDSA_P384_SHA384_ASN1,
            Theirs::Rs(&theirs::ECDSA_P384_SHA384_ASN1),
            Kind::Ecdsa,
        ),
        6 => (
            &verify::ECDSA_P384_SHA512_ASN1,
            Theirs::Rs(&theirs::ECDSA_P384_SHA512_ASN1),
            Kind::Ecdsa,
        ),
        7 => (
            &verify::ECDSA_P521_SHA256_ASN1,
            Theirs::Rs(&theirs::ECDSA_P521_SHA256_ASN1),
            Kind::Ecdsa,
        ),
        8 => (
            &verify::ECDSA_P521_SHA384_ASN1,
            Theirs::Rs(&theirs::ECDSA_P521_SHA384_ASN1),
            Kind::Ecdsa,
        ),
        9 => (
            &verify::ECDSA_P521_SHA512_ASN1,
            Theirs::Rs(&theirs::ECDSA_P521_SHA512_ASN1),
            Kind::Ecdsa,
        ),
        10 => (
            &verify::ECDSA_P256_SHA256_FIXED,
            Theirs::Rs(&theirs::ECDSA_P256_SHA256_FIXED),
            Kind::Ecdsa,
        ),
        11 => (
            &verify::ECDSA_P384_SHA384_FIXED,
            Theirs::Rs(&theirs::ECDSA_P384_SHA384_FIXED),
            Kind::Ecdsa,
        ),
        12 => (
            &verify::ECDSA_P521_SHA512_FIXED,
            Theirs::Rs(&theirs::ECDSA_P521_SHA512_FIXED),
            Kind::Ecdsa,
        ),
        13 => (
            verify::RSA_PKCS1_SHA256.as_ref(),
            Theirs::Rs(&theirs::RSA_PKCS1_2048_8192_SHA256),
            Kind::Rsa,
        ),
        14 => (
            verify::RSA_PKCS1_SHA384.as_ref(),
            Theirs::Rs(&theirs::RSA_PKCS1_2048_8192_SHA384),
            Kind::Rsa,
        ),
        15 => (
            verify::RSA_PKCS1_SHA512.as_ref(),
            Theirs::Rs(&theirs::RSA_PKCS1_2048_8192_SHA512),
            Kind::Rsa,
        ),
        16 => (
            verify::RSA_PSS_SHA256.as_ref(),
            Theirs::Rs(&theirs::RSA_PSS_2048_8192_SHA256),
            Kind::Rsa,
        ),
        17 => (
            verify::RSA_PSS_SHA384.as_ref(),
            Theirs::Rs(&theirs::RSA_PSS_2048_8192_SHA384),
            Kind::Rsa,
        ),
        18 => (
            verify::RSA_PSS_SHA512.as_ref(),
            Theirs::Rs(&theirs::RSA_PSS_2048_8192_SHA512),
            Kind::Rsa,
        ),
        19 => (
            legacy::RSA_PKCS1_SHA1.as_ref(),
            Theirs::Rs(&theirs::RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY),
            Kind::Rsa,
        ),
        20 => (
            legacy::RSA_PKCS1_1024_SHA1.as_ref(),
            Theirs::Rs(&theirs::RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY),
            Kind::Rsa,
        ),
        21 => (
            legacy::RSA_PKCS1_1024_SHA256.as_ref(),
            Theirs::Rs(&theirs::RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY),
            Kind::Rsa,
        ),
        22 => (
            legacy::RSA_PKCS1_1024_SHA512.as_ref(),
            Theirs::Rs(&theirs::RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY),
            Kind::Rsa,
        ),
        23 => (
            legacy::RSA_PKCS1_3072_SHA384.as_ref(),
            Theirs::Rs(&theirs::RSA_PKCS1_3072_8192_SHA384),
            Kind::Rsa,
        ),
        24 => (
            OURS_PSS_SHA256_NO_SALT.as_ref(),
            Theirs::Rs(&THEIRS_PSS_SHA256_NO_SALT),
            Kind::Rsa,
        ),
        25 => (
            OURS_PSS_SHA512_MAX_SALT.as_ref(),
            Theirs::Rs(&THEIRS_PSS_SHA512_MAX_SALT),
            Kind::Rsa,
        ),
        26 => (
            verify::RSA_PSS_SHA256_ANY_SALT.as_ref(),
            Theirs::PssAnySalt(&digest::SHA256, aws_lc_sys::EVP_sha256),
            Kind::Rsa,
        ),
        27 => (
            verify::RSA_PSS_SHA384_ANY_SALT.as_ref(),
            Theirs::PssAnySalt(&digest::SHA384, aws_lc_sys::EVP_sha384),
            Kind::Rsa,
        ),
        28 => (
            verify::RSA_PSS_SHA512_ANY_SALT.as_ref(),
            Theirs::PssAnySalt(&digest::SHA512, aws_lc_sys::EVP_sha512),
            Kind::Rsa,
        ),
        29 => (
            &verify::ML_DSA_44,
            Theirs::Rs(&theirs::ML_DSA_44),
            Kind::MlDsa(1312),
        ),
        30 => (
            &verify::ML_DSA_65,
            Theirs::Rs(&theirs::ML_DSA_65),
            Kind::MlDsa(1952),
        ),
        31 => (
            &verify::ML_DSA_87,
            Theirs::Rs(&theirs::ML_DSA_87),
            Kind::MlDsa(2592),
        ),
        32 => (
            &verify::SLH_DSA_SHA2_128S,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_128s>),
            Kind::SlhDsa,
        ),
        33 => (
            &verify::SLH_DSA_SHA2_128F,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_128f>),
            Kind::SlhDsa,
        ),
        34 => (
            &verify::SLH_DSA_SHA2_192S,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_192s>),
            Kind::SlhDsa,
        ),
        35 => (
            &verify::SLH_DSA_SHA2_192F,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_192f>),
            Kind::SlhDsa,
        ),
        36 => (
            &verify::SLH_DSA_SHA2_256S,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_256s>),
            Kind::SlhDsa,
        ),
        37 => (
            &verify::SLH_DSA_SHA2_256F,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_256f>),
            Kind::SlhDsa,
        ),
        38 => (
            &verify::SLH_DSA_SHAKE_128S,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake128s>),
            Kind::SlhDsa,
        ),
        39 => (
            &verify::SLH_DSA_SHAKE_128F,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake128f>),
            Kind::SlhDsa,
        ),
        40 => (
            &verify::SLH_DSA_SHAKE_192S,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake192s>),
            Kind::SlhDsa,
        ),
        41 => (
            &verify::SLH_DSA_SHAKE_192F,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake192f>),
            Kind::SlhDsa,
        ),
        42 => (
            &verify::SLH_DSA_SHAKE_256S,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake256s>),
            Kind::SlhDsa,
        ),
        43 => (
            &verify::SLH_DSA_SHAKE_256F,
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake256f>),
            Kind::SlhDsa,
        ),
        _ => return None,
    })
}

// PSS with salt lengths other than the hash's, at both ends of the range.
static OURS_PSS_SHA256_NO_SALT: RsaVerificationAlgorithm =
    RsaVerificationAlgorithm::pss_sha256(RsaPssSaltLength::Custom(0));
static THEIRS_PSS_SHA256_NO_SALT: theirs::RsaParameters =
    theirs::RSA_PSS_2048_8192_SHA256.with_pss_salt_length(theirs::RsaPssSaltLength::Custom(0));
static OURS_PSS_SHA512_MAX_SALT: RsaVerificationAlgorithm =
    RsaVerificationAlgorithm::pss_sha512(RsaPssSaltLength::Max);
static THEIRS_PSS_SHA512_MAX_SALT: theirs::RsaParameters =
    theirs::RSA_PSS_2048_8192_SHA512.with_pss_salt_length(theirs::RsaPssSaltLength::Max);

/// Whether rind refuses `key` by design where aws-lc-rs takes it.
fn refused(kind: Kind, key: &[u8]) -> bool {
    match kind {
        // aws-lc-rs also takes a `SubjectPublicKeyInfo`, and a compressed or
        // hybrid point; rind takes only the uncompressed point.
        Kind::Ecdsa => key.first() != Some(&4),
        // aws-lc-rs ignores a `SubjectPublicKeyInfo`'s parameters, and
        // bytes after the key.
        Kind::Rsa => spki_parameters(key) || trailing(key),
        // aws-lc-rs also takes a `SubjectPublicKeyInfo`, any length but 32,
        // and rind refuses a key of small order, under which signatures
        // nobody made verify.
        Kind::Ed25519 => match <[u8; 32]>::try_from(key) {
            Ok(key) => CompressedEdwardsY(key)
                .decompress()
                .is_some_and(|point| point.is_small_order()),
            Err(_) => true,
        },
        // aws-lc-rs also takes a `SubjectPublicKeyInfo`; rind takes only the
        // raw key, of which any bytes of its length are one.
        Kind::MlDsa(len) => key.len() != len,
        // Any bytes of the key's length are one, on both sides.
        Kind::SlhDsa => false,
    }
}
