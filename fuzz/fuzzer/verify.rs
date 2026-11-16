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
use rind::ml_dsa::{MlDsa44, MlDsa65, MlDsa87};
use rind::rsa::{PssSaltLength, VerificationAlgorithm as RsaVerificationAlgorithm};
use rind::{Error, ecdsa, ed25519, ml_dsa, rsa};

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
    let Some((ours, theirs)) = algorithm(selector) else {
        return;
    };

    let accepted = match theirs {
        Theirs::Rs(theirs) => UnparsedPublicKey::new(theirs, key)
            .verify(message, signature)
            .is_ok(),
        Theirs::PssAnySalt(hash, md) => pss_any_salt(hash, md, key, message, signature),
        Theirs::SlhDsa(verify) => verify(key, message, signature),
    };
    match ours.verify(key, message, signature) {
        Ok(verified) => assert_eq!(verified, accepted),
        Err(e) => assert!(
            !accepted || refused(ours, key),
            "refused a key aws-lc-rs verifies with: {e:?}"
        ),
    }
});

/// rind's algorithm, in its module.
#[derive(Clone, Copy)]
enum Ours {
    Ecdsa(&'static ecdsa::VerificationAlgorithm),
    Rsa(&'static RsaVerificationAlgorithm),
    Ed25519,
    MlDsa44,
    MlDsa65,
    MlDsa87,
    SlhDsa(OurSlhDsa),
}

/// Whether a key of an SLH-DSA parameter set verifies a signature over a
/// message, `(key, message, signature)`, or an error if rind refuses the key.
type OurSlhDsa = fn(&[u8], &[u8], &[u8]) -> Result<bool, Error>;

impl Ours {
    /// Whether `signature` verifies over `message`, or an error if rind
    /// refuses `key`: as it loads it, or for RSA as it verifies, with a
    /// modulus below the algorithm's floor.
    fn verify(self, key: &[u8], message: &[u8], signature: &[u8]) -> Result<bool, Error> {
        let verified = match self {
            Self::Ecdsa(algorithm) => {
                ecdsa::PublicKey::new(algorithm, key)?.verify(message, signature)
            }
            Self::Rsa(algorithm) => {
                // aws-lc-rs takes PKCS#1 or a `SubjectPublicKeyInfo`.
                let key = rsa::PublicKey::new(key).or_else(|_| rsa::PublicKey::from_spki(key))?;
                match key.verify(algorithm, message, signature) {
                    Err(Error::KeyRejected(e)) => return Err(Error::KeyRejected(e)),
                    verified => verified,
                }
            }
            Self::Ed25519 => ed25519::PublicKey::new(key)?.verify(message, signature),
            Self::MlDsa44 => ml_dsa::PublicKey::<MlDsa44>::new(key)?.verify(message, signature),
            Self::MlDsa65 => ml_dsa::PublicKey::<MlDsa65>::new(key)?.verify(message, signature),
            Self::MlDsa87 => ml_dsa::PublicKey::<MlDsa87>::new(key)?.verify(message, signature),
            Self::SlhDsa(verify) => return verify(key, message, signature),
        };
        Ok(verified.is_ok())
    }
}

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

/// Whether rind verifies `signature` with SLH-DSA parameter set `P`, or an
/// error if it refuses `key`.
fn our_slh_dsa<P: rind::slh_dsa::ParameterSet>(
    key: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<bool, Error> {
    let key = rind::slh_dsa::PublicKey::<P>::new(key)?;
    Ok(key.verify(message, signature).is_ok())
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

/// The algorithm `selector` picks on each side.
fn algorithm(selector: u8) -> Option<(Ours, Theirs)> {
    use rsa::verify::{self, legacy};
    Some(match selector {
        0 => (Ours::Ed25519, Theirs::Rs(&theirs::ED25519)),
        1 => (
            Ours::Ecdsa(&ecdsa::verify::P256_SHA256_ASN1),
            Theirs::Rs(&theirs::ECDSA_P256_SHA256_ASN1),
        ),
        2 => (
            Ours::Ecdsa(&ecdsa::verify::P256_SHA384_ASN1),
            Theirs::Rs(&theirs::ECDSA_P256_SHA384_ASN1),
        ),
        3 => (
            Ours::Ecdsa(&ecdsa::verify::P256_SHA512_ASN1),
            Theirs::Rs(&theirs::ECDSA_P256_SHA512_ASN1),
        ),
        4 => (
            Ours::Ecdsa(&ecdsa::verify::P384_SHA256_ASN1),
            Theirs::Rs(&theirs::ECDSA_P384_SHA256_ASN1),
        ),
        5 => (
            Ours::Ecdsa(&ecdsa::verify::P384_SHA384_ASN1),
            Theirs::Rs(&theirs::ECDSA_P384_SHA384_ASN1),
        ),
        6 => (
            Ours::Ecdsa(&ecdsa::verify::P384_SHA512_ASN1),
            Theirs::Rs(&theirs::ECDSA_P384_SHA512_ASN1),
        ),
        7 => (
            Ours::Ecdsa(&ecdsa::verify::P521_SHA256_ASN1),
            Theirs::Rs(&theirs::ECDSA_P521_SHA256_ASN1),
        ),
        8 => (
            Ours::Ecdsa(&ecdsa::verify::P521_SHA384_ASN1),
            Theirs::Rs(&theirs::ECDSA_P521_SHA384_ASN1),
        ),
        9 => (
            Ours::Ecdsa(&ecdsa::verify::P521_SHA512_ASN1),
            Theirs::Rs(&theirs::ECDSA_P521_SHA512_ASN1),
        ),
        10 => (
            Ours::Ecdsa(&ecdsa::verify::P256_SHA256_FIXED),
            Theirs::Rs(&theirs::ECDSA_P256_SHA256_FIXED),
        ),
        11 => (
            Ours::Ecdsa(&ecdsa::verify::P384_SHA384_FIXED),
            Theirs::Rs(&theirs::ECDSA_P384_SHA384_FIXED),
        ),
        12 => (
            Ours::Ecdsa(&ecdsa::verify::P521_SHA512_FIXED),
            Theirs::Rs(&theirs::ECDSA_P521_SHA512_FIXED),
        ),
        13 => (
            Ours::Rsa(&verify::PKCS1_SHA256),
            Theirs::Rs(&theirs::RSA_PKCS1_2048_8192_SHA256),
        ),
        14 => (
            Ours::Rsa(&verify::PKCS1_SHA384),
            Theirs::Rs(&theirs::RSA_PKCS1_2048_8192_SHA384),
        ),
        15 => (
            Ours::Rsa(&verify::PKCS1_SHA512),
            Theirs::Rs(&theirs::RSA_PKCS1_2048_8192_SHA512),
        ),
        16 => (
            Ours::Rsa(&verify::PSS_SHA256),
            Theirs::Rs(&theirs::RSA_PSS_2048_8192_SHA256),
        ),
        17 => (
            Ours::Rsa(&verify::PSS_SHA384),
            Theirs::Rs(&theirs::RSA_PSS_2048_8192_SHA384),
        ),
        18 => (
            Ours::Rsa(&verify::PSS_SHA512),
            Theirs::Rs(&theirs::RSA_PSS_2048_8192_SHA512),
        ),
        19 => (
            Ours::Rsa(&legacy::PKCS1_SHA1),
            Theirs::Rs(&theirs::RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY),
        ),
        20 => (
            Ours::Rsa(&legacy::PKCS1_1024_SHA1),
            Theirs::Rs(&theirs::RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY),
        ),
        21 => (
            Ours::Rsa(&legacy::PKCS1_1024_SHA256),
            Theirs::Rs(&theirs::RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY),
        ),
        22 => (
            Ours::Rsa(&legacy::PKCS1_1024_SHA512),
            Theirs::Rs(&theirs::RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY),
        ),
        23 => (
            Ours::Rsa(&legacy::PKCS1_3072_SHA384),
            Theirs::Rs(&theirs::RSA_PKCS1_3072_8192_SHA384),
        ),
        24 => (
            Ours::Rsa(&OURS_PSS_SHA256_NO_SALT),
            Theirs::Rs(&THEIRS_PSS_SHA256_NO_SALT),
        ),
        25 => (
            Ours::Rsa(&OURS_PSS_SHA512_MAX_SALT),
            Theirs::Rs(&THEIRS_PSS_SHA512_MAX_SALT),
        ),
        26 => (
            Ours::Rsa(&verify::PSS_SHA256_ANY_SALT),
            Theirs::PssAnySalt(&digest::SHA256, aws_lc_sys::EVP_sha256),
        ),
        27 => (
            Ours::Rsa(&verify::PSS_SHA384_ANY_SALT),
            Theirs::PssAnySalt(&digest::SHA384, aws_lc_sys::EVP_sha384),
        ),
        28 => (
            Ours::Rsa(&verify::PSS_SHA512_ANY_SALT),
            Theirs::PssAnySalt(&digest::SHA512, aws_lc_sys::EVP_sha512),
        ),
        29 => (Ours::MlDsa44, Theirs::Rs(&theirs::ML_DSA_44)),
        30 => (Ours::MlDsa65, Theirs::Rs(&theirs::ML_DSA_65)),
        31 => (Ours::MlDsa87, Theirs::Rs(&theirs::ML_DSA_87)),
        32 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaSha2_128s>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_128s>),
        ),
        33 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaSha2_128f>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_128f>),
        ),
        34 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaSha2_192s>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_192s>),
        ),
        35 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaSha2_192f>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_192f>),
        ),
        36 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaSha2_256s>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_256s>),
        ),
        37 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaSha2_256f>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Sha2_256f>),
        ),
        38 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaShake128s>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake128s>),
        ),
        39 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaShake128f>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake128f>),
        ),
        40 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaShake192s>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake192s>),
        ),
        41 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaShake192f>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake192f>),
        ),
        42 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaShake256s>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake256s>),
        ),
        43 => (
            Ours::SlhDsa(our_slh_dsa::<rind::slh_dsa::SlhDsaShake256f>),
            Theirs::SlhDsa(slh_dsa::<slh_dsa::Shake256f>),
        ),
        _ => return None,
    })
}

// PSS with salt lengths other than the hash's, at both ends of the range.
static OURS_PSS_SHA256_NO_SALT: RsaVerificationAlgorithm =
    RsaVerificationAlgorithm::pss_sha256(PssSaltLength::Custom(0));
static THEIRS_PSS_SHA256_NO_SALT: theirs::RsaParameters =
    theirs::RSA_PSS_2048_8192_SHA256.with_pss_salt_length(theirs::RsaPssSaltLength::Custom(0));
static OURS_PSS_SHA512_MAX_SALT: RsaVerificationAlgorithm =
    RsaVerificationAlgorithm::pss_sha512(PssSaltLength::Max);
static THEIRS_PSS_SHA512_MAX_SALT: theirs::RsaParameters =
    theirs::RSA_PSS_2048_8192_SHA512.with_pss_salt_length(theirs::RsaPssSaltLength::Max);

/// Whether rind refuses `key` by design where aws-lc-rs takes it.
fn refused(ours: Ours, key: &[u8]) -> bool {
    match ours {
        // aws-lc-rs also takes a `SubjectPublicKeyInfo`, and a compressed or
        // hybrid point; rind takes only the uncompressed point.
        Ours::Ecdsa(_) => key.first() != Some(&4),
        // aws-lc-rs ignores a `SubjectPublicKeyInfo`'s parameters, and
        // bytes after the key.
        Ours::Rsa(_) => spki_parameters(key) || trailing(key),
        // aws-lc-rs also takes a `SubjectPublicKeyInfo`, any length but 32,
        // and rind refuses a key of small order, under which signatures
        // nobody made verify.
        Ours::Ed25519 => match <[u8; 32]>::try_from(key) {
            Ok(key) => CompressedEdwardsY(key)
                .decompress()
                .is_some_and(|point| point.is_small_order()),
            Err(_) => true,
        },
        // aws-lc-rs also takes a `SubjectPublicKeyInfo`; rind takes only the
        // raw key, of which any bytes of its length are one.
        Ours::MlDsa44 => key.len() != 1312,
        Ours::MlDsa65 => key.len() != 1952,
        Ours::MlDsa87 => key.len() != 2592,
        // Any bytes of the key's length are one, on both sides.
        Ours::SlhDsa(_) => false,
    }
}
