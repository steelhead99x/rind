// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Signatures, as FIPS 186-5 and FIPS 204 approve them, and aws-lc's
//! service indicator: ECDSA on P-256, P-384, and P-521, RSA PKCS#1 v1.5 and
//! PSS, Ed25519, and ML-DSA.
//!
//! - An RSA modulus is an even length of 2048 bits or more, or exactly 1024
//!   bits for the `legacy` algorithms that verify old signatures.
//! - SHA-1 only verifies, and only RSA PKCS#1 v1.5.
//! - A PSS salt is as long as the hash: the length ACVP tests.
//! - A pairwise consistency test follows every key pair generation.

use rind::ecdsa::KeyPair as EcdsaKeyPair;
use rind::ed25519::KeyPair as Ed25519KeyPair;
use rind::encoding::Spki;
use rind::ml_dsa::{KeyPair as MlDsaKeyPair, MlDsa44, MlDsa65, MlDsa87};
use rind::rsa::{KeyPair as RsaKeyPair, KeySize, PublicKeyComponents};
use rind::{Error, ecdsa, ed25519, ml_dsa, rsa};

use crate::abi::{Encoded, Status, bytes, bytes_mut, copy_out, encoded, free, handle, put, status};
use crate::ids::{self, signature as id};
use crate::scrub::{Depth, scrubbed};
use crate::selftest::{SelfTest as T, ensure, pct, pct_drawing};

/// What every pairwise consistency test signs.
const PCT_MESSAGE: &[u8] = b"rind-fips pairwise consistency test";

/// Boxes `result`'s value as a handle at `out`, returning its status.
///
/// # Safety
/// `out` must be valid for a write.
unsafe fn put_handle<V>(result: Result<V, Error>, out: *mut *mut V) -> Status {
    // SAFETY: the caller's contract.
    status(result.map(|value| unsafe { put(out, handle(value)) }))
}

/// Writes `signature` to the `cap` bytes at `out`, and its length to `len`.
///
/// # Safety
/// As [`copy_out`] requires.
unsafe fn put_signature(
    signature: Result<impl AsRef<[u8]>, Error>,
    out: *mut u8,
    cap: usize,
    len: *mut usize,
) -> Status {
    // SAFETY: the caller's contract.
    status(signature.and_then(|s| unsafe { copy_out(s.as_ref(), out, cap, len) }))
}

/// The status of an unknown algorithm, which `rind-fips`'s types never pass.
fn unsupported() -> Status {
    status(Err(Error::Unsupported))
}

/// A public key a handle holds, in its algorithm's module.
#[allow(clippy::large_enum_variant)]
#[derive(Clone)]
pub(crate) enum PublicKey {
    Ecdsa(ecdsa::PublicKey),
    Ed25519(ed25519::PublicKey),
    MlDsa44(ml_dsa::PublicKey<MlDsa44>),
    MlDsa65(ml_dsa::PublicKey<MlDsa65>),
    MlDsa87(ml_dsa::PublicKey<MlDsa87>),
    Rsa(rsa::PublicKey),
}

impl PublicKey {
    fn bytes(&self) -> &[u8] {
        match self {
            Self::Ecdsa(key) => key.as_ref(),
            Self::Ed25519(key) => key.as_ref(),
            Self::MlDsa44(key) => key.as_ref(),
            Self::MlDsa65(key) => key.as_ref(),
            Self::MlDsa87(key) => key.as_ref(),
            Self::Rsa(key) => key.as_ref(),
        }
    }

    fn to_spki(&self) -> Spki {
        match self {
            Self::Ecdsa(key) => key.to_spki(),
            Self::Ed25519(key) => key.to_spki(),
            Self::MlDsa44(key) => key.to_spki(),
            Self::MlDsa65(key) => key.to_spki(),
            Self::MlDsa87(key) => key.to_spki(),
            Self::Rsa(key) => key.to_spki(),
        }
    }

    /// Verifies with a key bound to its algorithm: any but RSA's, which
    /// [`rind_fips_rsa_public_key_verify`] takes with its algorithm.
    fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        match self {
            Self::Ecdsa(key) => key.verify(message, signature),
            Self::Ed25519(key) => key.verify(message, signature),
            Self::MlDsa44(key) => key.verify(message, signature),
            Self::MlDsa65(key) => key.verify(message, signature),
            Self::MlDsa87(key) => key.verify(message, signature),
            Self::Rsa(_) => Err(Error::Unsupported),
        }
    }

    fn verify_digest(&self, digest: &rind::digest::Digest, signature: &[u8]) -> Result<(), Error> {
        match self {
            Self::Ecdsa(key) => key.verify_digest(digest, signature),
            _ => Err(Error::Unsupported),
        }
    }
}

/// A verification algorithm other than RSA's, whose keys are bound to none,
/// in its module.
#[derive(Clone, Copy)]
enum Verification {
    Ecdsa(&'static ecdsa::VerificationAlgorithm),
    Ed25519,
    MlDsa44,
    MlDsa65,
    MlDsa87,
}

impl Verification {
    /// Parses a public key's encoding.
    fn parse(self, bytes: &[u8]) -> Result<PublicKey, Error> {
        match self {
            Self::Ecdsa(algorithm) => ecdsa::PublicKey::new(algorithm, bytes).map(PublicKey::Ecdsa),
            Self::Ed25519 => ed25519::PublicKey::new(bytes).map(PublicKey::Ed25519),
            Self::MlDsa44 => ml_dsa::PublicKey::new(bytes).map(PublicKey::MlDsa44),
            Self::MlDsa65 => ml_dsa::PublicKey::new(bytes).map(PublicKey::MlDsa65),
            Self::MlDsa87 => ml_dsa::PublicKey::new(bytes).map(PublicKey::MlDsa87),
        }
    }

    fn parse_spki(self, der: &[u8]) -> Result<PublicKey, Error> {
        match self {
            Self::Ecdsa(algorithm) => {
                ecdsa::PublicKey::from_spki(algorithm, der).map(PublicKey::Ecdsa)
            }
            Self::Ed25519 => ed25519::PublicKey::from_spki(der).map(PublicKey::Ed25519),
            Self::MlDsa44 => ml_dsa::PublicKey::from_spki(der).map(PublicKey::MlDsa44),
            Self::MlDsa65 => ml_dsa::PublicKey::from_spki(der).map(PublicKey::MlDsa65),
            Self::MlDsa87 => ml_dsa::PublicKey::from_spki(der).map(PublicKey::MlDsa87),
        }
    }
}

/// The verification algorithm other than RSA's `id` names, after its
/// self-tests.
fn verification(id: u32) -> Option<Verification> {
    let (algorithm, tests): (Verification, &[T]) = match id {
        id::ECDSA_P256_SHA256_ASN1 => (
            Verification::Ecdsa(&ecdsa::verify::P256_SHA256_ASN1),
            &[T::Ecdsa, T::Sha256],
        ),
        id::ECDSA_P256_SHA384_ASN1 => (
            Verification::Ecdsa(&ecdsa::verify::P256_SHA384_ASN1),
            &[T::Ecdsa, T::Sha512],
        ),
        id::ECDSA_P256_SHA512_ASN1 => (
            Verification::Ecdsa(&ecdsa::verify::P256_SHA512_ASN1),
            &[T::Ecdsa, T::Sha512],
        ),
        id::ECDSA_P384_SHA256_ASN1 => (
            Verification::Ecdsa(&ecdsa::verify::P384_SHA256_ASN1),
            &[T::Ecdsa, T::Sha256],
        ),
        id::ECDSA_P384_SHA384_ASN1 => (
            Verification::Ecdsa(&ecdsa::verify::P384_SHA384_ASN1),
            &[T::Ecdsa, T::Sha512],
        ),
        id::ECDSA_P384_SHA512_ASN1 => (
            Verification::Ecdsa(&ecdsa::verify::P384_SHA512_ASN1),
            &[T::Ecdsa, T::Sha512],
        ),
        id::ECDSA_P521_SHA256_ASN1 => (
            Verification::Ecdsa(&ecdsa::verify::P521_SHA256_ASN1),
            &[T::Ecdsa, T::Sha256],
        ),
        id::ECDSA_P521_SHA384_ASN1 => (
            Verification::Ecdsa(&ecdsa::verify::P521_SHA384_ASN1),
            &[T::Ecdsa, T::Sha512],
        ),
        id::ECDSA_P521_SHA512_ASN1 => (
            Verification::Ecdsa(&ecdsa::verify::P521_SHA512_ASN1),
            &[T::Ecdsa, T::Sha512],
        ),
        id::ECDSA_P256_SHA256_FIXED => (
            Verification::Ecdsa(&ecdsa::verify::P256_SHA256_FIXED),
            &[T::Ecdsa, T::Sha256],
        ),
        id::ECDSA_P384_SHA384_FIXED => (
            Verification::Ecdsa(&ecdsa::verify::P384_SHA384_FIXED),
            &[T::Ecdsa, T::Sha512],
        ),
        id::ECDSA_P521_SHA512_FIXED => (
            Verification::Ecdsa(&ecdsa::verify::P521_SHA512_FIXED),
            &[T::Ecdsa, T::Sha512],
        ),
        id::ED25519 => (Verification::Ed25519, &[T::Ed25519, T::Sha512]),
        id::ML_DSA_44 => (Verification::MlDsa44, &[T::MlDsa]),
        id::ML_DSA_65 => (Verification::MlDsa65, &[T::MlDsa]),
        id::ML_DSA_87 => (Verification::MlDsa87, &[T::MlDsa]),
        _ => return None,
    };
    ensure(tests);
    Some(algorithm)
}

/// The RSA verification algorithm `id` names, and whether it takes a
/// 1024-bit modulus, after its self-tests.
fn rsa_verification(id: u32) -> Option<(&'static rsa::VerificationAlgorithm, bool)> {
    use rsa::verify::{self as v, legacy};
    let (algorithm, legacy_1024, hash) = match id {
        id::RSA_PKCS1_SHA256 => (&v::PKCS1_SHA256, false, T::Sha256),
        id::RSA_PKCS1_SHA384 => (&v::PKCS1_SHA384, false, T::Sha512),
        id::RSA_PKCS1_SHA512 => (&v::PKCS1_SHA512, false, T::Sha512),
        id::RSA_PSS_SHA256 => (&v::PSS_SHA256, false, T::Sha256),
        id::RSA_PSS_SHA384 => (&v::PSS_SHA384, false, T::Sha512),
        id::RSA_PSS_SHA512 => (&v::PSS_SHA512, false, T::Sha512),
        id::RSA_PKCS1_SHA1 => (&legacy::PKCS1_SHA1, false, T::Sha1),
        id::RSA_PKCS1_1024_SHA1 => (&legacy::PKCS1_1024_SHA1, true, T::Sha1),
        id::RSA_PKCS1_1024_SHA256 => (&legacy::PKCS1_1024_SHA256, true, T::Sha256),
        id::RSA_PKCS1_1024_SHA512 => (&legacy::PKCS1_1024_SHA512, true, T::Sha512),
        id::RSA_PKCS1_3072_SHA384 => (&legacy::PKCS1_3072_SHA384, false, T::Sha512),
        _ => return None,
    };
    ensure(&[T::Rsa, hash]);
    Some((algorithm, legacy_1024))
}

/// The ECDSA signing algorithm `id` names, after its self-tests.
fn ecdsa_algorithm(id: u32) -> Option<&'static ecdsa::SigningAlgorithm> {
    let (algorithm, hash) = match id {
        id::ECDSA_P256_SHA256_ASN1 => (&ecdsa::sign::P256_SHA256_ASN1, T::Sha256),
        id::ECDSA_P384_SHA384_ASN1 => (&ecdsa::sign::P384_SHA384_ASN1, T::Sha512),
        id::ECDSA_P521_SHA512_ASN1 => (&ecdsa::sign::P521_SHA512_ASN1, T::Sha512),
        id::ECDSA_P256_SHA256_FIXED => (&ecdsa::sign::P256_SHA256_FIXED, T::Sha256),
        id::ECDSA_P384_SHA384_FIXED => (&ecdsa::sign::P384_SHA384_FIXED, T::Sha512),
        id::ECDSA_P521_SHA512_FIXED => (&ecdsa::sign::P521_SHA512_FIXED, T::Sha512),
        _ => return None,
    };
    ensure(&[T::Ecdsa, hash]);
    Some(algorithm)
}

/// The RSA signing algorithm `id` names, after its self-tests.
fn rsa_algorithm(id: u32) -> Option<&'static rsa::SigningAlgorithm> {
    let (algorithm, hash) = match id {
        id::RSA_PKCS1_SHA256 => (&rsa::sign::PKCS1_SHA256, T::Sha256),
        id::RSA_PKCS1_SHA384 => (&rsa::sign::PKCS1_SHA384, T::Sha512),
        id::RSA_PKCS1_SHA512 => (&rsa::sign::PKCS1_SHA512, T::Sha512),
        id::RSA_PSS_SHA256 => (&rsa::sign::PSS_SHA256, T::Sha256),
        id::RSA_PSS_SHA384 => (&rsa::sign::PSS_SHA384, T::Sha512),
        id::RSA_PSS_SHA512 => (&rsa::sign::PSS_SHA512, T::Sha512),
        _ => return None,
    };
    ensure(&[T::Rsa, hash]);
    Some(algorithm)
}

/// The digest of hash `hash` holding `value`, as the caller computed it.
fn digest(hash: u32, value: &[u8]) -> Result<rind::digest::Digest, Error> {
    let algorithm = crate::digest::algorithm(hash).ok_or(Error::Unsupported)?;
    rind::fips::digest(algorithm, value).ok_or(Error::WrongLength)
}

// Public keys. Verifying handles nothing secret, so no service here zeroes
// the stack.

/// Parses the `len` bytes at `key` as a public key for verification
/// algorithm `id`, boxing it at `out`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_public_key_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut PublicKey,
) -> Status {
    let Some(algorithm) = verification(id) else {
        return unsupported();
    };
    // SAFETY: the caller's contract.
    unsafe { put_handle(algorithm.parse(bytes(key, len)), out) }
}

/// Parses the `len` bytes at `der` as a `SubjectPublicKeyInfo` for
/// verification algorithm `id`, boxing it at `out`.
///
/// # Safety
/// As for [`rind_fips_public_key_new`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_public_key_from_spki(
    id: u32,
    der: *const u8,
    len: usize,
    out: *mut *mut PublicKey,
) -> Status {
    let Some(algorithm) = verification(id) else {
        return unsupported();
    };
    // SAFETY: the caller's contract.
    unsafe { put_handle(algorithm.parse_spki(bytes(der, len)), out) }
}

/// The encoding of `key`, writing its length to `len`; it lives as long as
/// the handle.
///
/// # Safety
/// `key` must be live, and `len` valid for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_public_key_bytes(
    key: *const PublicKey,
    len: *mut usize,
) -> *const u8 {
    // SAFETY: the caller's contract.
    let bytes = unsafe { (*key).bytes() };
    // SAFETY: the caller's contract.
    unsafe { put(len, bytes.len()) };
    bytes.as_ptr()
}

/// `key` as a `SubjectPublicKeyInfo`.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_public_key_to_spki(key: *const PublicKey) -> *mut Encoded {
    // SAFETY: the caller's contract.
    encoded(unsafe { (*key).to_spki() })
}

/// Verifies the `signature_len` bytes at `signature` over the `len` bytes
/// at `message` with `key`.
///
/// # Safety
/// `key` must be live, and `message` and `signature` valid for their
/// lengths' reads.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_public_key_verify(
    key: *const PublicKey,
    message: *const u8,
    len: usize,
    signature: *const u8,
    signature_len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, message, signature) =
        unsafe { (&*key, bytes(message, len), bytes(signature, signature_len)) };
    status(key.verify(message, signature))
}

/// Verifies the `signature_len` bytes at `signature` over the message the
/// `len` bytes at `digest` hash with hash `hash`, with `key`.
///
/// # Safety
/// As for [`rind_fips_public_key_verify`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_public_key_verify_digest(
    key: *const PublicKey,
    hash: u32,
    value: *const u8,
    len: usize,
    signature: *const u8,
    signature_len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, value, signature) =
        unsafe { (&*key, bytes(value, len), bytes(signature, signature_len)) };
    status(digest(hash, value).and_then(|digest| key.verify_digest(&digest, signature)))
}

/// A copy of `key`.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_public_key_clone(key: *const PublicKey) -> *mut PublicKey {
    // SAFETY: the caller's contract.
    handle(unsafe { (*key).clone() })
}

free!(rind_fips_public_key_free, PublicKey);

// RSA public keys, which are bound to no algorithm: each verification
// names its own.

/// Refuses an RSA key whose modulus FIPS 186-5 approves for no algorithm:
/// one of an odd number of bits, or under 2048 bits but for the legacy
/// algorithms' 1024.
fn rsa_public_key(key: Result<rsa::PublicKey, Error>) -> Result<PublicKey, Error> {
    ensure(&[T::Rsa]);
    let key = key?;
    rind::fips::check_rsa_modulus(&key, true)?;
    Ok(PublicKey::Rsa(key))
}

/// Parses the PKCS#1 `RSAPublicKey` in the `len` bytes at `der`, boxing it
/// at `out`.
///
/// # Safety
/// `der` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rsa_public_key_new(
    der: *const u8,
    len: usize,
    out: *mut *mut PublicKey,
) -> Status {
    // SAFETY: the caller's contract.
    let der = unsafe { bytes(der, len) };
    // SAFETY: the caller's contract.
    unsafe { put_handle(rsa_public_key(rsa::PublicKey::new(der)), out) }
}

/// Parses the `SubjectPublicKeyInfo` in the `len` bytes at `der` as an RSA
/// public key, boxing it at `out`.
///
/// # Safety
/// As for [`rind_fips_rsa_public_key_new`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rsa_public_key_from_spki(
    der: *const u8,
    len: usize,
    out: *mut *mut PublicKey,
) -> Status {
    // SAFETY: the caller's contract.
    let der = unsafe { bytes(der, len) };
    // SAFETY: the caller's contract.
    unsafe { put_handle(rsa_public_key(rsa::PublicKey::from_spki(der)), out) }
}

/// Loads an RSA public key from its big-endian modulus and exponent,
/// boxing it at `out`.
///
/// # Safety
/// `n` and `e` must be valid for their lengths' reads, and `out` for a
/// write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rsa_public_key_from_components(
    n: *const u8,
    n_len: usize,
    e: *const u8,
    e_len: usize,
    out: *mut *mut PublicKey,
) -> Status {
    // SAFETY: the caller's contract.
    let components = unsafe {
        PublicKeyComponents {
            n: bytes(n, n_len),
            e: bytes(e, e_len),
        }
    };
    let key = rsa_public_key(rsa::PublicKey::from_components(&components));
    // SAFETY: the caller's contract.
    unsafe { put_handle(key, out) }
}

/// The modulus length in bytes of RSA key `key`, or 0 for another key.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rsa_public_key_modulus_len(key: *const PublicKey) -> usize {
    // SAFETY: the caller's contract.
    match unsafe { &*key } {
        PublicKey::Rsa(key) => key.modulus_len(),
        _ => 0,
    }
}

/// Verifies the `signature_len` bytes at `signature` over the `len` bytes
/// at `message` with RSA key `key` and verification algorithm `id`,
/// refusing a modulus below the algorithm's floor or one FIPS 186-5 does
/// not approve for it.
///
/// # Safety
/// As for [`rind_fips_public_key_verify`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rsa_public_key_verify(
    key: *const PublicKey,
    id: u32,
    message: *const u8,
    len: usize,
    signature: *const u8,
    signature_len: usize,
) -> Status {
    let Some((algorithm, legacy_1024)) = rsa_verification(id) else {
        return unsupported();
    };
    // SAFETY: the caller's contract.
    let (key, message, signature) =
        unsafe { (&*key, bytes(message, len), bytes(signature, signature_len)) };
    let PublicKey::Rsa(key) = key else {
        return unsupported();
    };
    status(
        rind::fips::check_rsa_modulus(key, legacy_1024)
            .and_then(|()| key.verify(algorithm, message, signature)),
    )
}

// ECDSA.

fn ecdsa_pct(key: &EcdsaKeyPair) -> Result<(), Error> {
    pct_drawing(
        "pct_ecdsa",
        || key.sign(PCT_MESSAGE),
        |signature| {
            key.public_key()
                .verify(PCT_MESSAGE, signature.as_ref())
                .is_ok()
        },
    )
}

/// Loads an ECDSA key pair for signing algorithm `id` with `load`, boxing
/// it at `out`.
///
/// # Safety
/// `out` must be valid for a write.
unsafe fn ecdsa_load(
    id: u32,
    out: *mut *mut EcdsaKeyPair,
    load: impl FnOnce(&'static ecdsa::SigningAlgorithm) -> Result<EcdsaKeyPair, Error>,
) -> Status {
    let Some(algorithm) = ecdsa_algorithm(id) else {
        return unsupported();
    };
    // SAFETY: the caller's contract.
    scrubbed(Depth::Medium, || unsafe {
        put_handle(load(algorithm), out)
    })
}

/// Generates an ECDSA key pair for signing algorithm `id`, boxing it at
/// `out`, after a pairwise consistency test.
///
/// # Safety
/// `out` must be valid for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ecdsa_generate(id: u32, out: *mut *mut EcdsaKeyPair) -> Status {
    // SAFETY: the caller's contract.
    unsafe {
        ecdsa_load(id, out, |algorithm| {
            let key = EcdsaKeyPair::generate(algorithm)?;
            ecdsa_pct(&key)?;
            Ok(key)
        })
    }
}

/// Loads the PKCS#8 key in the `len` bytes at `der` for ECDSA signing
/// algorithm `id`, boxing it at `out`.
///
/// # Safety
/// `der` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ecdsa_from_pkcs8(
    id: u32,
    der: *const u8,
    len: usize,
    out: *mut *mut EcdsaKeyPair,
) -> Status {
    // SAFETY: the caller's contract.
    let der = unsafe { bytes(der, len) };
    // SAFETY: the caller's contract.
    unsafe {
        ecdsa_load(id, out, |algorithm| {
            EcdsaKeyPair::from_pkcs8(algorithm, der)
        })
    }
}

/// Loads the SEC1 key in the `len` bytes at `der` for ECDSA signing
/// algorithm `id`, boxing it at `out`.
///
/// # Safety
/// As for [`rind_fips_ecdsa_from_pkcs8`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ecdsa_from_sec1(
    id: u32,
    der: *const u8,
    len: usize,
    out: *mut *mut EcdsaKeyPair,
) -> Status {
    // SAFETY: the caller's contract.
    let der = unsafe { bytes(der, len) };
    // SAFETY: the caller's contract.
    unsafe { ecdsa_load(id, out, |algorithm| EcdsaKeyPair::from_sec1(algorithm, der)) }
}

/// Loads the private scalar at `scalar` with its public key at
/// `public_key` for ECDSA signing algorithm `id`, boxing it at `out`.
///
/// # Safety
/// `scalar` and `public_key` must be valid for their lengths' reads, and
/// `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ecdsa_from_scalar_and_public_key(
    id: u32,
    scalar: *const u8,
    scalar_len: usize,
    public_key: *const u8,
    public_key_len: usize,
    out: *mut *mut EcdsaKeyPair,
) -> Status {
    // SAFETY: the caller's contract.
    let (scalar, public_key) =
        unsafe { (bytes(scalar, scalar_len), bytes(public_key, public_key_len)) };
    // SAFETY: the caller's contract.
    unsafe {
        ecdsa_load(id, out, |algorithm| {
            EcdsaKeyPair::from_scalar_and_public_key(algorithm, scalar, public_key)
        })
    }
}

/// `key`'s public key.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ecdsa_public_key(key: *const EcdsaKeyPair) -> *mut PublicKey {
    // SAFETY: the caller's contract.
    let key = unsafe { (*key).public_key() };
    scrubbed(Depth::Medium, || handle(PublicKey::Ecdsa(key.clone())))
}

/// Signs the `len` bytes at `message` with `key`, writing the signature to
/// the `cap` bytes at `out` and its length to `out_len`.
///
/// # Safety
/// `key` must be live, `message` valid for `len` reads, `out` for `cap`
/// writes, and `out_len` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ecdsa_sign(
    key: *const EcdsaKeyPair,
    message: *const u8,
    len: usize,
    out: *mut u8,
    cap: usize,
    out_len: *mut usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, message) = unsafe { (&*key, bytes(message, len)) };
    // SAFETY: the caller's contract.
    scrubbed(Depth::Medium, || unsafe {
        put_signature(key.sign(message), out, cap, out_len)
    })
}

/// Signs the message the `len` bytes at `value` hash with hash `hash`,
/// with `key`, as [`rind_fips_ecdsa_sign`] writes it.
///
/// # Safety
/// As for [`rind_fips_ecdsa_sign`], with `value` for `message`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ecdsa_sign_digest(
    key: *const EcdsaKeyPair,
    hash: u32,
    value: *const u8,
    len: usize,
    out: *mut u8,
    cap: usize,
    out_len: *mut usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, value) = unsafe { (&*key, bytes(value, len)) };
    let digest = digest(hash, value);
    scrubbed(Depth::Medium, || {
        let signature = digest.and_then(|digest| key.sign_digest(&digest));
        // SAFETY: the caller's contract.
        unsafe { put_signature(signature, out, cap, out_len) }
    })
}

/// `key`'s private key as PKCS#8.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ecdsa_to_pkcs8(key: *const EcdsaKeyPair) -> *mut Encoded {
    // SAFETY: the caller's contract.
    scrubbed(Depth::Medium, || encoded(unsafe { (*key).to_pkcs8() }))
}

/// `key`'s private key as a big-endian scalar.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ecdsa_to_scalar(key: *const EcdsaKeyPair) -> *mut Encoded {
    // SAFETY: the caller's contract.
    scrubbed(Depth::Small, || encoded(unsafe { (*key).to_scalar() }))
}

/// `key`'s private key as SEC1.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ecdsa_to_sec1(key: *const EcdsaKeyPair) -> *mut Encoded {
    // SAFETY: the caller's contract.
    scrubbed(Depth::Small, || encoded(unsafe { (*key).to_sec1() }))
}

free!(rind_fips_ecdsa_free, EcdsaKeyPair);

// Ed25519.

fn ed25519_pct(key: &Ed25519KeyPair) -> bool {
    let signature = key.sign(PCT_MESSAGE);
    key.public_key()
        .verify(PCT_MESSAGE, signature.as_ref())
        .is_ok()
}

/// Loads an Ed25519 key pair with `load`, boxing it at `out`.
///
/// # Safety
/// `out` must be valid for a write.
unsafe fn ed25519_load(
    out: *mut *mut Ed25519KeyPair,
    load: impl FnOnce() -> Result<Ed25519KeyPair, Error>,
) -> Status {
    ensure(&[T::Ed25519, T::Sha512]);
    // SAFETY: the caller's contract.
    scrubbed(Depth::Medium, || unsafe { put_handle(load(), out) })
}

/// Generates an Ed25519 key pair, boxing it at `out`, after a pairwise
/// consistency test.
///
/// # Safety
/// `out` must be valid for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ed25519_generate(out: *mut *mut Ed25519KeyPair) -> Status {
    // SAFETY: the caller's contract.
    unsafe {
        ed25519_load(out, || {
            let key = Ed25519KeyPair::generate()?;
            pct("pct_ed25519", || ed25519_pct(&key));
            Ok(key)
        })
    }
}

/// Loads the PKCS#8 key in the `len` bytes at `der`, boxing it at `out`.
///
/// # Safety
/// `der` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ed25519_from_pkcs8(
    der: *const u8,
    len: usize,
    out: *mut *mut Ed25519KeyPair,
) -> Status {
    // SAFETY: the caller's contract.
    let der = unsafe { bytes(der, len) };
    // SAFETY: the caller's contract.
    unsafe { ed25519_load(out, || Ed25519KeyPair::from_pkcs8(der)) }
}

/// Loads the seed in the `len` bytes at `seed`, boxing it at `out`.
///
/// # Safety
/// `seed` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ed25519_from_seed(
    seed: *const u8,
    len: usize,
    out: *mut *mut Ed25519KeyPair,
) -> Status {
    // SAFETY: the caller's contract.
    let seed = unsafe { bytes(seed, len) };
    // SAFETY: the caller's contract.
    unsafe { ed25519_load(out, || Ed25519KeyPair::from_seed(seed)) }
}

/// Loads the seed at `seed`, refused unless `public_key` is its public key,
/// boxing it at `out`.
///
/// # Safety
/// `seed` and `public_key` must be valid for their lengths' reads, and
/// `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ed25519_from_seed_and_public_key(
    seed: *const u8,
    seed_len: usize,
    public_key: *const u8,
    public_key_len: usize,
    out: *mut *mut Ed25519KeyPair,
) -> Status {
    // SAFETY: the caller's contract.
    let (seed, public_key) = unsafe { (bytes(seed, seed_len), bytes(public_key, public_key_len)) };
    // SAFETY: the caller's contract.
    unsafe {
        ed25519_load(out, || {
            Ed25519KeyPair::from_seed_and_public_key(seed, public_key)
        })
    }
}

/// `key`'s public key.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ed25519_public_key(
    key: *const Ed25519KeyPair,
) -> *mut PublicKey {
    // SAFETY: the caller's contract.
    let key = unsafe { (*key).public_key() };
    scrubbed(Depth::Medium, || handle(PublicKey::Ed25519(key.clone())))
}

/// Signs the `len` bytes at `message` with `key`, writing the 64-byte
/// signature to `out`.
///
/// # Safety
/// `key` must be live, `message` valid for `len` reads, and `out` for 64
/// writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ed25519_sign(
    key: *const Ed25519KeyPair,
    message: *const u8,
    len: usize,
    out: *mut u8,
) {
    // SAFETY: the caller's contract.
    let (key, message) = unsafe { (&*key, bytes(message, len)) };
    scrubbed(Depth::Medium, || {
        let signature = key.sign(message);
        // SAFETY: the caller's contract; an Ed25519 signature is 64 bytes.
        unsafe { bytes_mut(out, 64).copy_from_slice(signature.as_ref()) };
    })
}

/// `key`'s private key as PKCS#8 v2, or v1 if `v1`.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ed25519_to_pkcs8(
    key: *const Ed25519KeyPair,
    v1: bool,
) -> *mut Encoded {
    // SAFETY: the caller's contract.
    let key = unsafe { &*key };
    scrubbed(Depth::Medium, || {
        encoded(match v1 {
            true => key.to_pkcs8v1(),
            false => key.to_pkcs8(),
        })
    })
}

/// `key`'s private key's seed.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ed25519_to_seed(key: *const Ed25519KeyPair) -> *mut Encoded {
    // SAFETY: the caller's contract.
    scrubbed(Depth::Small, || encoded(unsafe { (*key).to_seed() }))
}

free!(rind_fips_ed25519_free, Ed25519KeyPair);

// RSA.

fn rsa_pct(key: &RsaKeyPair) -> bool {
    // PKCS#1 v1.5 signs without drawing.
    key.sign(&rsa::sign::PKCS1_SHA256, PCT_MESSAGE)
        .is_ok_and(|signature| {
            key.public_key()
                .verify(&rsa::verify::PKCS1_SHA256, PCT_MESSAGE, signature.as_ref())
                .is_ok()
        })
}

/// Loads an RSA key pair with `load`, refused unless FIPS 186-5 approves its
/// modulus, boxing it at `out`.
///
/// # Safety
/// `out` must be valid for a write.
unsafe fn rsa_load(
    out: *mut *mut RsaKeyPair,
    load: impl FnOnce() -> Result<RsaKeyPair, Error>,
) -> Status {
    ensure(&[T::Rsa, T::Sha256]);
    scrubbed(Depth::Large, || {
        let key = load()
            .and_then(|key| rind::fips::check_rsa_modulus(key.public_key(), false).map(|()| key));
        // SAFETY: the caller's contract.
        unsafe { put_handle(key, out) }
    })
}

/// Generates an RSA key pair of size `size` (`ids::rsa_size`), boxing it at
/// `out`, after a pairwise consistency test.
///
/// # Safety
/// `out` must be valid for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rsa_generate(size: u32, out: *mut *mut RsaKeyPair) -> Status {
    let size = match size {
        ids::rsa_size::RSA_2048 => KeySize::Rsa2048,
        ids::rsa_size::RSA_3072 => KeySize::Rsa3072,
        ids::rsa_size::RSA_4096 => KeySize::Rsa4096,
        ids::rsa_size::RSA_6144 => KeySize::Rsa6144,
        ids::rsa_size::RSA_8192 => KeySize::Rsa8192,
        _ => return unsupported(),
    };
    // SAFETY: the caller's contract.
    unsafe {
        rsa_load(out, || {
            let key = RsaKeyPair::generate(size)?;
            pct("pct_rsa", || rsa_pct(&key));
            Ok(key)
        })
    }
}

/// Loads the PKCS#8 key in the `len` bytes at `der`, boxing it at `out`.
///
/// # Safety
/// `der` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rsa_from_pkcs8(
    der: *const u8,
    len: usize,
    out: *mut *mut RsaKeyPair,
) -> Status {
    // SAFETY: the caller's contract.
    let der = unsafe { bytes(der, len) };
    // SAFETY: the caller's contract.
    unsafe { rsa_load(out, || RsaKeyPair::from_pkcs8(der)) }
}

/// Loads the PKCS#1 key in the `len` bytes at `der`, boxing it at `out`.
///
/// # Safety
/// `der` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rsa_from_pkcs1(
    der: *const u8,
    len: usize,
    out: *mut *mut RsaKeyPair,
) -> Status {
    // SAFETY: the caller's contract.
    let der = unsafe { bytes(der, len) };
    // SAFETY: the caller's contract.
    unsafe { rsa_load(out, || RsaKeyPair::from_pkcs1(der)) }
}

/// `key`'s public key.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rsa_public_key(key: *const RsaKeyPair) -> *mut PublicKey {
    // SAFETY: the caller's contract.
    let key = unsafe { (*key).public_key() };
    scrubbed(Depth::Small, || handle(PublicKey::Rsa(key.clone())))
}

/// Signs the `len` bytes at `message` with `key` and signing algorithm
/// `id`, as [`rind_fips_ecdsa_sign`] writes it.
///
/// # Safety
/// As for [`rind_fips_ecdsa_sign`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rsa_sign(
    key: *const RsaKeyPair,
    id: u32,
    message: *const u8,
    len: usize,
    out: *mut u8,
    cap: usize,
    out_len: *mut usize,
) -> Status {
    let Some(algorithm) = rsa_algorithm(id) else {
        return unsupported();
    };
    // SAFETY: the caller's contract.
    let (key, message) = unsafe { (&*key, bytes(message, len)) };
    scrubbed(Depth::Large, || {
        // SAFETY: the caller's contract.
        unsafe { put_signature(key.sign(algorithm, message), out, cap, out_len) }
    })
}

/// `key`'s private key as PKCS#8.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rsa_to_pkcs8(key: *const RsaKeyPair) -> *mut Encoded {
    // SAFETY: the caller's contract.
    scrubbed(Depth::Medium, || encoded(unsafe { (*key).to_pkcs8() }))
}

free!(rind_fips_rsa_free, RsaKeyPair);

// ML-DSA.

/// An ML-DSA key pair of any parameter set, boxed as a handle.
#[allow(clippy::large_enum_variant)]
pub(crate) enum MlDsa {
    MlDsa44(MlDsaKeyPair<MlDsa44>),
    MlDsa65(MlDsaKeyPair<MlDsa65>),
    MlDsa87(MlDsaKeyPair<MlDsa87>),
}

/// Runs `$body` with `$key` bound to whichever key pair `$pair` holds.
macro_rules! on_ml_dsa {
    ($pair:expr, |$key:ident| $body:expr) => {
        match $pair {
            MlDsa::MlDsa44($key) => $body,
            MlDsa::MlDsa65($key) => $body,
            MlDsa::MlDsa87($key) => $body,
        }
    };
}

/// Runs `load` for the parameter set `set` names (`ids::ml_dsa`), as
/// `load!(set, |P| key_pair)`, or `None` for an unknown `set`.
macro_rules! ml_dsa_load {
    ($set:expr, |$P:ident| $body:expr) => {
        match $set {
            ids::ml_dsa::ML_DSA_44 => {
                type $P = MlDsa44;
                Some($body.map(MlDsa::MlDsa44))
            }
            ids::ml_dsa::ML_DSA_65 => {
                type $P = MlDsa65;
                Some($body.map(MlDsa::MlDsa65))
            }
            ids::ml_dsa::ML_DSA_87 => {
                type $P = MlDsa87;
                Some($body.map(MlDsa::MlDsa87))
            }
            _ => None,
        }
    };
}

impl MlDsa {
    fn pct(&self) -> Result<(), Error> {
        on_ml_dsa!(self, |key| pct_drawing(
            "pct_ml_dsa",
            || key.sign(PCT_MESSAGE),
            |signature| {
                key.public_key()
                    .verify(PCT_MESSAGE, signature.as_ref())
                    .is_ok()
            }
        ))
    }
}

/// Boxes `key` at `out`, or fails for an unknown parameter set.
///
/// # Safety
/// `out` must be valid for a write.
unsafe fn ml_dsa_put(key: Option<Result<MlDsa, Error>>, out: *mut *mut MlDsa) -> Status {
    match key {
        // SAFETY: the caller's contract.
        Some(key) => unsafe { put_handle(key, out) },
        None => unsupported(),
    }
}

/// Generates an ML-DSA key pair of parameter set `set` (`ids::ml_dsa`),
/// boxing it at `out`, after a pairwise consistency test.
///
/// # Safety
/// `out` must be valid for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ml_dsa_generate(set: u32, out: *mut *mut MlDsa) -> Status {
    ensure(&[T::MlDsa]);
    scrubbed(Depth::Large, || {
        let key = ml_dsa_load!(set, |P| MlDsaKeyPair::<P>::generate())
            .map(|key| key.and_then(|key| key.pct().map(|()| key)));
        // SAFETY: the caller's contract.
        unsafe { ml_dsa_put(key, out) }
    })
}

/// Expands the seed in the `len` bytes at `seed` into a key pair of
/// parameter set `set`, boxing it at `out`.
///
/// # Safety
/// `seed` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ml_dsa_from_seed(
    set: u32,
    seed: *const u8,
    len: usize,
    out: *mut *mut MlDsa,
) -> Status {
    ensure(&[T::MlDsa]);
    // SAFETY: the caller's contract.
    let seed = unsafe { bytes(seed, len) };
    scrubbed(Depth::Large, || {
        let key = ml_dsa_load!(set, |P| MlDsaKeyPair::<P>::from_seed(seed));
        // SAFETY: the caller's contract.
        unsafe { ml_dsa_put(key, out) }
    })
}

/// Loads the PKCS#8 key of parameter set `set` in the `len` bytes at `der`,
/// boxing it at `out`.
///
/// # Safety
/// `der` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ml_dsa_from_pkcs8(
    set: u32,
    der: *const u8,
    len: usize,
    out: *mut *mut MlDsa,
) -> Status {
    ensure(&[T::MlDsa]);
    // SAFETY: the caller's contract.
    let der = unsafe { bytes(der, len) };
    scrubbed(Depth::Large, || {
        let key = ml_dsa_load!(set, |P| MlDsaKeyPair::<P>::from_pkcs8(der));
        // SAFETY: the caller's contract.
        unsafe { ml_dsa_put(key, out) }
    })
}

/// `key`'s seed, or null if it was loaded from its expanded form.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ml_dsa_to_seed(key: *const MlDsa) -> *mut Encoded {
    // SAFETY: the caller's contract.
    let key = unsafe { &*key };
    scrubbed(Depth::Small, || {
        on_ml_dsa!(key, |key| key.to_seed()).map_or(core::ptr::null_mut(), encoded)
    })
}

/// Whether `key` has its seed, which it lacks if it was loaded from its
/// expanded form.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ml_dsa_has_seed(key: *const MlDsa) -> bool {
    // SAFETY: the caller's contract.
    let key = unsafe { &*key };
    on_ml_dsa!(key, |key| key.has_seed())
}

/// `key`'s private key as PKCS#8.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ml_dsa_to_pkcs8(key: *const MlDsa) -> *mut Encoded {
    // SAFETY: the caller's contract.
    let key = unsafe { &*key };
    scrubbed(Depth::Medium, || {
        encoded(on_ml_dsa!(key, |key| key.to_pkcs8()))
    })
}

/// `key`'s public key.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ml_dsa_public_key(key: *const MlDsa) -> *mut PublicKey {
    // SAFETY: the caller's contract.
    let key = unsafe { &*key };
    scrubbed(Depth::Medium, || {
        handle(match key {
            MlDsa::MlDsa44(key) => PublicKey::MlDsa44(key.public_key().clone()),
            MlDsa::MlDsa65(key) => PublicKey::MlDsa65(key.public_key().clone()),
            MlDsa::MlDsa87(key) => PublicKey::MlDsa87(key.public_key().clone()),
        })
    })
}

/// Signs the `len` bytes at `message` with `key`, as
/// [`rind_fips_ecdsa_sign`] writes it.
///
/// # Safety
/// As for [`rind_fips_ecdsa_sign`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_ml_dsa_sign(
    key: *const MlDsa,
    message: *const u8,
    len: usize,
    out: *mut u8,
    cap: usize,
    out_len: *mut usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, message) = unsafe { (&*key, bytes(message, len)) };
    scrubbed(Depth::Large, || {
        on_ml_dsa!(key, |key| {
            // SAFETY: the caller's contract.
            unsafe { put_signature(key.sign(message), out, cap, out_len) }
        })
    })
}

free!(rind_fips_ml_dsa_free, MlDsa);
