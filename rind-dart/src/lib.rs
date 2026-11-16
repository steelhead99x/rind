// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! The C ABI that the `rind` Dart package's `dart:ffi` bindings call.
//!
//! Every function returns an `isize`: a byte count or zero on success, or a
//! negative `Status` code. Keys and streaming states are boxed handles that
//! the Dart side frees, through a `NativeFinalizer`, with the matching
//! `*_free` function; freeing a key wipes it, as rind wipes its keys.
//! Algorithms are small integer ids, matched by the algorithm types in
//! `lib/src/`, such as `ecdsa.dart`'s `VerificationAlgorithm`.
//!
//! A pointer and length pair may be dangling or null when the length is
//! zero. The Dart side owns every other invariant: pointers are valid for
//! their lengths, outputs do not overlap inputs, and handles are live and
//! of the type each function names.
#![allow(clippy::missing_safety_doc)]
#![warn(clippy::undocumented_unsafe_blocks, unreachable_pub)]

use core::cell::RefCell;
use core::slice;
use std::num::NonZeroU32;

use rind::ecdsa::KeyPair as EcdsaKeyPair;
use rind::ed25519::KeyPair as Ed25519KeyPair;
use rind::rsa::KeyPair as RsaKeyPair;
use rind::{Error, aead, agreement, cipher, digest, ecdsa, ed25519, hkdf, hmac, kem, pbkdf2, rsa};

#[cfg(test)]
mod ctgrind;

/// The negative codes a call returns on failure, one per [`Error`] variant
/// and one of the binding's own.
#[repr(isize)]
enum Status {
    WrongLength = -1,
    KeyRejected = -2,
    BadSignature = -3,
    DecryptFailed = -4,
    RngFailed = -5,
    NotEqual = -6,
    Fault = -7,
    Unsupported = -8,
    /// An argument the Dart side should never pass, such as an unknown
    /// algorithm id.
    Misuse = -10,
}

thread_local! {
    // Why the last call on this thread failed, for the statuses that carry
    // a reason. A Dart isolate stays on one thread while synchronous code
    // runs, so it reads the reason right after the failing call.
    static MESSAGE: RefCell<String> = const { RefCell::new(String::new()) };
}

fn fail(status: Status, message: impl ToString) -> isize {
    MESSAGE.with(|m| *m.borrow_mut() = message.to_string());
    status as isize
}

fn status(error: Error) -> isize {
    match error {
        Error::WrongLength => Status::WrongLength as isize,
        Error::KeyRejected(reason) => fail(Status::KeyRejected, reason),
        Error::BadSignature => Status::BadSignature as isize,
        Error::DecryptFailed => Status::DecryptFailed as isize,
        Error::RngFailed => Status::RngFailed as isize,
        Error::NotEqual => Status::NotEqual as isize,
        Error::Fault => Status::Fault as isize,
        Error::Unsupported => Status::Unsupported as isize,
        other => fail(Status::Fault, format!("{other:?}")),
    }
}

/// A failure of the binding's own contract, rather than of rind.
struct Misuse(&'static str);

enum Failure {
    Rind(Error),
    Misuse(Misuse),
}

impl From<Error> for Failure {
    fn from(error: Error) -> Self {
        Self::Rind(error)
    }
}

impl From<Misuse> for Failure {
    fn from(misuse: Misuse) -> Self {
        Self::Misuse(misuse)
    }
}

/// Runs `f` and folds its result into a return value.
fn run(f: impl FnOnce() -> Result<usize, Failure>) -> isize {
    match f() {
        // A length never exceeds isize::MAX: it is the length of a slice.
        Ok(len) => len as isize,
        Err(Failure::Rind(error)) => status(error),
        Err(Failure::Misuse(Misuse(why))) => fail(Status::Misuse, why),
    }
}

unsafe fn input<'a>(data: *const u8, len: usize) -> &'a [u8] {
    match len {
        0 => &[],
        // SAFETY: the caller passes `len` readable bytes at `data`.
        _ => unsafe { slice::from_raw_parts(data, len) },
    }
}

unsafe fn output<'a>(data: *mut u8, len: usize) -> &'a mut [u8] {
    match len {
        0 => &mut [],
        // SAFETY: the caller passes `len` writable bytes at `data`, which
        // alias nothing else this call reads.
        _ => unsafe { slice::from_raw_parts_mut(data, len) },
    }
}

/// `selector` 0 is the algorithm's own encoding and 1 is a
/// `SubjectPublicKeyInfo`. Any other value is a bug in the binding.
fn own_or_spki(selector: u32) -> Result<bool, Misuse> {
    match selector {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(Misuse("unknown public key encoding")),
    }
}

/// Copies `bytes` to the front of `out`, refusing an `out` too short.
fn write(out: &mut [u8], bytes: &[u8]) -> Result<usize, Failure> {
    out.get_mut(..bytes.len())
        .ok_or(Misuse("output buffer too short"))?
        .copy_from_slice(bytes);
    Ok(bytes.len())
}

unsafe fn handle<'a, T>(handle: *const T) -> &'a T {
    // SAFETY: the caller passes a live handle of this type.
    unsafe { &*handle }
}

unsafe fn handle_mut<'a, T>(handle: *mut T) -> &'a mut T {
    // SAFETY: the caller passes a live handle of this type, which nothing
    // else uses during the call.
    unsafe { &mut *handle }
}

/// Boxes `value` into the handle slot at `out`.
unsafe fn store<T>(out: *mut *mut T, value: T) -> usize {
    // SAFETY: the caller passes a writable slot.
    unsafe { out.write(Box::into_raw(Box::new(value))) };
    0
}

macro_rules! free {
    ($($name:ident: $ty:ty;)*) => {$(
        /// Drops the handle, wiping a key as it frees it.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name(handle: *mut $ty) {
            if !handle.is_null() {
                // SAFETY: a handle comes from `store`, and the Dart side
                // frees each exactly once.
                drop(unsafe { Box::from_raw(handle) });
            }
        }
    )*};
}

free! {
    rind_dart_aead_key_free: aead::Key;
    rind_dart_randomized_nonce_key_free: aead::RandomizedNonceKey;
    rind_dart_aes_cbc_encrypting_key_free: cipher::AesCbcEncryptingKey;
    rind_dart_aes_cbc_decrypting_key_free: cipher::AesCbcDecryptingKey;
    rind_dart_aes_ctr_free: cipher::AesCtr;
    rind_dart_chacha20_free: cipher::ChaCha20;
    rind_dart_digest_context_free: digest::Context;
    rind_dart_hmac_key_free: hmac::Key;
    rind_dart_hmac_context_free: hmac::Context;
    rind_dart_hkdf_salt_free: hkdf::Salt;
    rind_dart_hkdf_prk_free: hkdf::Prk;
    rind_dart_pbkdf2_secret_free: pbkdf2::Secret;
    rind_dart_agreement_private_key_free: agreement::PrivateKey;
    rind_dart_ecdsa_key_pair_free: EcdsaKeyPair;
    rind_dart_ed25519_key_pair_free: Ed25519KeyPair;
    rind_dart_rsa_key_pair_free: RsaKeyPair;
    rind_dart_ecdsa_public_key_free: ecdsa::PublicKey;
    rind_dart_ed25519_public_key_free: ed25519::PublicKey;
    rind_dart_rsa_public_key_free: rsa::PublicKey;
    rind_dart_decapsulation_key_free: kem::DecapsulationKey<kem::MlKem768>;
    rind_dart_encapsulation_key_free: kem::EncapsulationKey<kem::MlKem768>;
    rind_dart_decrypting_key_free: rsa::DecryptingKey;
    rind_dart_encrypting_key_free: rsa::EncryptingKey;
}

macro_rules! public_key_of {
    ($($name:ident: $owner:ty => $key:ty;)*) => {$(
        /// Stores a copy of the key's public key.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name(owner: *const $owner, out: *mut *mut $key) -> isize {
            run(|| {
                // SAFETY: forwarded from the caller.
                let key = unsafe { handle(owner) }.public_key().clone();
                // SAFETY: forwarded from the caller.
                Ok(unsafe { store(out, key) })
            })
        }
    )*};
}

public_key_of! {
    rind_dart_ecdsa_key_pair_public_key: EcdsaKeyPair => ecdsa::PublicKey;
    rind_dart_ed25519_key_pair_public_key: Ed25519KeyPair => ed25519::PublicKey;
    rind_dart_rsa_key_pair_public_key: RsaKeyPair => rsa::PublicKey;
    rind_dart_decrypting_key_public_key: rsa::DecryptingKey => rsa::EncryptingKey;
}

macro_rules! public_key_export {
    ($($(#[$doc:meta])* $name:ident: $key:ty;)*) => {$(
        $(#[$doc])*
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name(
            key: *const $key,
            spki: u32,
            out: *mut u8,
            out_len: usize,
        ) -> isize {
            run(|| {
                let as_spki = own_or_spki(spki)?;
                // SAFETY: forwarded from the caller.
                let (key, out) = unsafe { (handle(key), output(out, out_len)) };
                if as_spki {
                    write(out, key.to_spki().as_ref())
                } else {
                    write(out, key.as_ref())
                }
            })
        }
    )*};
}

public_key_export! {
    /// Writes the public key's X9.62 point when `spki` is 0, or its
    /// `SubjectPublicKeyInfo` when `spki` is 1.
    rind_dart_ecdsa_public_key_export: ecdsa::PublicKey;
    /// Writes the public key's 32 bytes when `spki` is 0, or its
    /// `SubjectPublicKeyInfo` when `spki` is 1.
    rind_dart_ed25519_public_key_export: ed25519::PublicKey;
    /// Writes the public key's PKCS#1 encoding when `spki` is 0, or its
    /// `SubjectPublicKeyInfo` when `spki` is 1.
    rind_dart_rsa_public_key_export: rsa::PublicKey;
    /// Writes the key's PKCS#1 encoding when `spki` is 0, or its
    /// `SubjectPublicKeyInfo` when `spki` is 1.
    rind_dart_encrypting_key_export: rsa::EncryptingKey;
}

macro_rules! public_key_verify {
    ($($name:ident: $key:ty;)*) => {$(
        /// Checks that `signature` is the key's signature of `message`, under
        /// the one algorithm the key is bound to.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name(
            key: *const $key,
            message: *const u8,
            message_len: usize,
            signature: *const u8,
            signature_len: usize,
        ) -> isize {
            run(|| {
                // SAFETY: forwarded from the caller.
                let (key, message, signature) = unsafe {
                    (
                        handle(key),
                        input(message, message_len),
                        input(signature, signature_len),
                    )
                };
                key.verify(message, signature)?;
                Ok(0)
            })
        }
    )*};
}

public_key_verify! {
    rind_dart_ecdsa_public_key_verify: ecdsa::PublicKey;
    rind_dart_ed25519_public_key_verify: ed25519::PublicKey;
}

// Algorithm ids. Legacy algorithms start at 100.

fn aead_algorithm(id: u32) -> Result<&'static aead::Algorithm, Misuse> {
    Ok(match id {
        0 => &aead::AES_128_GCM,
        1 => &aead::AES_192_GCM,
        2 => &aead::AES_256_GCM,
        3 => &aead::CHACHA20_POLY1305,
        _ => return Err(Misuse("unknown AEAD algorithm")),
    })
}

fn cipher_algorithm(id: u32) -> Result<&'static cipher::Algorithm, Misuse> {
    Ok(match id {
        0 => &cipher::AES_128,
        1 => &cipher::AES_192,
        2 => &cipher::AES_256,
        _ => return Err(Misuse("unknown cipher algorithm")),
    })
}

fn digest_algorithm(id: u32) -> Result<&'static digest::Algorithm, Misuse> {
    Ok(match id {
        0 => &digest::SHA256,
        1 => &digest::SHA384,
        2 => &digest::SHA512,
        3 => &digest::SHA512_256,
        4 => &digest::SHA3_256,
        5 => &digest::SHA3_384,
        6 => &digest::SHA3_512,
        100 => &digest::legacy::SHA1,
        101 => &digest::legacy::MD5,
        _ => return Err(Misuse("unknown digest algorithm")),
    })
}

fn hmac_algorithm(id: u32) -> Result<&'static hmac::Algorithm, Misuse> {
    Ok(match id {
        0 => &hmac::HMAC_SHA256,
        1 => &hmac::HMAC_SHA384,
        2 => &hmac::HMAC_SHA512,
        100 => &hmac::legacy::HMAC_SHA1,
        _ => return Err(Misuse("unknown HMAC algorithm")),
    })
}

fn hkdf_algorithm(id: u32) -> Result<&'static hkdf::Algorithm, Misuse> {
    Ok(match id {
        0 => &hkdf::HKDF_SHA256,
        1 => &hkdf::HKDF_SHA384,
        2 => &hkdf::HKDF_SHA512,
        100 => &hkdf::legacy::HKDF_SHA1,
        _ => return Err(Misuse("unknown HKDF algorithm")),
    })
}

fn pbkdf2_algorithm(id: u32) -> Result<&'static pbkdf2::Algorithm, Misuse> {
    Ok(match id {
        0 => &pbkdf2::PBKDF2_HMAC_SHA256,
        1 => &pbkdf2::PBKDF2_HMAC_SHA384,
        2 => &pbkdf2::PBKDF2_HMAC_SHA512,
        100 => &pbkdf2::legacy::PBKDF2_HMAC_SHA1,
        _ => return Err(Misuse("unknown PBKDF2 algorithm")),
    })
}

fn agreement_algorithm(id: u32) -> Result<&'static agreement::Algorithm, Misuse> {
    Ok(match id {
        0 => &agreement::X25519,
        1 => &agreement::ECDH_P256,
        2 => &agreement::ECDH_P384,
        3 => &agreement::ECDH_P521,
        _ => return Err(Misuse("unknown agreement algorithm")),
    })
}

fn ecdsa_algorithm(id: u32) -> Result<&'static ecdsa::SigningAlgorithm, Misuse> {
    Ok(match id {
        0 => &ecdsa::sign::P256_SHA256_ASN1,
        1 => &ecdsa::sign::P256_SHA256_FIXED,
        2 => &ecdsa::sign::P384_SHA384_ASN1,
        3 => &ecdsa::sign::P384_SHA384_FIXED,
        4 => &ecdsa::sign::P521_SHA512_ASN1,
        5 => &ecdsa::sign::P521_SHA512_FIXED,
        _ => return Err(Misuse("unknown ECDSA algorithm")),
    })
}

fn rsa_signing_algorithm(id: u32) -> Result<&'static rsa::SigningAlgorithm, Misuse> {
    Ok(match id {
        0 => &rsa::sign::PKCS1_SHA256,
        1 => &rsa::sign::PKCS1_SHA384,
        2 => &rsa::sign::PKCS1_SHA512,
        3 => &rsa::sign::PSS_SHA256,
        4 => &rsa::sign::PSS_SHA384,
        5 => &rsa::sign::PSS_SHA512,
        _ => return Err(Misuse("unknown RSA signing algorithm")),
    })
}

fn ecdsa_verification_algorithm(id: u32) -> Result<&'static ecdsa::VerificationAlgorithm, Misuse> {
    Ok(match id {
        0 => &ecdsa::verify::P256_SHA256_ASN1,
        1 => &ecdsa::verify::P256_SHA384_ASN1,
        2 => &ecdsa::verify::P256_SHA512_ASN1,
        3 => &ecdsa::verify::P384_SHA256_ASN1,
        4 => &ecdsa::verify::P384_SHA384_ASN1,
        5 => &ecdsa::verify::P384_SHA512_ASN1,
        6 => &ecdsa::verify::P521_SHA256_ASN1,
        7 => &ecdsa::verify::P521_SHA384_ASN1,
        8 => &ecdsa::verify::P521_SHA512_ASN1,
        9 => &ecdsa::verify::P256_SHA256_FIXED,
        10 => &ecdsa::verify::P384_SHA384_FIXED,
        11 => &ecdsa::verify::P521_SHA512_FIXED,
        _ => return Err(Misuse("unknown ECDSA verification algorithm")),
    })
}

fn rsa_verification_algorithm(id: u32) -> Result<&'static rsa::VerificationAlgorithm, Misuse> {
    Ok(match id {
        0 => &rsa::verify::PKCS1_SHA256,
        1 => &rsa::verify::PKCS1_SHA384,
        2 => &rsa::verify::PKCS1_SHA512,
        3 => &rsa::verify::PSS_SHA256,
        4 => &rsa::verify::PSS_SHA384,
        5 => &rsa::verify::PSS_SHA512,
        6 => &rsa::verify::PSS_SHA256_ANY_SALT,
        7 => &rsa::verify::PSS_SHA384_ANY_SALT,
        8 => &rsa::verify::PSS_SHA512_ANY_SALT,
        100 => &rsa::verify::legacy::PKCS1_SHA1,
        101 => &rsa::verify::legacy::PKCS1_1024_SHA1,
        102 => &rsa::verify::legacy::PKCS1_1024_SHA256,
        103 => &rsa::verify::legacy::PKCS1_1024_SHA512,
        104 => &rsa::verify::legacy::PKCS1_3072_SHA384,
        _ => return Err(Misuse("unknown RSA verification algorithm")),
    })
}

fn oaep_algorithm(id: u32) -> Result<&'static rsa::OaepAlgorithm, Misuse> {
    Ok(match id {
        0 => &rsa::OAEP_SHA256,
        1 => &rsa::OAEP_SHA384,
        2 => &rsa::OAEP_SHA512,
        100 => &rsa::legacy::OAEP_SHA1,
        _ => return Err(Misuse("unknown RSA-OAEP algorithm")),
    })
}

fn rsa_key_size(id: u32) -> Result<rsa::KeySize, Misuse> {
    Ok(match id {
        0 => rsa::KeySize::Rsa2048,
        1 => rsa::KeySize::Rsa3072,
        2 => rsa::KeySize::Rsa4096,
        3 => rsa::KeySize::Rsa6144,
        4 => rsa::KeySize::Rsa8192,
        _ => return Err(Misuse("unknown RSA key size")),
    })
}

/// Checks that `id` names ML-KEM-768, the one set these bindings offer.
fn kem_algorithm(id: u32) -> Result<(), Misuse> {
    match id {
        0 => Ok(()),
        _ => Err(Misuse("unknown KEM algorithm")),
    }
}

// --- Errors, CPU, randomness, comparison ---

/// Copies the reason the last failing call on this thread gave into `out`,
/// returning its full length, which may exceed `out_len`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_message(out: *mut u8, out_len: usize) -> isize {
    // SAFETY: forwarded from the caller.
    let out = unsafe { output(out, out_len) };
    MESSAGE.with(|m| {
        let m = m.borrow();
        let n = m.len().min(out.len());
        out[..n].copy_from_slice(&m.as_bytes()[..n]);
        m.len() as isize
    })
}

/// Whether rind runs AES on CPU instructions: 1 if so, 0 if not.
#[unsafe(no_mangle)]
pub extern "C" fn rind_dart_has_aes_hardware() -> isize {
    run(|| Ok(rind::cpu::has_aes_hardware().into()))
}

/// Fills `out` with random bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_rand_fill(out: *mut u8, out_len: usize) -> isize {
    // SAFETY: forwarded from the caller.
    run(|| Ok(rind::rand::fill(unsafe { output(out, out_len) }).map(|()| 0)?))
}

/// Compares `a` and `b` in constant time.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_constant_time_verify(
    a: *const u8,
    a_len: usize,
    b: *const u8,
    b_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (a, b) = unsafe { (input(a, a_len), input(b, b_len)) };
        rind::constant_time::verify(a, b)?;
        Ok(0)
    })
}

// --- AEAD ---

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_aead_key_new(
    algorithm: u32,
    key: *const u8,
    key_len: usize,
    out: *mut *mut aead::Key,
) -> isize {
    run(|| {
        let algorithm = aead_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let key = aead::Key::new(algorithm, unsafe { input(key, key_len) })?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

fn nonce(bytes: &[u8]) -> Result<aead::Nonce, Failure> {
    let bytes = bytes.try_into().map_err(|_| Error::WrongLength)?;
    Ok(aead::Nonce::assume_unique_for_key(bytes))
}

/// Seals the `in_out_len - 16` bytes of plaintext at the front of `in_out`
/// in place, writing the tag into its last 16 bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_aead_seal(
    key: *const aead::Key,
    nonce_bytes: *const u8,
    nonce_len: usize,
    aad: *const u8,
    aad_len: usize,
    in_out: *mut u8,
    in_out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, nonce_bytes, aad, in_out) = unsafe {
            (
                handle(key),
                input(nonce_bytes, nonce_len),
                input(aad, aad_len),
                output(in_out, in_out_len),
            )
        };
        let (plaintext, tag) = in_out
            .split_last_chunk_mut::<16>()
            .ok_or(Misuse("no room for the tag"))?;
        let computed = key.seal_in_place_separate_tag(nonce(nonce_bytes)?, aad, plaintext)?;
        tag.copy_from_slice(computed.as_ref());
        Ok(in_out_len)
    })
}

/// Opens the ciphertext and tag in `in_out` in place, returning the
/// plaintext's length.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_aead_open(
    key: *const aead::Key,
    nonce_bytes: *const u8,
    nonce_len: usize,
    aad: *const u8,
    aad_len: usize,
    in_out: *mut u8,
    in_out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, nonce_bytes, aad, in_out) = unsafe {
            (
                handle(key),
                input(nonce_bytes, nonce_len),
                input(aad, aad_len),
                output(in_out, in_out_len),
            )
        };
        Ok(key.open_in_place(nonce(nonce_bytes)?, aad, in_out)?.len())
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_randomized_nonce_key_new(
    key: *const u8,
    key_len: usize,
    out: *mut *mut aead::RandomizedNonceKey,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let key: &[u8; 32] = unsafe { input(key, key_len) }
            .try_into()
            .map_err(|_| Error::WrongLength)?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, aead::RandomizedNonceKey::new(key)) })
    })
}

/// Seals as [`rind_dart_aead_seal`] does, under a random nonce written to
/// the 24 bytes at `nonce_out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_randomized_nonce_key_seal(
    key: *const aead::RandomizedNonceKey,
    aad: *const u8,
    aad_len: usize,
    in_out: *mut u8,
    in_out_len: usize,
    nonce_out: *mut u8,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, aad, in_out, nonce_out) = unsafe {
            (
                handle(key),
                input(aad, aad_len),
                output(in_out, in_out_len),
                output(nonce_out, 24),
            )
        };
        let len = in_out_len
            .checked_sub(16)
            .ok_or(Misuse("no room for the tag"))?;
        let nonce = key.seal_in_place_append_tag(aad, &mut Room { buf: in_out, len })?;
        nonce_out.copy_from_slice(nonce.as_ref());
        Ok(in_out_len)
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_randomized_nonce_key_open(
    key: *const aead::RandomizedNonceKey,
    nonce_bytes: *const u8,
    nonce_len: usize,
    aad: *const u8,
    aad_len: usize,
    in_out: *mut u8,
    in_out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, nonce_bytes, aad, in_out) = unsafe {
            (
                handle(key),
                input(nonce_bytes, nonce_len),
                input(aad, aad_len),
                output(in_out, in_out_len),
            )
        };
        let nonce: [u8; 24] = nonce_bytes.try_into().map_err(|_| Error::WrongLength)?;
        Ok(key.open_in_place(nonce.into(), aad, in_out)?.len())
    })
}

/// The plaintext at the front of `buf`, which a seal extends in place with
/// its tag, and AES-CBC with its padding.
struct Room<'a> {
    buf: &'a mut [u8],
    len: usize,
}

impl AsMut<[u8]> for Room<'_> {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.buf[..self.len]
    }
}

impl<'b> Extend<&'b u8> for Room<'_> {
    fn extend<I: IntoIterator<Item = &'b u8>>(&mut self, bytes: I) {
        for &byte in bytes {
            // The caller sized `buf` for the tag or padding.
            self.buf[self.len] = byte;
            self.len += 1;
        }
    }
}

// --- Ciphers ---

/// A 16-byte IV or counter block.
fn block(bytes: &[u8]) -> Result<&[u8; 16], Error> {
    bytes.try_into().map_err(|_| Error::WrongLength)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_aes_cbc_encrypting_key_new(
    algorithm: u32,
    key: *const u8,
    key_len: usize,
    out: *mut *mut cipher::AesCbcEncryptingKey,
) -> isize {
    run(|| {
        let algorithm = cipher_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let key = cipher::AesCbcEncryptingKey::new(algorithm, unsafe { input(key, key_len) })?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

/// Encrypts the `len` bytes of plaintext at the front of `in_out` in place
/// under `iv`, padded with PKCS#7 when `pad` is nonzero, and returns the
/// ciphertext's length, which padding makes the next multiple of 16 above
/// `len`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_aes_cbc_encrypt(
    key: *const cipher::AesCbcEncryptingKey,
    iv: *const u8,
    iv_len: usize,
    pad: u32,
    in_out: *mut u8,
    in_out_len: usize,
    len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, iv, in_out) =
            unsafe { (handle(key), input(iv, iv_len), output(in_out, in_out_len)) };
        let iv = cipher::CbcIv::assume_unpredictable(*block(iv)?);
        let padded_len = match pad {
            0 => Some(len),
            _ => (len / 16 + 1).checked_mul(16),
        }
        .filter(|&padded_len| padded_len <= in_out_len)
        .ok_or(Misuse("no room for the plaintext and padding"))?;
        if pad == 0 {
            key.encrypt_blocks(iv, &mut in_out[..len])?;
        } else {
            key.encrypt(iv, &mut Room { buf: in_out, len })?;
        }
        Ok(padded_len)
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_aes_cbc_decrypting_key_new(
    algorithm: u32,
    key: *const u8,
    key_len: usize,
    out: *mut *mut cipher::AesCbcDecryptingKey,
) -> isize {
    run(|| {
        let algorithm = cipher_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let key = cipher::AesCbcDecryptingKey::new(algorithm, unsafe { input(key, key_len) })?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

/// Decrypts `in_out` in place under `iv`, checking and removing its PKCS#7
/// padding when `pad` is nonzero, and returns the plaintext's length.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_aes_cbc_decrypt(
    key: *const cipher::AesCbcDecryptingKey,
    iv: *const u8,
    iv_len: usize,
    pad: u32,
    in_out: *mut u8,
    in_out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, iv, in_out) =
            unsafe { (handle(key), input(iv, iv_len), output(in_out, in_out_len)) };
        let iv = block(iv)?;
        if pad == 0 {
            key.decrypt_blocks(iv, in_out)?;
            return Ok(in_out_len);
        }
        Ok(key.decrypt(iv, in_out)?.len())
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_aes_ctr_new(
    algorithm: u32,
    key: *const u8,
    key_len: usize,
    counter_bits: u32,
    out: *mut *mut cipher::AesCtr,
) -> isize {
    run(|| {
        let algorithm = cipher_algorithm(algorithm)?;
        // rind refuses a width over 128 as wrong, so one over 255 is too.
        let counter_bits = u8::try_from(counter_bits).map_err(|_| Error::WrongLength)?;
        // SAFETY: forwarded from the caller.
        let key = cipher::AesCtr::new(algorithm, unsafe { input(key, key_len) }, counter_bits)?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

/// XORs the keystream from `counter_block` into `in_out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_aes_ctr_apply_keystream(
    key: *const cipher::AesCtr,
    counter_block: *const u8,
    counter_block_len: usize,
    in_out: *mut u8,
    in_out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, counter_block, in_out) = unsafe {
            (
                handle(key),
                input(counter_block, counter_block_len),
                output(in_out, in_out_len),
            )
        };
        key.apply_keystream(block(counter_block)?, in_out)?;
        Ok(in_out_len)
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_chacha20_new(
    key: *const u8,
    key_len: usize,
    out: *mut *mut cipher::ChaCha20,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let key: &[u8; 32] = unsafe { input(key, key_len) }
            .try_into()
            .map_err(|_| Error::WrongLength)?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, cipher::ChaCha20::new(key)) })
    })
}

/// XORs the keystream for `nonce`, from block `counter`, into `in_out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_chacha20_apply_keystream(
    key: *const cipher::ChaCha20,
    nonce: *const u8,
    nonce_len: usize,
    counter: u32,
    in_out: *mut u8,
    in_out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, nonce, in_out) = unsafe {
            (
                handle(key),
                input(nonce, nonce_len),
                output(in_out, in_out_len),
            )
        };
        let nonce = nonce.try_into().map_err(|_| Error::WrongLength)?;
        key.apply_keystream(nonce, counter, in_out)?;
        Ok(in_out_len)
    })
}

// --- Digests ---

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_digest(
    algorithm: u32,
    data: *const u8,
    data_len: usize,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        let algorithm = digest_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let (data, out) = unsafe { (input(data, data_len), output(out, out_len)) };
        write(out, digest::digest(algorithm, data).as_ref())
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_digest_context_new(
    algorithm: u32,
    out: *mut *mut digest::Context,
) -> isize {
    run(|| {
        let context = digest::Context::new(digest_algorithm(algorithm)?);
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, context) })
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_digest_context_update(
    context: *mut digest::Context,
    data: *const u8,
    data_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (context, data) = unsafe { (handle_mut(context), input(data, data_len)) };
        context.update(data);
        Ok(0)
    })
}

/// Writes the digest, and starts the context on a new message.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_digest_context_finish(
    context: *mut digest::Context,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (context, out) = unsafe { (handle_mut(context), output(out, out_len)) };
        write(out, context.finish().as_ref())
    })
}

// --- HMAC ---

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_hmac_key_new(
    algorithm: u32,
    key: *const u8,
    key_len: usize,
    out: *mut *mut hmac::Key,
) -> isize {
    run(|| {
        let algorithm = hmac_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let key = hmac::Key::new(algorithm, unsafe { input(key, key_len) });
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_hmac_sign(
    key: *const hmac::Key,
    data: *const u8,
    data_len: usize,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, data, out) =
            unsafe { (handle(key), input(data, data_len), output(out, out_len)) };
        write(out, hmac::sign(key, data).as_ref())
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_hmac_verify(
    key: *const hmac::Key,
    data: *const u8,
    data_len: usize,
    tag: *const u8,
    tag_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, data, tag) = unsafe { (handle(key), input(data, data_len), input(tag, tag_len)) };
        hmac::verify(key, data, tag)?;
        Ok(0)
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_hmac_context_new(
    key: *const hmac::Key,
    out: *mut *mut hmac::Context,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let context = hmac::Context::with_key(unsafe { handle(key) });
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, context) })
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_hmac_context_update(
    context: *mut hmac::Context,
    data: *const u8,
    data_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (context, data) = unsafe { (handle_mut(context), input(data, data_len)) };
        context.update(data);
        Ok(0)
    })
}

/// Writes the tag and frees the context, which the caller must not free
/// again.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_hmac_context_sign(
    context: *mut hmac::Context,
    out: *mut u8,
    out_len: usize,
) -> isize {
    // SAFETY: a handle from `store`, which the caller gives up.
    let context = unsafe { Box::from_raw(context) };
    run(|| {
        // SAFETY: forwarded from the caller.
        let out = unsafe { output(out, out_len) };
        write(out, context.sign().as_ref())
    })
}

// --- HKDF ---

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_hkdf_salt_new(
    algorithm: u32,
    salt: *const u8,
    salt_len: usize,
    out: *mut *mut hkdf::Salt,
) -> isize {
    run(|| {
        let algorithm = hkdf_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let salt = hkdf::Salt::new(algorithm, unsafe { input(salt, salt_len) });
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, salt) })
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_hkdf_extract(
    salt: *const hkdf::Salt,
    secret: *const u8,
    secret_len: usize,
    out: *mut *mut hkdf::Prk,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let prk = unsafe { handle(salt) }.extract(unsafe { input(secret, secret_len) })?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, prk) })
    })
}

/// Expands `info`, the concatenation of the caller's info parts, to fill
/// `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_hkdf_expand(
    prk: *const hkdf::Prk,
    info: *const u8,
    info_len: usize,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (prk, info, out) =
            unsafe { (handle(prk), input(info, info_len), output(out, out_len)) };
        prk.fill(&[info], out)?;
        Ok(out_len)
    })
}

// --- PBKDF2 ---

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_pbkdf2_secret_new(
    algorithm: u32,
    secret: *const u8,
    secret_len: usize,
    out: *mut *mut pbkdf2::Secret,
) -> isize {
    run(|| {
        let algorithm = pbkdf2_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let secret = pbkdf2::Secret::new(algorithm, unsafe { input(secret, secret_len) });
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, secret) })
    })
}

fn iterations(iterations: u32) -> Result<NonZeroU32, Misuse> {
    NonZeroU32::new(iterations).ok_or(Misuse("zero PBKDF2 iterations"))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_pbkdf2_derive(
    secret: *const pbkdf2::Secret,
    rounds: u32,
    salt: *const u8,
    salt_len: usize,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (secret, salt, out) =
            unsafe { (handle(secret), input(salt, salt_len), output(out, out_len)) };
        secret.derive(iterations(rounds)?, salt, out)?;
        Ok(out_len)
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_pbkdf2_verify(
    secret: *const pbkdf2::Secret,
    rounds: u32,
    salt: *const u8,
    salt_len: usize,
    previous: *const u8,
    previous_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (secret, salt, previous) = unsafe {
            (
                handle(secret),
                input(salt, salt_len),
                input(previous, previous_len),
            )
        };
        secret.verify(iterations(rounds)?, salt, previous)?;
        Ok(0)
    })
}

// --- Key agreement ---

/// Loads a private key: `source` 0 generates one, ignoring `bytes`, 1 takes
/// a scalar, 2 PKCS#8, and 3 SEC1.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_agreement_private_key_new(
    algorithm: u32,
    source: u32,
    bytes: *const u8,
    bytes_len: usize,
    out: *mut *mut agreement::PrivateKey,
) -> isize {
    use agreement::PrivateKey;
    run(|| {
        let algorithm = agreement_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let bytes = unsafe { input(bytes, bytes_len) };
        let key = match source {
            0 => PrivateKey::generate(algorithm),
            1 => PrivateKey::from_scalar(algorithm, bytes),
            2 => PrivateKey::from_pkcs8(algorithm, bytes),
            3 => PrivateKey::from_sec1(algorithm, bytes),
            _ => return Err(Misuse("unknown key source").into()),
        }?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

/// Writes an export of the private key: `what` 0 is its public key, 1 its
/// PKCS#8, and 2 its scalar.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_agreement_private_key_export(
    key: *const agreement::PrivateKey,
    what: u32,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, out) = unsafe { (handle(key), output(out, out_len)) };
        match what {
            0 => write(out, key.public_key().as_ref()),
            1 => write(out, key.to_pkcs8().as_ref()),
            2 => write(out, key.to_scalar().as_ref()),
            _ => Err(Misuse("unknown export").into()),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_agreement_agree(
    key: *const agreement::PrivateKey,
    peer: *const u8,
    peer_len: usize,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, peer, out) =
            unsafe { (handle(key), input(peer, peer_len), output(out, out_len)) };
        write(out, key.agree(peer)?.as_ref())
    })
}

/// Parses a peer's public key, from its bytes when `spki` is 0 or its
/// `SubjectPublicKeyInfo` when `spki` is 1, and writes its bytes when
/// `export` is 0 or its `SubjectPublicKeyInfo` when `export` is 1.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_agreement_public_key(
    algorithm: u32,
    spki: u32,
    bytes: *const u8,
    bytes_len: usize,
    export: u32,
    out: *mut u8,
    out_len: usize,
) -> isize {
    use agreement::PublicKey;
    run(|| {
        let algorithm = agreement_algorithm(algorithm)?;
        let from_spki = own_or_spki(spki)?;
        let as_spki = own_or_spki(export)?;
        // SAFETY: forwarded from the caller.
        let (bytes, out) = unsafe { (input(bytes, bytes_len), output(out, out_len)) };
        let key = if from_spki {
            PublicKey::from_spki(algorithm, bytes)
        } else {
            PublicKey::new(algorithm, bytes)
        }?;
        if as_spki {
            write(out, key.to_spki().as_ref())
        } else {
            write(out, key.as_ref())
        }
    })
}

// --- Signatures ---

/// Loads an ECDSA key pair: `source` 0 generates one, ignoring `bytes`, 1
/// takes PKCS#8, 2 SEC1, and 3 a scalar with `public_key`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_ecdsa_key_pair_new(
    algorithm: u32,
    source: u32,
    bytes: *const u8,
    bytes_len: usize,
    public_key: *const u8,
    public_key_len: usize,
    out: *mut *mut EcdsaKeyPair,
) -> isize {
    run(|| {
        let algorithm = ecdsa_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let (bytes, public_key) =
            unsafe { (input(bytes, bytes_len), input(public_key, public_key_len)) };
        let pair = match source {
            0 => EcdsaKeyPair::generate(algorithm),
            1 => EcdsaKeyPair::from_pkcs8(algorithm, bytes),
            2 => EcdsaKeyPair::from_sec1(algorithm, bytes),
            3 => EcdsaKeyPair::from_scalar_and_public_key(algorithm, bytes, public_key),
            _ => return Err(Misuse("unknown key source").into()),
        }?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, pair) })
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_ecdsa_sign(
    pair: *const EcdsaKeyPair,
    message: *const u8,
    message_len: usize,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (pair, message, out) = unsafe {
            (
                handle(pair),
                input(message, message_len),
                output(out, out_len),
            )
        };
        write(out, pair.sign(message)?.as_ref())
    })
}

/// Writes an export of the key pair: `what` 1 is its PKCS#8, 2 its SEC1,
/// and 3 its scalar.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_ecdsa_key_pair_export(
    pair: *const EcdsaKeyPair,
    what: u32,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (pair, out) = unsafe { (handle(pair), output(out, out_len)) };
        match what {
            1 => write(out, pair.to_pkcs8().as_ref()),
            2 => write(out, pair.to_sec1().as_ref()),
            3 => write(out, pair.to_scalar().as_ref()),
            _ => Err(Misuse("unknown export").into()),
        }
    })
}

/// Parses an ECDSA public key for `algorithm`, from its X9.62 point when
/// `spki` is 0 or its `SubjectPublicKeyInfo` when `spki` is 1.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_ecdsa_public_key_new(
    algorithm: u32,
    spki: u32,
    bytes: *const u8,
    bytes_len: usize,
    out: *mut *mut ecdsa::PublicKey,
) -> isize {
    use ecdsa::PublicKey;
    run(|| {
        let algorithm = ecdsa_verification_algorithm(algorithm)?;
        let from_spki = own_or_spki(spki)?;
        // SAFETY: forwarded from the caller.
        let bytes = unsafe { input(bytes, bytes_len) };
        let key = if from_spki {
            PublicKey::from_spki(algorithm, bytes)
        } else {
            PublicKey::new(algorithm, bytes)
        }?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

/// Loads an Ed25519 key pair: `source` 0 generates one, ignoring `bytes`,
/// 1 takes PKCS#8, 2 a seed, and 3 a seed with `public_key`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_ed25519_key_pair_new(
    source: u32,
    bytes: *const u8,
    bytes_len: usize,
    public_key: *const u8,
    public_key_len: usize,
    out: *mut *mut Ed25519KeyPair,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (bytes, public_key) =
            unsafe { (input(bytes, bytes_len), input(public_key, public_key_len)) };
        let pair = match source {
            0 => Ed25519KeyPair::generate(),
            1 => Ed25519KeyPair::from_pkcs8(bytes),
            2 => Ed25519KeyPair::from_seed(bytes),
            3 => Ed25519KeyPair::from_seed_and_public_key(bytes, public_key),
            _ => return Err(Misuse("unknown key source").into()),
        }?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, pair) })
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_ed25519_sign(
    pair: *const Ed25519KeyPair,
    message: *const u8,
    message_len: usize,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (pair, message, out) = unsafe {
            (
                handle(pair),
                input(message, message_len),
                output(out, out_len),
            )
        };
        write(out, pair.sign(message).as_ref())
    })
}

/// Writes an export of the key pair: `what` 1 is its PKCS#8 v2, 2 its
/// PKCS#8 v1, and 3 its seed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_ed25519_key_pair_export(
    pair: *const Ed25519KeyPair,
    what: u32,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (pair, out) = unsafe { (handle(pair), output(out, out_len)) };
        match what {
            1 => write(out, pair.to_pkcs8().as_ref()),
            2 => write(out, pair.to_pkcs8v1().as_ref()),
            3 => write(out, pair.to_seed().as_ref()),
            _ => Err(Misuse("unknown export").into()),
        }
    })
}

/// Parses an Ed25519 public key, from its 32 bytes when `spki` is 0 or its
/// `SubjectPublicKeyInfo` when `spki` is 1.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_ed25519_public_key_new(
    spki: u32,
    bytes: *const u8,
    bytes_len: usize,
    out: *mut *mut ed25519::PublicKey,
) -> isize {
    use ed25519::PublicKey;
    run(|| {
        let from_spki = own_or_spki(spki)?;
        // SAFETY: forwarded from the caller.
        let bytes = unsafe { input(bytes, bytes_len) };
        let key = if from_spki {
            PublicKey::from_spki(bytes)
        } else {
            PublicKey::new(bytes)
        }?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

/// Loads an RSA key pair: `source` 0 generates one of `size`, ignoring
/// `bytes`, 1 takes PKCS#8, and 2 PKCS#1.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_rsa_key_pair_new(
    source: u32,
    size: u32,
    bytes: *const u8,
    bytes_len: usize,
    out: *mut *mut RsaKeyPair,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let bytes = unsafe { input(bytes, bytes_len) };
        let pair = match source {
            0 => RsaKeyPair::generate(rsa_key_size(size)?),
            1 => RsaKeyPair::from_pkcs8(bytes),
            2 => RsaKeyPair::from_pkcs1(bytes),
            _ => return Err(Misuse("unknown key source").into()),
        }?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, pair) })
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_rsa_sign(
    pair: *const RsaKeyPair,
    algorithm: u32,
    message: *const u8,
    message_len: usize,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        let algorithm = rsa_signing_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let (pair, message, out) = unsafe {
            (
                handle(pair),
                input(message, message_len),
                output(out, out_len),
            )
        };
        write(out, pair.sign(algorithm, message)?.as_ref())
    })
}

/// Writes the key pair's PKCS#8 when `what` is 1.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_rsa_key_pair_export(
    pair: *const RsaKeyPair,
    what: u32,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (pair, out) = unsafe { (handle(pair), output(out, out_len)) };
        match what {
            1 => write(out, pair.to_pkcs8().as_ref()),
            _ => Err(Misuse("unknown export").into()),
        }
    })
}

/// Parses an RSA public key: `source` 0 takes PKCS#1, 1 a
/// `SubjectPublicKeyInfo`, and 2 a modulus in `bytes` with the exponent in
/// `exponent`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_rsa_public_key_new(
    source: u32,
    bytes: *const u8,
    bytes_len: usize,
    exponent: *const u8,
    exponent_len: usize,
    out: *mut *mut rsa::PublicKey,
) -> isize {
    use rsa::PublicKey;
    run(|| {
        // SAFETY: forwarded from the caller.
        let (bytes, exponent) = unsafe { (input(bytes, bytes_len), input(exponent, exponent_len)) };
        let key = match source {
            0 => PublicKey::new(bytes),
            1 => PublicKey::from_spki(bytes),
            2 => PublicKey::from_components(&rsa::PublicKeyComponents {
                n: bytes,
                e: exponent,
            }),
            _ => return Err(Misuse("unknown key source").into()),
        }?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

/// Checks that `signature` is the key's signature of `message` under
/// `algorithm`, refusing a modulus below that algorithm's floor.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_rsa_public_key_verify(
    key: *const rsa::PublicKey,
    algorithm: u32,
    message: *const u8,
    message_len: usize,
    signature: *const u8,
    signature_len: usize,
) -> isize {
    run(|| {
        let algorithm = rsa_verification_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let (key, message, signature) = unsafe {
            (
                handle(key),
                input(message, message_len),
                input(signature, signature_len),
            )
        };
        key.verify(algorithm, message, signature)?;
        Ok(0)
    })
}

/// The modulus's length in bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_rsa_public_key_modulus_len(key: *const rsa::PublicKey) -> isize {
    // SAFETY: forwarded from the caller.
    run(|| Ok(unsafe { handle(key) }.modulus_len()))
}

// --- Key encapsulation ---

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_decapsulation_key_generate(
    algorithm: u32,
    out: *mut *mut kem::DecapsulationKey<kem::MlKem768>,
) -> isize {
    run(|| {
        kem_algorithm(algorithm)?;
        let key = kem::DecapsulationKey::generate()?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_decapsulation_key_public_key(
    key: *const kem::DecapsulationKey<kem::MlKem768>,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, out) = unsafe { (handle(key), output(out, out_len)) };
        write(out, key.public_key().as_ref())
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_decapsulate(
    key: *const kem::DecapsulationKey<kem::MlKem768>,
    ciphertext: *const u8,
    ciphertext_len: usize,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, ciphertext, out) = unsafe {
            (
                handle(key),
                input(ciphertext, ciphertext_len),
                output(out, out_len),
            )
        };
        let ciphertext = kem::Ciphertext::new(ciphertext)?;
        write(out, key.decapsulate(&ciphertext).as_ref())
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_encapsulation_key_new(
    algorithm: u32,
    bytes: *const u8,
    bytes_len: usize,
    out: *mut *mut kem::EncapsulationKey<kem::MlKem768>,
) -> isize {
    run(|| {
        kem_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let key = kem::EncapsulationKey::new(unsafe { input(bytes, bytes_len) })?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

/// Writes the ciphertext to `ciphertext` and the shared secret to `secret`,
/// returning the ciphertext's length.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_encapsulate(
    key: *const kem::EncapsulationKey<kem::MlKem768>,
    ciphertext: *mut u8,
    ciphertext_len: usize,
    secret: *mut u8,
    secret_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, ciphertext_out, secret_out) = unsafe {
            (
                handle(key),
                output(ciphertext, ciphertext_len),
                output(secret, secret_len),
            )
        };
        let (ciphertext, secret) = key.encapsulate()?;
        write(secret_out, secret.as_ref())?;
        write(ciphertext_out, ciphertext.as_ref())
    })
}

// --- RSA encryption ---

/// Loads an RSA-OAEP decrypting key: `source` 0 generates one of `size`,
/// ignoring `bytes`, 1 takes PKCS#8, and 2 PKCS#1.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_decrypting_key_new(
    algorithm: u32,
    source: u32,
    size: u32,
    bytes: *const u8,
    bytes_len: usize,
    out: *mut *mut rsa::DecryptingKey,
) -> isize {
    use rsa::DecryptingKey;
    run(|| {
        let algorithm = oaep_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let bytes = unsafe { input(bytes, bytes_len) };
        let key = match source {
            0 => DecryptingKey::generate(algorithm, rsa_key_size(size)?),
            1 => DecryptingKey::from_pkcs8(algorithm, bytes),
            2 => DecryptingKey::from_pkcs1(algorithm, bytes),
            _ => return Err(Misuse("unknown key source").into()),
        }?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_decrypt(
    key: *const rsa::DecryptingKey,
    ciphertext: *const u8,
    ciphertext_len: usize,
    label: *const u8,
    label_len: usize,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, ciphertext, label, out) = unsafe {
            (
                handle(key),
                input(ciphertext, ciphertext_len),
                input(label, label_len),
                output(out, out_len),
            )
        };
        write(out, key.decrypt(ciphertext, label)?.as_ref())
    })
}

/// Writes the key's PKCS#8 when `what` is 1.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_decrypting_key_export(
    key: *const rsa::DecryptingKey,
    what: u32,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, out) = unsafe { (handle(key), output(out, out_len)) };
        match what {
            1 => write(out, key.to_pkcs8().as_ref()),
            _ => Err(Misuse("unknown export").into()),
        }
    })
}

/// Parses an RSA-OAEP encrypting key: `source` 0 takes PKCS#1, 1 a
/// `SubjectPublicKeyInfo`, and 2 a modulus in `bytes` with the exponent in
/// `exponent`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_encrypting_key_new(
    algorithm: u32,
    source: u32,
    bytes: *const u8,
    bytes_len: usize,
    exponent: *const u8,
    exponent_len: usize,
    out: *mut *mut rsa::EncryptingKey,
) -> isize {
    use rsa::EncryptingKey;
    run(|| {
        let algorithm = oaep_algorithm(algorithm)?;
        // SAFETY: forwarded from the caller.
        let (bytes, exponent) = unsafe { (input(bytes, bytes_len), input(exponent, exponent_len)) };
        let key = match source {
            0 => EncryptingKey::new(algorithm, bytes),
            1 => EncryptingKey::from_spki(algorithm, bytes),
            2 => EncryptingKey::from_components(
                algorithm,
                &rsa::PublicKeyComponents {
                    n: bytes,
                    e: exponent,
                },
            ),
            _ => return Err(Misuse("unknown key source").into()),
        }?;
        // SAFETY: forwarded from the caller.
        Ok(unsafe { store(out, key) })
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_encrypt(
    key: *const rsa::EncryptingKey,
    message: *const u8,
    message_len: usize,
    label: *const u8,
    label_len: usize,
    out: *mut u8,
    out_len: usize,
) -> isize {
    run(|| {
        // SAFETY: forwarded from the caller.
        let (key, message, label, out) = unsafe {
            (
                handle(key),
                input(message, message_len),
                input(label, label_len),
                output(out, out_len),
            )
        };
        write(out, key.encrypt(message, label)?.as_ref())
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_dart_encrypting_key_max_message_len(
    key: *const rsa::EncryptingKey,
) -> isize {
    // SAFETY: forwarded from the caller.
    run(|| Ok(unsafe { handle(key) }.max_message_len()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kem_refuses_an_unknown_algorithm() {
        let mut key = std::ptr::null_mut();
        // SAFETY: `key` is a writable handle slot.
        let status = unsafe { rind_dart_decapsulation_key_generate(1, &mut key) };
        assert_eq!(status, Status::Misuse as isize);
        assert!(key.is_null());
    }

    #[test]
    fn an_unknown_public_key_encoding_is_misuse() {
        let mut ecdsa = std::ptr::null_mut();
        let mut ed25519 = std::ptr::null_mut();
        // SAFETY: length zero, so the null pointers are not read, and each
        // selector is rejected before a handle is.
        let status =
            unsafe { rind_dart_ecdsa_public_key_new(0, 2, std::ptr::null(), 0, &mut ecdsa) };
        assert_eq!(status, Status::Misuse as isize);
        assert!(ecdsa.is_null());
        // SAFETY: as above.
        let status =
            unsafe { rind_dart_ed25519_public_key_new(2, std::ptr::null(), 0, &mut ed25519) };
        assert_eq!(status, Status::Misuse as isize);
        assert!(ed25519.is_null());
        // SAFETY: as above.
        let status = unsafe {
            rind_dart_ecdsa_public_key_export(std::ptr::null(), 2, std::ptr::null_mut(), 0)
        };
        assert_eq!(status, Status::Misuse as isize);
        // SAFETY: as above.
        let status = unsafe {
            rind_dart_ed25519_public_key_export(std::ptr::null(), 2, std::ptr::null_mut(), 0)
        };
        assert_eq!(status, Status::Misuse as isize);
        // SAFETY: as above.
        let status = unsafe {
            rind_dart_rsa_public_key_export(std::ptr::null(), 2, std::ptr::null_mut(), 0)
        };
        assert_eq!(status, Status::Misuse as isize);
        // SAFETY: as above.
        let status = unsafe {
            rind_dart_encrypting_key_export(std::ptr::null(), 2, std::ptr::null_mut(), 0)
        };
        assert_eq!(status, Status::Misuse as isize);
        // SAFETY: as above.
        let status = unsafe {
            rind_dart_agreement_public_key(0, 2, std::ptr::null(), 0, 0, std::ptr::null_mut(), 0)
        };
        assert_eq!(status, Status::Misuse as isize);
        // SAFETY: as above.
        let status = unsafe {
            rind_dart_agreement_public_key(0, 0, std::ptr::null(), 0, 2, std::ptr::null_mut(), 0)
        };
        assert_eq!(status, Status::Misuse as isize);
    }
}
