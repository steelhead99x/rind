// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Key agreement: ECDH on P-256, P-384, and P-521, SP 800-56A's shared
//! secret computation. X25519 is not approved, so no service takes it.
//!
//! A generated key passes SP 800-56A section 5.6.2.1.4's pairwise
//! consistency test: its public key recomputes from its private scalar. A
//! peer's key passes section 5.6.2.3.3's full validation as rind parses it,
//! refused off the curve.

use rind::Error;
use rind::agreement::{self, PrivateKey, PublicKey};

use crate::abi::{Encoded, Status, bytes, bytes_mut, encoded, free, handle, put, status};
use crate::ids::curve;
use crate::scrub::{Depth, scrubbed};
use crate::selftest::{SelfTest, ensure, pct};

/// The longest public key: P-521's uncompressed point.
const MAX_PUBLIC_KEY_LEN: usize = 133;

/// The ECDH algorithm on the curve `id` names, after its self-test.
fn algorithm(id: u32) -> Option<&'static agreement::Algorithm> {
    let algorithm = match id {
        curve::P256 => &agreement::ECDH_P256,
        curve::P384 => &agreement::ECDH_P384,
        curve::P521 => &agreement::ECDH_P521,
        _ => return None,
    };
    ensure(&[SelfTest::Ecdh]);
    Some(algorithm)
}

/// Writes the handle `make` returns to `out`, zeroing the stack it used.
///
/// # Safety
/// `out` must be valid for a write.
unsafe fn new_key(
    id: u32,
    out: *mut *mut PrivateKey,
    make: impl FnOnce(&'static agreement::Algorithm) -> Result<PrivateKey, Error>,
) -> Status {
    let Some(algorithm) = algorithm(id) else {
        return status(Err(Error::Unsupported));
    };
    scrubbed(Depth::Medium, || {
        status(make(algorithm).map(|key| {
            // SAFETY: the caller's contract.
            unsafe { put(out, handle(key)) }
        }))
    })
}

/// Generates a private key on the curve `id` names, writing its handle to
/// `out`, after the pairwise consistency test.
///
/// # Safety
/// `out` must be valid for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_agreement_generate(
    id: u32,
    out: *mut *mut PrivateKey,
) -> Status {
    // SAFETY: the caller's contract.
    unsafe {
        new_key(id, out, |algorithm| {
            let key = PrivateKey::generate(algorithm)?;
            pct("pct_ecdh", || {
                PrivateKey::from_scalar(algorithm, key.to_scalar().as_ref())
                    .is_ok_and(|again| again.public_key().as_ref() == key.public_key().as_ref())
            });
            Ok(key)
        })
    }
}

/// Loads a private key on the curve `id` names from the `len` bytes at
/// `scalar`, writing its handle to `out`.
///
/// # Safety
/// `scalar` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_agreement_from_scalar(
    id: u32,
    scalar: *const u8,
    len: usize,
    out: *mut *mut PrivateKey,
) -> Status {
    // SAFETY: the caller's contract.
    let scalar = unsafe { bytes(scalar, len) };
    // SAFETY: the caller's contract.
    unsafe {
        new_key(id, out, |algorithm| {
            PrivateKey::from_scalar(algorithm, scalar)
        })
    }
}

/// Loads a PKCS#8 private key on the curve `id` names from the `len` bytes
/// at `der`, writing its handle to `out`.
///
/// # Safety
/// `der` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_agreement_from_pkcs8(
    id: u32,
    der: *const u8,
    len: usize,
    out: *mut *mut PrivateKey,
) -> Status {
    // SAFETY: the caller's contract.
    let der = unsafe { bytes(der, len) };
    // SAFETY: the caller's contract.
    unsafe { new_key(id, out, |algorithm| PrivateKey::from_pkcs8(algorithm, der)) }
}

/// Loads a SEC1 private key on the curve `id` names from the `len` bytes at
/// `der`, writing its handle to `out`.
///
/// # Safety
/// `der` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_agreement_from_sec1(
    id: u32,
    der: *const u8,
    len: usize,
    out: *mut *mut PrivateKey,
) -> Status {
    // SAFETY: the caller's contract.
    let der = unsafe { bytes(der, len) };
    // SAFETY: the caller's contract.
    unsafe { new_key(id, out, |algorithm| PrivateKey::from_sec1(algorithm, der)) }
}

/// Writes `key`'s public key to `out`, which holds 133 bytes, returning its
/// length.
///
/// # Safety
/// `key` must be live, and `out` valid for 133 writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_agreement_public_key(
    key: *const PrivateKey,
    out: *mut u8,
) -> usize {
    // SAFETY: the caller's contract.
    let public = unsafe { (*key).public_key().as_ref() };
    // SAFETY: the caller's contract; a public key is at most 133 bytes.
    unsafe { bytes_mut(out, public.len()).copy_from_slice(public) };
    public.len()
}

/// Agrees on a secret between `key` and the `len` bytes at `peer`, writing
/// its handle to `out`.
///
/// # Safety
/// `key` must be live, `peer` valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_agreement_agree(
    key: *const PrivateKey,
    peer: *const u8,
    len: usize,
    out: *mut *mut Encoded,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, peer) = unsafe { (&*key, bytes(peer, len)) };
    scrubbed(Depth::Medium, || {
        status(key.agree(peer).map(|secret| {
            // SAFETY: the caller's contract.
            unsafe { put(out, encoded(secret)) }
        }))
    })
}

/// `key` as PKCS#8.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_agreement_to_pkcs8(key: *const PrivateKey) -> *mut Encoded {
    // SAFETY: the caller's contract.
    let key = unsafe { &*key };
    scrubbed(Depth::Medium, || encoded(key.to_pkcs8()))
}

/// `key` as its scalar.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_agreement_to_scalar(key: *const PrivateKey) -> *mut Encoded {
    // SAFETY: the caller's contract.
    let key = unsafe { &*key };
    scrubbed(Depth::Medium, || encoded(key.to_scalar()))
}

free!(rind_fips_agreement_key_free, PrivateKey);

/// Writes the public key `parse` returns to `out`, which holds 133 bytes,
/// and its length to `len`.
///
/// # Safety
/// `out` must be valid for 133 writes, and `len` for a write.
unsafe fn write_public(
    id: u32,
    out: *mut u8,
    len: *mut usize,
    parse: impl FnOnce(&'static agreement::Algorithm) -> Result<PublicKey, Error>,
) -> Status {
    let Some(algorithm) = algorithm(id) else {
        return status(Err(Error::Unsupported));
    };
    status(parse(algorithm).map(|key| {
        let key = key.as_ref();
        debug_assert!(key.len() <= MAX_PUBLIC_KEY_LEN);
        // SAFETY: the caller's contract, and `key` fits.
        unsafe {
            bytes_mut(out, key.len()).copy_from_slice(key);
            put(len, key.len());
        }
    }))
}

/// Parses a peer's public key on the curve `id` names from the `len` bytes
/// at `key`, writing it uncompressed to `out`, which holds 133 bytes, and
/// its length to `out_len`.
///
/// # Safety
/// `key` must be valid for `len` reads, `out` for 133 writes, and `out_len`
/// for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_agreement_public_key_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut u8,
    out_len: *mut usize,
) -> Status {
    // SAFETY: the caller's contract.
    let key = unsafe { bytes(key, len) };
    // SAFETY: the caller's contract.
    unsafe { write_public(id, out, out_len, |algorithm| PublicKey::new(algorithm, key)) }
}

/// As [`rind_fips_agreement_public_key_new`], from a
/// `SubjectPublicKeyInfo`.
///
/// # Safety
/// As for [`rind_fips_agreement_public_key_new`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_agreement_public_key_from_spki(
    id: u32,
    der: *const u8,
    len: usize,
    out: *mut u8,
    out_len: *mut usize,
) -> Status {
    // SAFETY: the caller's contract.
    let der = unsafe { bytes(der, len) };
    // SAFETY: the caller's contract.
    unsafe {
        write_public(id, out, out_len, |algorithm| {
            PublicKey::from_spki(algorithm, der)
        })
    }
}

/// The `SubjectPublicKeyInfo` of the public key on the curve `id` names in
/// the `len` bytes at `key`, or null if it is not one.
///
/// # Safety
/// `key` must be valid for `len` reads.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_agreement_public_key_to_spki(
    id: u32,
    key: *const u8,
    len: usize,
) -> *mut Encoded {
    // SAFETY: the caller's contract.
    let key = unsafe { bytes(key, len) };
    algorithm(id)
        .and_then(|algorithm| PublicKey::new(algorithm, key).ok())
        .map_or(core::ptr::null_mut(), |key| encoded(key.to_spki()))
}
