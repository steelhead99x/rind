// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Hashing: SHA-2 and SHA-3. SHA-1 hashes only inside HMAC and legacy
//! verification, so no service here takes it.
//!
//! A hash carries no SSP, so these services zero no stack, as aws-lc's
//! digests wipe nothing.

use rind::digest::{self, Context};

use crate::abi::{bytes, bytes_mut, free, handle};
use crate::ids::hash;
use crate::selftest::{SelfTest, ensure};

/// The digest algorithm `id` names, after its self-test, or `None` if it
/// names none a digest service takes.
pub(crate) fn algorithm(id: u32) -> Option<&'static digest::Algorithm> {
    let (algorithm, test) = match id {
        hash::SHA256 => (&digest::SHA256, SelfTest::Sha256),
        hash::SHA384 => (&digest::SHA384, SelfTest::Sha512),
        hash::SHA512 => (&digest::SHA512, SelfTest::Sha512),
        hash::SHA512_256 => (&digest::SHA512_256, SelfTest::Sha512),
        hash::SHA3_256 => (&digest::SHA3_256, SelfTest::Sha3),
        hash::SHA3_384 => (&digest::SHA3_384, SelfTest::Sha3),
        hash::SHA3_512 => (&digest::SHA3_512, SelfTest::Sha3),
        _ => return None,
    };
    ensure(&[test]);
    Some(algorithm)
}

/// Hashes the `len` bytes at `data` with algorithm `id`, writing the digest
/// to `out`, which holds 64 bytes, and returning its length, or 0 for an
/// unknown `id`.
///
/// # Safety
/// `data` must be valid for `len` reads, and `out` for 64 writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_digest(
    id: u32,
    data: *const u8,
    len: usize,
    out: *mut u8,
) -> usize {
    let Some(algorithm) = algorithm(id) else {
        return 0;
    };
    // SAFETY: the caller's contract.
    let digest = digest::digest(algorithm, unsafe { bytes(data, len) });
    // SAFETY: the caller's contract; a digest is at most 64 bytes.
    unsafe { bytes_mut(out, digest.as_ref().len()).copy_from_slice(digest.as_ref()) };
    digest.as_ref().len()
}

/// Starts hashing with algorithm `id`, or returns null for an unknown `id`.
#[unsafe(no_mangle)]
pub extern "C" fn rind_fips_digest_new(id: u32) -> *mut Context {
    algorithm(id).map_or(core::ptr::null_mut(), |a| handle(Context::new(a)))
}

/// Adds the `len` bytes at `data` to `context`'s message.
///
/// # Safety
/// `context` must be live, and `data` valid for `len` reads.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_digest_update(
    context: *mut Context,
    data: *const u8,
    len: usize,
) {
    // SAFETY: the caller's contract.
    unsafe { (*context).update(bytes(data, len)) }
}

/// Writes the digest of `context`'s message to `out`, which holds 64
/// bytes, returning its length, and starts a new message.
///
/// # Safety
/// `context` must be live, and `out` valid for 64 writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_digest_finish(context: *mut Context, out: *mut u8) -> usize {
    // SAFETY: the caller's contract.
    let digest = unsafe { (*context).finish() };
    // SAFETY: the caller's contract; a digest is at most 64 bytes.
    unsafe { bytes_mut(out, digest.as_ref().len()).copy_from_slice(digest.as_ref()) };
    digest.as_ref().len()
}

/// A copy of `context`, which hashes on from where it is.
///
/// # Safety
/// `context` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_digest_clone(context: *const Context) -> *mut Context {
    // SAFETY: the caller's contract.
    handle(unsafe { (*context).clone() })
}

free!(rind_fips_digest_free, Context);
