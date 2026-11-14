// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! HMAC, HKDF, and PBKDF2, over SHA-1 and SHA-2. SHA-1 serves all three,
//! as aws-lc approves it, since none relies on its collision resistance.
//!
//! HKDF refuses an empty salt or info, which aws-lc's service indicator
//! does not approve. PBKDF2 refuses what SP 800-132 and aws-lc's service
//! indicator do not approve: a salt under 16 bytes, fewer than 1000
//! iterations, a derived key under 112 bits, or a password under 14 bytes.

use core::num::NonZeroU32;

use rind::{Error, hkdf, hmac, pbkdf2};

use crate::abi::{Bytes, Status, byte_list, bytes, bytes_mut, free, handle, put, status};
use crate::ids::hash;
use crate::scrub::{Depth, scrubbed};
use crate::selftest::{SelfTest, ensure};

/// The self-test of the hash `id` names, which HMAC, HKDF, or PBKDF2 runs
/// on, or `None` if none of them takes it.
fn hash_test(id: u32) -> Option<SelfTest> {
    match id {
        hash::SHA1 => Some(SelfTest::Sha1),
        hash::SHA256 => Some(SelfTest::Sha256),
        hash::SHA384 | hash::SHA512 => Some(SelfTest::Sha512),
        _ => None,
    }
}

/// The HMAC over the hash `id` names, after its self-tests.
pub(crate) fn hmac_algorithm(id: u32) -> Option<&'static hmac::Algorithm> {
    let algorithm = match id {
        hash::SHA1 => &hmac::legacy::HMAC_SHA1,
        hash::SHA256 => &hmac::HMAC_SHA256,
        hash::SHA384 => &hmac::HMAC_SHA384,
        hash::SHA512 => &hmac::HMAC_SHA512,
        _ => return None,
    };
    ensure(&[hash_test(id)?, SelfTest::Hmac]);
    Some(algorithm)
}

/// The HKDF over the hash `id` names, after its self-tests.
fn hkdf_algorithm(id: u32) -> Option<&'static hkdf::Algorithm> {
    let algorithm = match id {
        hash::SHA1 => &hkdf::legacy::HKDF_SHA1,
        hash::SHA256 => &hkdf::HKDF_SHA256,
        hash::SHA384 => &hkdf::HKDF_SHA384,
        hash::SHA512 => &hkdf::HKDF_SHA512,
        _ => return None,
    };
    ensure(&[hash_test(id)?, SelfTest::Hmac, SelfTest::Hkdf]);
    Some(algorithm)
}

/// The PBKDF2 over the hash `id` names, after its self-tests.
fn pbkdf2_algorithm(id: u32) -> Option<&'static pbkdf2::Algorithm> {
    let algorithm = match id {
        hash::SHA1 => &pbkdf2::legacy::PBKDF2_HMAC_SHA1,
        hash::SHA256 => &pbkdf2::PBKDF2_HMAC_SHA256,
        hash::SHA384 => &pbkdf2::PBKDF2_HMAC_SHA384,
        hash::SHA512 => &pbkdf2::PBKDF2_HMAC_SHA512,
        _ => return None,
    };
    ensure(&[hash_test(id)?, SelfTest::Hmac, SelfTest::Pbkdf2]);
    Some(algorithm)
}

/// Boxes what `make` returns as a handle, zeroing the stack it used.
fn new_handle<T>(make: impl FnOnce() -> T) -> *mut T {
    scrubbed(Depth::Small, || handle(make()))
}

/// Writes `tag` to `out`, which holds 64 bytes, returning its length.
///
/// # Safety
/// `out` must be valid for 64 writes.
unsafe fn write_tag(tag: &hmac::Tag, out: *mut u8) -> usize {
    let tag = tag.as_ref();
    // SAFETY: the caller's contract; a tag is at most 64 bytes.
    unsafe { bytes_mut(out, tag.len()).copy_from_slice(tag) };
    tag.len()
}

/// An HMAC key for the hash `id` names, from the `len` bytes at `key`, or
/// null for an unknown `id`.
///
/// # Safety
/// `key` must be valid for `len` reads.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hmac_key_new(
    id: u32,
    key: *const u8,
    len: usize,
) -> *mut hmac::Key {
    let Some(algorithm) = hmac_algorithm(id) else {
        return core::ptr::null_mut();
    };
    // SAFETY: the caller's contract.
    let key = unsafe { bytes(key, len) };
    new_handle(|| hmac::Key::new(algorithm, key))
}

/// A copy of `key`.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hmac_key_clone(key: *const hmac::Key) -> *mut hmac::Key {
    // SAFETY: the caller's contract.
    new_handle(|| unsafe { (*key).clone() })
}

/// Writes the tag of the `len` bytes at `data` under `key` to `out`, which
/// holds 64 bytes, returning its length.
///
/// # Safety
/// `key` must be live, `data` valid for `len` reads, and `out` for 64
/// writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hmac_sign(
    key: *const hmac::Key,
    data: *const u8,
    len: usize,
    out: *mut u8,
) -> usize {
    // SAFETY: the caller's contract.
    let (key, data) = unsafe { (&*key, bytes(data, len)) };
    // SAFETY: the caller's contract.
    scrubbed(Depth::Small, || unsafe {
        write_tag(&hmac::sign(key, data), out)
    })
}

/// Checks that the `tag_len` bytes at `tag` are the tag of the `len` bytes
/// at `data` under `key`.
///
/// # Safety
/// `key` must be live, and `data` and `tag` valid for their lengths' reads.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hmac_verify(
    key: *const hmac::Key,
    data: *const u8,
    len: usize,
    tag: *const u8,
    tag_len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, data, tag) = unsafe { (&*key, bytes(data, len), bytes(tag, tag_len)) };
    scrubbed(Depth::Small, || status(hmac::verify(key, data, tag)))
}

/// Starts a tag computation under `key`.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hmac_context_new(key: *const hmac::Key) -> *mut hmac::Context {
    // SAFETY: the caller's contract.
    new_handle(|| hmac::Context::with_key(unsafe { &*key }))
}

/// Adds the `len` bytes at `data` to `context`'s message.
///
/// # Safety
/// `context` must be live, and `data` valid for `len` reads.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hmac_context_update(
    context: *mut hmac::Context,
    data: *const u8,
    len: usize,
) {
    // SAFETY: the caller's contract.
    let (context, data) = unsafe { (&mut *context, bytes(data, len)) };
    scrubbed(Depth::Small, || context.update(data))
}

/// A copy of `context`, which computes on from where it is.
///
/// # Safety
/// `context` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hmac_context_clone(
    context: *const hmac::Context,
) -> *mut hmac::Context {
    // SAFETY: the caller's contract.
    new_handle(|| unsafe { (*context).clone() })
}

/// Writes the tag of `context`'s message to `out`, which holds 64 bytes,
/// returning its length, and frees `context`.
///
/// # Safety
/// `context` must be live, and not used again, and `out` valid for 64
/// writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hmac_context_sign(
    context: *mut hmac::Context,
    out: *mut u8,
) -> usize {
    // SAFETY: the caller's contract.
    let context = unsafe { Box::from_raw(context) };
    // SAFETY: the caller's contract.
    scrubbed(Depth::Small, || unsafe { write_tag(&context.sign(), out) })
}

free!(rind_fips_hmac_key_free, hmac::Key);
free!(rind_fips_hmac_context_free, hmac::Context);

/// An HKDF salt, and whether it is empty, which extracting refuses.
pub(crate) struct Salt {
    salt: hkdf::Salt,
    empty: bool,
}

/// An HKDF salt for the hash `id` names, from the `len` bytes at `value`,
/// or null for an unknown `id`.
///
/// # Safety
/// `value` must be valid for `len` reads.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hkdf_salt_new(
    id: u32,
    value: *const u8,
    len: usize,
) -> *mut Salt {
    let Some(algorithm) = hkdf_algorithm(id) else {
        return core::ptr::null_mut();
    };
    // SAFETY: the caller's contract.
    let value = unsafe { bytes(value, len) };
    new_handle(|| Salt {
        salt: hkdf::Salt::new(algorithm, value),
        empty: value.is_empty(),
    })
}

/// Writes the handle of the pseudorandom key `salt` extracts from the `len`
/// bytes at `secret` to `out`, refusing an empty salt.
///
/// # Safety
/// `salt` must be live, `secret` valid for `len` reads, and `out` for a
/// write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hkdf_extract(
    salt: *const Salt,
    secret: *const u8,
    len: usize,
    out: *mut *mut hkdf::Prk,
) -> Status {
    // SAFETY: the caller's contract.
    let (salt, secret) = unsafe { (&*salt, bytes(secret, len)) };
    if salt.empty {
        return status(Err(Error::WrongLength));
    }
    scrubbed(Depth::Small, || {
        status(salt.salt.extract(secret).map(|prk| {
            // SAFETY: the caller's contract.
            unsafe { put(out, handle(prk)) }
        }))
    })
}

/// `prk.expand`, refusing an empty `info`.
pub(crate) fn expand<'a, L: hkdf::KeyType>(
    prk: &'a hkdf::Prk,
    info: &'a [&'a [u8]],
    len: L,
) -> Result<hkdf::Okm<'a, L>, Error> {
    if info.iter().all(|part| part.is_empty()) {
        return Err(Error::WrongLength);
    }
    prk.expand(info, len)
}

/// Fills the `len` bytes at `out` with what `prk` expands to for the
/// concatenation of the `info_len` strings at `info`, refusing an empty
/// one.
///
/// # Safety
/// `prk` must be live, `info` valid as `abi::byte_list` requires, and `out`
/// valid for `len` writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hkdf_fill(
    prk: *const hkdf::Prk,
    info: *const Bytes,
    info_len: usize,
    out: *mut u8,
    len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (prk, info, out) = unsafe { (&*prk, byte_list(info, info_len), bytes_mut(out, len)) };
    scrubbed(Depth::Small, || {
        status(expand(prk, &info, out.len()).and_then(|okm| okm.fill(out)))
    })
}

/// The HMAC key for the hash `id` names that `prk` expands to for `info`,
/// as [`rind_fips_hkdf_fill`] takes it, or null for an unknown `id` or an
/// empty `info`.
///
/// # Safety
/// As for [`rind_fips_hkdf_fill`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hkdf_expand_hmac(
    prk: *const hkdf::Prk,
    info: *const Bytes,
    info_len: usize,
    id: u32,
) -> *mut hmac::Key {
    let Some(algorithm) = hmac_algorithm(id) else {
        return core::ptr::null_mut();
    };
    // SAFETY: the caller's contract.
    let (prk, info) = unsafe { (&*prk, byte_list(info, info_len)) };
    let Ok(okm) = expand(prk, &info, algorithm) else {
        return core::ptr::null_mut();
    };
    new_handle(|| hmac::Key::from(okm))
}

/// The pseudorandom key for the hash `id` names that `prk` expands to for
/// `info`, as [`rind_fips_hkdf_fill`] takes it, or null for an unknown `id`
/// or an empty `info`.
///
/// # Safety
/// As for [`rind_fips_hkdf_fill`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hkdf_expand_prk(
    prk: *const hkdf::Prk,
    info: *const Bytes,
    info_len: usize,
    id: u32,
) -> *mut hkdf::Prk {
    let Some(algorithm) = hkdf_algorithm(id) else {
        return core::ptr::null_mut();
    };
    // SAFETY: the caller's contract.
    let (prk, info) = unsafe { (&*prk, byte_list(info, info_len)) };
    let Ok(okm) = expand(prk, &info, algorithm) else {
        return core::ptr::null_mut();
    };
    new_handle(|| hkdf::Prk::from(okm))
}

free!(rind_fips_hkdf_salt_free, Salt);
free!(rind_fips_hkdf_prk_free, hkdf::Prk);

/// A PBKDF2 secret, and whether it is long enough to derive with.
pub(crate) struct Secret {
    secret: pbkdf2::Secret,
    approved: bool,
}

/// aws-lc's floor: SP 800-132 asks for strong passwords without a length.
const MIN_PASSWORD_LEN: usize = 14;
/// SP 800-132 section 5.1's 128 bits.
const MIN_SALT_LEN: usize = 16;
/// SP 800-132 section 5.2's minimum.
const MIN_ITERATIONS: u32 = 1000;
/// SP 800-132 section 5.3's 112 bits.
const MIN_OUTPUT_LEN: usize = 14;

impl Secret {
    /// Checks the floors on everything but the output's length, returning
    /// the iteration count.
    fn check(&self, iterations: u32, salt: &[u8]) -> Result<NonZeroU32, Error> {
        if !self.approved || salt.len() < MIN_SALT_LEN || iterations < MIN_ITERATIONS {
            return Err(Error::WrongLength);
        }
        NonZeroU32::new(iterations).ok_or(Error::WrongLength)
    }
}

/// A PBKDF2 secret for the hash `id` names, from the `len` bytes at
/// `secret`, or null for an unknown `id`.
///
/// # Safety
/// `secret` must be valid for `len` reads.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_pbkdf2_secret_new(
    id: u32,
    secret: *const u8,
    len: usize,
) -> *mut Secret {
    let Some(algorithm) = pbkdf2_algorithm(id) else {
        return core::ptr::null_mut();
    };
    // SAFETY: the caller's contract.
    let secret = unsafe { bytes(secret, len) };
    new_handle(|| Secret {
        secret: pbkdf2::Secret::new(algorithm, secret),
        approved: secret.len() >= MIN_PASSWORD_LEN,
    })
}

/// Fills the `len` bytes at `out` with the key `secret` derives from the
/// `salt_len` bytes at `salt` over `iterations` rounds.
///
/// # Safety
/// `secret` must be live, `salt` valid for `salt_len` reads, and `out` for
/// `len` writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_pbkdf2_derive(
    secret: *const Secret,
    iterations: u32,
    salt: *const u8,
    salt_len: usize,
    out: *mut u8,
    len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (secret, salt, out) = unsafe { (&*secret, bytes(salt, salt_len), bytes_mut(out, len)) };
    scrubbed(Depth::Small, || {
        status(secret.check(iterations, salt).and_then(|iterations| {
            if out.len() < MIN_OUTPUT_LEN {
                return Err(Error::WrongLength);
            }
            secret.secret.derive(iterations, salt, out)
        }))
    })
}

/// Checks that the `len` bytes at `derived` are what `secret` derives from
/// the `salt_len` bytes at `salt` over `iterations` rounds.
///
/// # Safety
/// `secret` must be live, and `salt` and `derived` valid for their lengths'
/// reads.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_pbkdf2_verify(
    secret: *const Secret,
    iterations: u32,
    salt: *const u8,
    salt_len: usize,
    derived: *const u8,
    len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (secret, salt, derived) = unsafe { (&*secret, bytes(salt, salt_len), bytes(derived, len)) };
    // rind refuses a stored key shorter than the hash, longer than the
    // output floor.
    scrubbed(Depth::Small, || {
        status(
            secret
                .check(iterations, salt)
                .and_then(|iterations| secret.secret.verify(iterations, salt, derived)),
        )
    })
}

free!(rind_fips_pbkdf2_secret_free, Secret);
