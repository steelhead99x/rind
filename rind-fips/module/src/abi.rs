// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The C ABI's conventions, and the services that belong to no algorithm.
//!
//! - A fallible service returns a status: 0 for success, otherwise the
//!   error's code (`rind::fips::error_code`).
//! - A byte string is a pointer and a length; a null pointer is allowed
//!   only with length 0.
//! - Keys and contexts are opaque handles, boxed on the module's heap, which
//!   the caller frees with the handle type's `_free`. Keys never leave the
//!   module, nor move once boxed.
//! - Output of variable length goes to the caller's buffer, with its
//!   capacity, and the service writes the length used.
//!
//! The caller is `rind-fips`, which upholds every safety contract here: each
//! pointer is valid for its length, and each handle is live and of its type.

use rind::Error;

use crate::scrub::{Depth, scrubbed};
use crate::selftest;

pub(crate) type Status = u32;

/// The status of `result`: 0, or the error's kind (`ids::error`) in the low
/// byte and rind's code for it above.
pub(crate) fn status(result: Result<(), Error>) -> Status {
    use crate::ids::error::*;
    let Err(error) = result else {
        return 0;
    };
    let kind = match error {
        Error::WrongLength => WRONG_LENGTH,
        Error::KeyRejected(_) => KEY_REJECTED,
        Error::BadSignature => BAD_SIGNATURE,
        Error::DecryptFailed => DECRYPT_FAILED,
        Error::RngFailed => RNG_FAILED,
        Error::NotEqual => NOT_EQUAL,
        Error::Unsupported => UNSUPPORTED,
        // HPKE's message limit, which no service here reaches.
        _ => FAULT,
    };
    kind | rind::fips::error_code(error) << 8
}

/// The `len` bytes at `ptr`.
///
/// # Safety
/// `ptr` must be valid for `len` reads, or null if `len` is 0.
pub(crate) unsafe fn bytes<'a>(ptr: *const u8, len: usize) -> &'a [u8] {
    if len == 0 {
        return &[];
    }
    // SAFETY: the caller's contract.
    unsafe { core::slice::from_raw_parts(ptr, len) }
}

/// The `len` writable bytes at `ptr`.
///
/// # Safety
/// `ptr` must be valid for `len` writes, or null if `len` is 0.
pub(crate) unsafe fn bytes_mut<'a>(ptr: *mut u8, len: usize) -> &'a mut [u8] {
    if len == 0 {
        return &mut [];
    }
    // SAFETY: the caller's contract.
    unsafe { core::slice::from_raw_parts_mut(ptr, len) }
}

/// A byte string within a list, as `info` for HKDF.
#[repr(C)]
pub(crate) struct Bytes {
    ptr: *const u8,
    len: usize,
}

/// The byte strings of the `len` [`Bytes`] at `ptr`.
///
/// # Safety
/// `ptr` must be valid for `len` reads, or null if `len` is 0, and each
/// [`Bytes`] valid as [`bytes`] requires.
pub(crate) unsafe fn byte_list<'a>(ptr: *const Bytes, len: usize) -> Vec<&'a [u8]> {
    if len == 0 {
        return Vec::new();
    }
    // SAFETY: the caller's contract.
    let list = unsafe { core::slice::from_raw_parts(ptr, len) };
    // SAFETY: the caller's contract.
    list.iter()
        .map(|b| unsafe { bytes(b.ptr, b.len) })
        .collect()
}

/// Boxes `value` as a handle.
pub(crate) fn handle<T>(value: T) -> *mut T {
    Box::into_raw(Box::new(value))
}

/// Writes `value` to `out`.
///
/// # Safety
/// `out` must be valid for a write of `T`.
pub(crate) unsafe fn put<T>(out: *mut T, value: T) {
    // SAFETY: the caller's contract.
    unsafe { out.write(value) }
}

/// Copies `value` to the `cap` bytes at `out`, writing its length to `len`,
/// or fails with [`Error::WrongLength`] if it does not fit.
///
/// # Safety
/// `out` must be valid for `cap` writes, and `len` for a write.
pub(crate) unsafe fn copy_out(
    value: &[u8],
    out: *mut u8,
    cap: usize,
    len: *mut usize,
) -> Result<(), Error> {
    if value.len() > cap {
        return Err(Error::WrongLength);
    }
    // SAFETY: the caller's contract, and `value` fits.
    unsafe {
        bytes_mut(out, value.len()).copy_from_slice(value);
        put(len, value.len());
    }
    Ok(())
}

/// Defines `$name`, which frees a `$ty` handle; null is allowed.
macro_rules! free {
    ($name:ident, $ty:ty) => {
        /// Frees a handle; its value wipes itself, and the allocator zeroes
        /// its block.
        ///
        /// # Safety
        /// `handle` must be null or a live handle of this type, not used
        /// again.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name(handle: *mut $ty) {
            if !handle.is_null() {
                // SAFETY: the caller's contract.
                drop(unsafe { Box::from_raw(handle) });
            }
        }
    };
}
pub(crate) use free;

/// An encoding a service made, such as a key's PKCS#8 or a ciphertext:
/// rind's own type, so a private one wipes itself when freed, behind a
/// handle the caller reads it through.
pub(crate) struct Encoded(Box<dyn AsRef<[u8]> + Send + Sync>);

/// Boxes `value` as an [`Encoded`] handle.
pub(crate) fn encoded(value: impl AsRef<[u8]> + Send + Sync + 'static) -> *mut Encoded {
    handle(Encoded(Box::new(value)))
}

/// The bytes of `encoded`, writing their length to `len`; they live as
/// long as the handle.
///
/// # Safety
/// `encoded` must be live, and `len` valid for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_encoded_bytes(
    encoded: *const Encoded,
    len: *mut usize,
) -> *const u8 {
    // SAFETY: the caller's contract.
    let bytes = unsafe { (*(*encoded).0).as_ref() };
    // SAFETY: the caller's contract.
    unsafe { put(len, bytes.len()) };
    bytes.as_ptr()
}

free!(rind_fips_encoded_free, Encoded);

/// The module's name and version, writing its length to `len`. The string
/// lives as long as the module.
///
/// # Safety
/// `len` must be valid for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_version(len: *mut usize) -> *const u8 {
    // SAFETY: the caller's contract.
    unsafe { put(len, crate::VERSION.len()) };
    crate::VERSION.as_ptr()
}

/// The on-demand self-tests: the integrity test, then every CAST, whether
/// it has run or not. A failure enters the error state.
#[unsafe(no_mangle)]
pub extern "C" fn rind_fips_self_test() {
    scrubbed(Depth::Large, || {
        if !crate::integrity::check() {
            rind::fips::fail("integrity");
        }
        selftest::run_all();
    })
}

/// Writes the message of the error with status `status` to the `cap` bytes
/// at `out`, truncated to fit, and returns its full length: a refused key's
/// reason, or any other error's description.
///
/// # Safety
/// `out` must be valid for `cap` writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_error_message(
    status: Status,
    out: *mut u8,
    cap: usize,
) -> usize {
    let message = match rind::fips::error_from_code(status >> 8) {
        Some(Error::KeyRejected(reason)) => reason.to_string(),
        Some(error) => error.to_string(),
        None => String::new(),
    };
    let n = message.len().min(cap);
    // SAFETY: the caller's contract, and `n` fits.
    unsafe { bytes_mut(out, n).copy_from_slice(&message.as_bytes()[..n]) };
    message.len()
}

/// Fills the `len` bytes at `out` from the module's DRBG.
///
/// # Safety
/// `out` must be valid for `len` writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_rand_fill(out: *mut u8, len: usize) -> Status {
    // The DRBG runs its own self-test before its first instantiation.
    // SAFETY: the caller's contract.
    scrubbed(Depth::Medium, || {
        status(rind::rand::fill(unsafe { bytes_mut(out, len) }))
    })
}

/// The first CPU feature the module requires that this CPU lacks, writing
/// its name's length to `len`, or null if it lacks none. The name lives as
/// long as the module.
///
/// # Safety
/// `len` must be valid for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_cpu_check(len: *mut usize) -> *const u8 {
    match rind::fips::missing_cpu_feature() {
        None => core::ptr::null(),
        Some(name) => {
            // SAFETY: the caller's contract.
            unsafe { put(len, name.len()) };
            name.as_ptr()
        }
    }
}

/// Whether the module runs AES on CPU instructions.
#[unsafe(no_mangle)]
pub extern "C" fn rind_fips_has_aes_hardware() -> bool {
    rind::cpu::has_aes_hardware()
}

/// Compares the `a_len` bytes at `a` with the `b_len` at `b` in constant
/// time.
///
/// # Safety
/// `a` and `b` must be valid for their lengths' reads.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_constant_time_verify(
    a: *const u8,
    a_len: usize,
    b: *const u8,
    b_len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (a, b) = unsafe { (bytes(a, a_len), bytes(b, b_len)) };
    scrubbed(Depth::Small, || status(rind::constant_time::verify(a, b)))
}
