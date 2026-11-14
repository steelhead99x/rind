// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::Error;
use crate::cipher::{Algorithm, new_handle};
use crate::ffi::{self, Handle, Status, opaque};

opaque! {
    Kek => rind_fips_aes_kek_free,
}

unsafe extern "C" {
    fn rind_fips_aes_kek_new(id: u32, key: *const u8, len: usize, out: *mut *mut Kek) -> Status;
    fn rind_fips_aes_kek_wrap(
        kek: *const Kek,
        key: *const u8,
        key_len: usize,
        wrapped: *mut u8,
        wrapped_len: usize,
    ) -> Status;
    fn rind_fips_aes_kek_unwrap(
        kek: *const Kek,
        wrapped: *const u8,
        wrapped_len: usize,
        key: *mut u8,
        key_len: usize,
    ) -> Status;
    fn rind_fips_aes_kek_wrap_padded(
        kek: *const Kek,
        key: *const u8,
        key_len: usize,
        wrapped: *mut u8,
        wrapped_len: usize,
    ) -> Status;
    fn rind_fips_aes_kek_unwrap_padded(
        kek: *const Kek,
        wrapped: *const u8,
        wrapped_len: usize,
        key: *mut u8,
        key_len: usize,
        unwrapped_len: *mut usize,
    ) -> Status;
}

/// An AES key-encryption key, which wraps and unwraps other keys with RFC
/// 3394 AES-KW, or with RFC 5649 AES-KWP for keys of any length; held in
/// the module, which wipes it on drop.
///
/// Wrapping is deterministic and authenticated: a wrapped key that was
/// altered fails to unwrap.
pub struct AesKek {
    algorithm: &'static Algorithm,
    handle: Handle<Kek>,
}

impl AesKek {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not that algorithm's key length.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        let handle = new_handle(|out| {
            // SAFETY: `key` is readable, and `out` writable.
            unsafe { rind_fips_aes_kek_new(algorithm.id(), key.as_ptr(), key.len(), out) }
        })?;
        Ok(Self { algorithm, handle })
    }

    /// Wraps `key` into `wrapped`, which must be 8 bytes longer.
    ///
    /// Fails with [`Error::WrongLength`], leaving `wrapped` unchanged, if
    /// `key` is shorter than 16 bytes or not a multiple of 8, or `wrapped` is
    /// not 8 bytes longer.
    pub fn wrap(&self, key: &[u8], wrapped: &mut [u8]) -> Result<(), Error> {
        // SAFETY: the handle is live, `key` readable, and `wrapped` writable.
        ffi::check(unsafe {
            rind_fips_aes_kek_wrap(
                self.handle.ptr(),
                key.as_ptr(),
                key.len(),
                wrapped.as_mut_ptr(),
                wrapped.len(),
            )
        })
    }

    /// Unwraps `wrapped` into `key`, which must be 8 bytes shorter.
    ///
    /// Fails with [`Error::DecryptFailed`] if `wrapped` was not wrapped by
    /// this key, clearing `key`, or is shorter than 24 bytes or not a
    /// multiple of 8, and with [`Error::WrongLength`] if `key` is not 8 bytes
    /// shorter; a length failure leaves `key` unchanged.
    pub fn unwrap(&self, wrapped: &[u8], key: &mut [u8]) -> Result<(), Error> {
        // SAFETY: the handle is live, `wrapped` readable, and `key` writable.
        ffi::check(unsafe {
            rind_fips_aes_kek_unwrap(
                self.handle.ptr(),
                wrapped.as_ptr(),
                wrapped.len(),
                key.as_mut_ptr(),
                key.len(),
            )
        })
    }

    /// Wraps `key`, of any length from 1 byte, into `wrapped`, which must be
    /// `key.len().next_multiple_of(8) + 8` bytes long, with RFC 5649's
    /// padding.
    ///
    /// Fails with [`Error::WrongLength`], leaving `wrapped` unchanged, if
    /// `key` is empty or longer than `u32::MAX` bytes, or `wrapped` is not
    /// that length.
    pub fn wrap_padded(&self, key: &[u8], wrapped: &mut [u8]) -> Result<(), Error> {
        // SAFETY: the handle is live, `key` readable, and `wrapped` writable.
        ffi::check(unsafe {
            rind_fips_aes_kek_wrap_padded(
                self.handle.ptr(),
                key.as_ptr(),
                key.len(),
                wrapped.as_mut_ptr(),
                wrapped.len(),
            )
        })
    }

    /// Unwraps `wrapped`, wrapped with RFC 5649's padding, into `key`, which
    /// must be 8 bytes shorter, returning the unwrapped key at its start.
    ///
    /// Fails with [`Error::DecryptFailed`] if `wrapped` was not wrapped by
    /// this key, clearing `key`, or is shorter than 16 bytes or not a
    /// multiple of 8, and with [`Error::WrongLength`] if `key` is not 8 bytes
    /// shorter; a length failure leaves `key` unchanged.
    pub fn unwrap_padded<'a>(
        &self,
        wrapped: &[u8],
        key: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        let mut len = 0;
        // SAFETY: the handle is live, `wrapped` readable, and `key` and
        // `len` writable.
        ffi::check(unsafe {
            rind_fips_aes_kek_unwrap_padded(
                self.handle.ptr(),
                wrapped.as_ptr(),
                wrapped.len(),
                key.as_mut_ptr(),
                key.len(),
                &mut len,
            )
        })?;
        Ok(&mut key[..len])
    }
}

impl fmt::Debug for AesKek {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AesKek")
            .field("algorithm", self.algorithm)
            .finish_non_exhaustive()
    }
}
