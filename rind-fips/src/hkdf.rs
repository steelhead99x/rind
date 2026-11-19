// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::ffi::{self, Bytes, Handle, opaque};
use crate::{Error, hmac};

opaque! {
    HkdfSalt => rind_fips_hkdf_salt_free,
    HkdfPrk => rind_fips_hkdf_prk_free,
}

unsafe extern "C" {
    fn rind_fips_hkdf_salt_new(id: u32, value: *const u8, len: usize) -> *mut HkdfSalt;
    fn rind_fips_hkdf_extract(
        salt: *const HkdfSalt,
        secret: *const u8,
        len: usize,
        out: *mut *mut HkdfPrk,
    ) -> ffi::Status;
    fn rind_fips_hkdf_prk_new(id: u32, value: *const u8, len: usize) -> *mut HkdfPrk;
    fn rind_fips_hkdf_prk_clone(prk: *const HkdfPrk) -> *mut HkdfPrk;
    fn rind_fips_hkdf_fill(
        prk: *const HkdfPrk,
        info: *const Bytes,
        info_len: usize,
        out: *mut u8,
        len: usize,
    ) -> ffi::Status;
    fn rind_fips_hkdf_expand_hmac(
        prk: *const HkdfPrk,
        info: *const Bytes,
        info_len: usize,
        id: u32,
    ) -> *mut hmac::HmacKey;
    fn rind_fips_hkdf_expand_prk(
        prk: *const HkdfPrk,
        info: *const Bytes,
        info_len: usize,
        id: u32,
    ) -> *mut HkdfPrk;
}

/// An HKDF algorithm, chosen by one of this module's constants.
pub struct Algorithm(&'static hmac::Algorithm);

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Algorithm").field(self.0).finish()
    }
}

/// HKDF-SHA256.
pub static HKDF_SHA256: Algorithm = Algorithm(&hmac::HMAC_SHA256);

/// HKDF-SHA384.
pub static HKDF_SHA384: Algorithm = Algorithm(&hmac::HMAC_SHA384);

/// HKDF-SHA512.
pub static HKDF_SHA512: Algorithm = Algorithm(&hmac::HMAC_SHA512);

/// HKDF algorithms only legacy protocols should use.
pub mod legacy {
    use super::{Algorithm, hmac};

    /// HKDF-SHA1, for legacy protocols only.
    ///
    /// Like HMAC, HKDF does not rely on SHA-1's broken collision resistance, but
    /// new protocols should pick a SHA-2 hash.
    pub static HKDF_SHA1: Algorithm = Algorithm(&hmac::legacy::HMAC_SHA1);
}

/// A salt, keyed once and reused for every secret it extracts from.
pub struct Salt {
    algorithm: &'static Algorithm,
    handle: Handle<HkdfSalt>,
}

impl Salt {
    /// Keys `algorithm` with `value`; an empty `value` is RFC 5869's absent salt.
    pub fn new(algorithm: &'static Algorithm, value: &[u8]) -> Self {
        // SAFETY: `value` is readable.
        let handle =
            unsafe { rind_fips_hkdf_salt_new(algorithm.0.id, value.as_ptr(), value.len()) };
        Self {
            algorithm,
            handle: Handle::new(handle),
        }
    }

    /// Extracts a pseudorandom key from `secret` (HKDF-Extract).
    ///
    /// Fails with [`Error::WrongLength`] for an empty salt, which FIPS 140-3
    /// does not approve.
    pub fn extract(&self, secret: &[u8]) -> Result<Prk, Error> {
        let mut out = core::ptr::null_mut();
        // SAFETY: the handle is live, `secret` readable, and `out` writable.
        let status = unsafe {
            rind_fips_hkdf_extract(self.handle.ptr(), secret.as_ptr(), secret.len(), &mut out)
        };
        Ok(Prk {
            algorithm: self.algorithm,
            handle: Handle::from_status(status, out)?,
        })
    }
}

impl fmt::Debug for Salt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Salt")
            .field("algorithm", &format_args!("{}", self.algorithm.0.name))
            .finish_non_exhaustive()
    }
}

/// A pseudorandom key, from which [`Prk::expand`] and [`Prk::fill`] derive
/// any number of keys; held in the module, which wipes it on drop.
pub struct Prk {
    algorithm: &'static Algorithm,
    pub(crate) handle: Handle<HkdfPrk>,
}

impl Prk {
    /// Takes `bytes` as a pseudorandom key for `algorithm`, skipping
    /// HKDF-Extract, as when a protocol's key schedule hands one over.
    pub fn new(algorithm: &'static Algorithm, bytes: &[u8]) -> Self {
        // SAFETY: `bytes` is readable.
        let handle = unsafe { rind_fips_hkdf_prk_new(algorithm.0.id, bytes.as_ptr(), bytes.len()) };
        Self {
            algorithm,
            handle: Handle::new(handle),
        }
    }

    /// Derives the key `len` names for the concatenation of `info` (HKDF-Expand).
    ///
    /// Fails with [`Error::WrongLength`] for an empty `info`, which FIPS
    /// 140-3 does not approve.
    pub fn expand<'a, L: KeyType>(
        &'a self,
        info: &'a [&'a [u8]],
        len: L,
    ) -> Result<Okm<'a, L>, Error> {
        if info.iter().all(|part| part.is_empty()) {
            return Err(Error::WrongLength);
        }
        Ok(Okm {
            prk: self,
            info,
            len,
        })
    }

    /// Fills `out` with HKDF-Expand's output for the concatenation of `info`.
    ///
    /// Fails with [`Error::WrongLength`], leaving `out` unchanged, for an
    /// empty `info`, which FIPS 140-3 does not approve, or if `out` is more
    /// than 255 hash outputs.
    pub fn fill(&self, info: &[&[u8]], out: &mut [u8]) -> Result<(), Error> {
        let info = Bytes::list(info);
        // SAFETY: the handle is live, `info` lists readable strings, and
        // `out` is writable.
        ffi::check(unsafe {
            rind_fips_hkdf_fill(
                self.handle.ptr(),
                info.as_ptr(),
                info.len(),
                out.as_mut_ptr(),
                out.len(),
            )
        })
    }
}

impl Clone for Prk {
    fn clone(&self) -> Self {
        Self {
            algorithm: self.algorithm,
            // SAFETY: the handle is live.
            handle: Handle::new(unsafe { rind_fips_hkdf_prk_clone(self.handle.ptr()) }),
        }
    }
}

impl fmt::Debug for Prk {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Prk")
            .field("algorithm", &format_args!("{}", self.algorithm.0.name))
            .finish_non_exhaustive()
    }
}

pub(crate) mod sealed {
    pub trait Sealed {}
}

/// The algorithm of the key an [`Okm`] becomes, which sets its length.
pub trait KeyType: sealed::Sealed {}

/// A key of the algorithm's [`hmac::Algorithm::tag_len`].
impl sealed::Sealed for &'static hmac::Algorithm {}
impl KeyType for &'static hmac::Algorithm {}

/// The pseudorandom key of a further [`Prk::expand`], the hash's output length.
impl sealed::Sealed for &'static Algorithm {}
impl KeyType for &'static Algorithm {}

/// Key material from [`Prk::expand`], which converts into the key its algorithm `L` names.
#[must_use]
pub struct Okm<'a, L: KeyType> {
    pub(crate) prk: &'a Prk,
    info: &'a [&'a [u8]],
    pub(crate) len: L,
}

impl<L: KeyType> Okm<'_, L> {
    /// `info` as the module takes it.
    pub(crate) fn info(&self) -> Vec<Bytes> {
        Bytes::list(self.info)
    }
}

impl<L: KeyType> fmt::Debug for Okm<'_, L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Okm")
            .field("algorithm", &format_args!("{}", self.prk.algorithm.0.name))
            .finish_non_exhaustive()
    }
}

impl From<Okm<'_, &'static hmac::Algorithm>> for hmac::Key {
    fn from(okm: Okm<'_, &'static hmac::Algorithm>) -> Self {
        let info = okm.info();
        // SAFETY: the handle is live, and `info` lists readable strings.
        let handle = unsafe {
            rind_fips_hkdf_expand_hmac(okm.prk.handle.ptr(), info.as_ptr(), info.len(), okm.len.id)
        };
        Self::from_handle(okm.len, handle)
    }
}

impl From<Okm<'_, &'static Algorithm>> for Prk {
    fn from(okm: Okm<'_, &'static Algorithm>) -> Self {
        let info = okm.info();
        // SAFETY: the handle is live, and `info` lists readable strings.
        let handle = unsafe {
            rind_fips_hkdf_expand_prk(
                okm.prk.handle.ptr(),
                info.as_ptr(),
                info.len(),
                okm.len.0.id,
            )
        };
        Self {
            algorithm: okm.len,
            handle: Handle::new(handle),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // `Prk::expand` refuses an empty info before reaching the module, which
    // must refuse one too, as the boundary.
    #[test]
    fn module_refuses_empty_info() {
        let prk = Salt::new(&HKDF_SHA256, b"salt").extract(b"secret").unwrap();
        let info = Bytes::list(&[b""]);
        let mut out = [0u8; 16];
        // SAFETY: the handle is live, `info` lists readable strings, and
        // `out` is writable.
        let status = unsafe {
            rind_fips_hkdf_fill(
                prk.handle.ptr(),
                info.as_ptr(),
                info.len(),
                out.as_mut_ptr(),
                out.len(),
            )
        };
        assert_eq!(ffi::check(status), Err(Error::WrongLength));
        // SAFETY: as above.
        let key = unsafe {
            rind_fips_hkdf_expand_hmac(
                prk.handle.ptr(),
                info.as_ptr(),
                info.len(),
                hmac::HMAC_SHA256.id,
            )
        };
        assert!(key.is_null());
        // SAFETY: as above.
        let next = unsafe {
            rind_fips_hkdf_expand_prk(
                prk.handle.ptr(),
                info.as_ptr(),
                info.len(),
                HKDF_SHA256.0.id,
            )
        };
        assert!(next.is_null());
    }
}
