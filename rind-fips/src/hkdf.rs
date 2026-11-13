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
    fn rind_fips_hkdf_extract(salt: *const HkdfSalt, secret: *const u8, len: usize)
    -> *mut HkdfPrk;
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
    #[must_use]
    pub fn extract(&self, secret: &[u8]) -> Prk {
        // SAFETY: the handle is live, and `secret` readable.
        let handle =
            unsafe { rind_fips_hkdf_extract(self.handle.ptr(), secret.as_ptr(), secret.len()) };
        Prk {
            algorithm: self.algorithm,
            handle: Handle::new(handle),
        }
    }
}

impl fmt::Debug for Salt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Salt")
            .field("algorithm", &format_args!("{}", self.algorithm.0.name))
            .finish_non_exhaustive()
    }
}

/// A pseudorandom key, from which [`Prk::expand`] derives any number of
/// keys; held in the module, which wipes it on drop.
pub struct Prk {
    algorithm: &'static Algorithm,
    pub(crate) handle: Handle<HkdfPrk>,
}

impl Prk {
    /// Derives key material for the concatenation of `info` (HKDF-Expand), as long as `len` says.
    pub fn expand<'a, L: KeyType>(&'a self, info: &'a [&'a [u8]], len: L) -> Okm<'a, L> {
        Okm {
            prk: self,
            info,
            len,
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

/// A length of HKDF output: a plain `usize`, or the algorithm of the key it becomes.
pub trait KeyType: sealed::Sealed {}

/// Raw key material of this many bytes, for [`Okm::fill`].
impl sealed::Sealed for usize {}
impl KeyType for usize {}

/// A key of the algorithm's [`hmac::Algorithm::tag_len`].
impl sealed::Sealed for &'static hmac::Algorithm {}
impl KeyType for &'static hmac::Algorithm {}

/// The pseudorandom key of a further [`Prk::expand`], the hash's output length.
impl sealed::Sealed for &'static Algorithm {}
impl KeyType for &'static Algorithm {}

/// Key material from [`Prk::expand`], sized by `L`: fill a buffer for a `usize` length, or convert it into the key an algorithm names.
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

impl Okm<'_, usize> {
    /// Writes the key material into `out`.
    ///
    /// Fails with [`Error::WrongLength`], leaving `out` unchanged, unless
    /// `out` is the length [`Prk::expand`] was given and at most 255 hash
    /// outputs.
    pub fn fill(self, out: &mut [u8]) -> Result<(), Error> {
        if out.len() != self.len {
            return Err(Error::WrongLength);
        }
        let info = self.info();
        // SAFETY: the handle is live, `info` lists readable strings, and
        // `out` is writable.
        ffi::check(unsafe {
            rind_fips_hkdf_fill(
                self.prk.handle.ptr(),
                info.as_ptr(),
                info.len(),
                out.as_mut_ptr(),
                out.len(),
            )
        })
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
