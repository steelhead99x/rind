// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::num::NonZeroU32;

use crate::ffi::{self, Handle, opaque};
use crate::{Error, hmac};

opaque! {
    Pbkdf2Secret => rind_fips_pbkdf2_secret_free,
}

unsafe extern "C" {
    fn rind_fips_pbkdf2_secret_new(id: u32, secret: *const u8, len: usize) -> *mut Pbkdf2Secret;
    fn rind_fips_pbkdf2_derive(
        secret: *const Pbkdf2Secret,
        iterations: u32,
        salt: *const u8,
        salt_len: usize,
        out: *mut u8,
        len: usize,
    ) -> ffi::Status;
    fn rind_fips_pbkdf2_verify(
        secret: *const Pbkdf2Secret,
        iterations: u32,
        salt: *const u8,
        salt_len: usize,
        derived: *const u8,
        len: usize,
    ) -> ffi::Status;
}

/// A PBKDF2 algorithm, chosen by one of this module's constants.
pub struct Algorithm(&'static hmac::Algorithm);

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Algorithm").field(self.0).finish()
    }
}

/// PBKDF2-HMAC-SHA256.
pub static PBKDF2_HMAC_SHA256: Algorithm = Algorithm(&hmac::HMAC_SHA256);

/// PBKDF2-HMAC-SHA384.
pub static PBKDF2_HMAC_SHA384: Algorithm = Algorithm(&hmac::HMAC_SHA384);

/// PBKDF2-HMAC-SHA512.
pub static PBKDF2_HMAC_SHA512: Algorithm = Algorithm(&hmac::HMAC_SHA512);

/// PBKDF2 algorithms only legacy formats should use.
pub mod legacy {
    use super::{Algorithm, hmac};

    /// PBKDF2-HMAC-SHA1, for legacy formats only.
    ///
    /// PBKDF2 does not rely on SHA-1's broken collision resistance, and formats
    /// such as WPA2 and older PKCS#12 files still require it.
    pub static PBKDF2_HMAC_SHA1: Algorithm = Algorithm(&hmac::legacy::HMAC_SHA1);
}

/// A secret, such as a password, keyed once for every salt it derives with;
/// held in the module, which wipes it on drop.
pub struct Secret {
    algorithm: &'static Algorithm,
    handle: Handle<Pbkdf2Secret>,
}

impl fmt::Debug for Secret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Secret")
            .field("algorithm", &format_args!("{}", self.algorithm.0.name))
            .finish_non_exhaustive()
    }
}

impl Secret {
    /// Keys `algorithm` with `secret`, which may be any length, though only
    /// one of at least 14 bytes derives.
    pub fn new(algorithm: &'static Algorithm, secret: &[u8]) -> Self {
        // SAFETY: `secret` is readable.
        let handle =
            unsafe { rind_fips_pbkdf2_secret_new(algorithm.0.id, secret.as_ptr(), secret.len()) };
        Self {
            algorithm,
            handle: Handle::new(handle),
        }
    }

    /// Fills `out` with the key derived from `salt` over `iterations` rounds.
    ///
    /// Each hash length of `out` costs another `iterations` rounds, which
    /// slows the defender but not an attacker, who needs only the first, so
    /// expand one hash's length with HKDF for more. The cost is linear in
    /// `iterations`, so cap any taken from untrusted input, such as PBES2 or
    /// PKCS#12 parameters.
    ///
    /// Fails with [`Error::WrongLength`], leaving `out` unchanged, outside
    /// what SP 800-132 approves: a secret under 14 bytes, a salt under 16,
    /// fewer than 1000 iterations, or `out` under 14 bytes. It fails so too
    /// if `out` is longer than PBKDF2 allows.
    pub fn derive(&self, iterations: NonZeroU32, salt: &[u8], out: &mut [u8]) -> Result<(), Error> {
        // SAFETY: the handle is live, `salt` readable, and `out` writable.
        ffi::check(unsafe {
            rind_fips_pbkdf2_derive(
                self.handle.ptr(),
                iterations.get(),
                salt.as_ptr(),
                salt.len(),
                out.as_mut_ptr(),
                out.len(),
            )
        })
    }

    /// Checks in constant time that `previously_derived` is what [`Secret::derive`] makes for `salt` and `iterations`.
    ///
    /// The key derived is as long as `previously_derived`. Fails with
    /// [`Error::WrongLength`] if that is shorter than the HMAC output or
    /// longer than PBKDF2 allows, or for what [`Secret::derive`] refuses,
    /// and with [`Error::BadSignature`] if the keys differ. A truncated
    /// stored value is refused because it is easier to match.
    pub fn verify(
        &self,
        iterations: NonZeroU32,
        salt: &[u8],
        previously_derived: &[u8],
    ) -> Result<(), Error> {
        // SAFETY: the handle is live, and `salt` and `previously_derived`
        // readable.
        ffi::check(unsafe {
            rind_fips_pbkdf2_verify(
                self.handle.ptr(),
                iterations.get(),
                salt.as_ptr(),
                salt.len(),
                previously_derived.as_ptr(),
                previously_derived.len(),
            )
        })
    }
}
