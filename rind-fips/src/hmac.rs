// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::Error;
use crate::ffi::{self, Handle, ids, opaque};

opaque! {
    HmacKey => rind_fips_hmac_key_free,
    HmacContext => rind_fips_hmac_context_free,
}

unsafe extern "C" {
    fn rind_fips_hmac_key_new(id: u32, key: *const u8, len: usize) -> *mut HmacKey;
    fn rind_fips_hmac_key_clone(key: *const HmacKey) -> *mut HmacKey;
    fn rind_fips_hmac_sign(key: *const HmacKey, data: *const u8, len: usize, out: *mut u8)
    -> usize;
    fn rind_fips_hmac_verify(
        key: *const HmacKey,
        data: *const u8,
        len: usize,
        tag: *const u8,
        tag_len: usize,
    ) -> ffi::Status;
    fn rind_fips_hmac_context_new(key: *const HmacKey) -> *mut HmacContext;
    fn rind_fips_hmac_context_update(context: *mut HmacContext, data: *const u8, len: usize);
    fn rind_fips_hmac_context_clone(context: *const HmacContext) -> *mut HmacContext;
    fn rind_fips_hmac_context_sign(context: *mut HmacContext, out: *mut u8) -> usize;
}

/// An HMAC algorithm, chosen by one of this module's constants.
pub struct Algorithm {
    pub(crate) id: u32,
    pub(crate) name: &'static str,
    tag_len: usize,
}

impl Algorithm {
    /// The length of this algorithm's tag, in bytes.
    pub fn tag_len(&self) -> usize {
        self.tag_len
    }
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Algorithm")
            .field(&format_args!("{}", self.name))
            .finish()
    }
}

/// HMAC-SHA256.
pub static HMAC_SHA256: Algorithm = Algorithm {
    id: ids::hash::SHA256,
    name: "Sha256",
    tag_len: 32,
};

/// HMAC-SHA384.
pub static HMAC_SHA384: Algorithm = Algorithm {
    id: ids::hash::SHA384,
    name: "Sha384",
    tag_len: 48,
};

/// HMAC-SHA512.
pub static HMAC_SHA512: Algorithm = Algorithm {
    id: ids::hash::SHA512,
    name: "Sha512",
    tag_len: 64,
};

/// HMAC algorithms only legacy protocols should use.
pub mod legacy {
    use super::{Algorithm, ids};

    /// HMAC-SHA1, for legacy protocols only.
    ///
    /// HMAC does not rely on SHA-1's broken collision resistance, and STUN
    /// (RFC 8489) and SRTP (RFC 3711) still require it.
    pub static HMAC_SHA1: Algorithm = Algorithm {
        id: ids::hash::SHA1,
        name: "Sha1",
        tag_len: 20,
    };
}

/// An HMAC key, keyed once and reused for every message; held in the
/// module, which wipes it on drop.
pub struct Key {
    algorithm: &'static Algorithm,
    pub(crate) handle: Handle<HmacKey>,
}

impl Key {
    /// Keys `algorithm` with `key_value`, which may be any length.
    pub fn new(algorithm: &'static Algorithm, key_value: &[u8]) -> Self {
        // SAFETY: `key_value` is readable.
        let handle =
            unsafe { rind_fips_hmac_key_new(algorithm.id, key_value.as_ptr(), key_value.len()) };
        Self::from_handle(algorithm, handle)
    }

    pub(crate) fn from_handle(algorithm: &'static Algorithm, handle: *mut HmacKey) -> Self {
        Self {
            algorithm,
            handle: Handle::new(handle),
        }
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }
}

impl Clone for Key {
    fn clone(&self) -> Self {
        // SAFETY: the handle is live.
        Self::from_handle(self.algorithm, unsafe {
            rind_fips_hmac_key_clone(self.handle.ptr())
        })
    }
}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Key")
            .field("algorithm", &format_args!("{}", self.algorithm.name))
            .finish_non_exhaustive()
    }
}

/// An in-progress tag computation, for a message given in pieces; held in
/// the module, which wipes it on drop.
///
/// A clone forks the computation, so messages sharing a prefix process it once.
pub struct Context {
    algorithm: &'static Algorithm,
    handle: Handle<HmacContext>,
}

impl Context {
    /// Starts a tag computation under `key`.
    pub fn with_key(key: &Key) -> Self {
        Self {
            algorithm: key.algorithm,
            // SAFETY: the key's handle is live.
            handle: Handle::new(unsafe { rind_fips_hmac_context_new(key.handle.ptr()) }),
        }
    }

    /// Adds `data` to the message.
    pub fn update(&mut self, data: &[u8]) {
        // SAFETY: the handle is live, and `data` readable.
        unsafe { rind_fips_hmac_context_update(self.handle.ptr(), data.as_ptr(), data.len()) }
    }

    /// Returns the tag of the message.
    #[must_use]
    pub fn sign(self) -> Tag {
        let mut tag = Tag::zeroed(self.algorithm);
        // SAFETY: the handle is live, and the service frees it; `tag.value`
        // is 64 writable bytes.
        unsafe { rind_fips_hmac_context_sign(self.handle.into_ptr(), tag.value.as_mut_ptr()) };
        tag
    }
}

impl Clone for Context {
    fn clone(&self) -> Self {
        Self {
            algorithm: self.algorithm,
            // SAFETY: the handle is live.
            handle: Handle::new(unsafe { rind_fips_hmac_context_clone(self.handle.ptr()) }),
        }
    }
}

impl fmt::Debug for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Context")
            .field("algorithm", &format_args!("{}", self.algorithm.name))
            .finish_non_exhaustive()
    }
}

/// Returns the tag of `data` under `key`.
#[must_use]
pub fn sign(key: &Key, data: &[u8]) -> Tag {
    let mut tag = Tag::zeroed(key.algorithm);
    // SAFETY: the handle is live, `data` readable, and `tag.value` 64
    // writable bytes.
    unsafe {
        rind_fips_hmac_sign(
            key.handle.ptr(),
            data.as_ptr(),
            data.len(),
            tag.value.as_mut_ptr(),
        )
    };
    tag
}

/// Checks in constant time that `tag` is the whole tag of `data` under `key`.
///
/// Fails with [`Error::BadSignature`] otherwise, including for a truncated tag.
/// To check a tag over a message fed in pieces, or one truncated to a length
/// the protocol fixes (SRTP's HMAC-SHA1-80), sign with a [`Context`] or
/// [`sign`] and compare the agreed prefix with [`crate::constant_time::verify`].
pub fn verify(key: &Key, data: &[u8], tag: &[u8]) -> Result<(), Error> {
    // SAFETY: the handle is live, and `data` and `tag` readable.
    ffi::check(unsafe {
        rind_fips_hmac_verify(
            key.handle.ptr(),
            data.as_ptr(),
            data.len(),
            tag.as_ptr(),
            tag.len(),
        )
    })
}

/// An HMAC tag.
#[derive(Clone)]
pub struct Tag {
    algorithm: &'static Algorithm,
    value: [u8; 64],
}

impl Tag {
    fn zeroed(algorithm: &'static Algorithm) -> Self {
        Self {
            algorithm,
            value: [0; 64],
        }
    }
}

// The bytes stay out: a tag is secret where HMAC serves as a PRF.
impl fmt::Debug for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Tag")
            .field("algorithm", &format_args!("{}", self.algorithm.name))
            .finish_non_exhaustive()
    }
}

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        &self.value[..self.algorithm.tag_len]
    }
}
