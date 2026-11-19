// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::Error;
use crate::ffi::{self, Handle, Status};

/// An encoding the module made and still holds, such as a private key's,
/// which wipes itself when the handle is freed.
pub(crate) struct Encoded(Handle<ffi::Encoded>);

impl Encoded {
    /// Takes ownership of `handle`.
    pub(crate) fn new(handle: *mut ffi::Encoded) -> Self {
        Self(Handle::new(handle))
    }

    /// Takes ownership of what a service wrote to `out` if `status` is 0.
    pub(crate) fn from_status(status: Status, out: *mut ffi::Encoded) -> Result<Self, Error> {
        Handle::from_status(status, out).map(Self)
    }

    pub(crate) fn bytes(&self) -> &[u8] {
        let mut len = 0;
        // SAFETY: the handle is live, and its bytes live as long as it,
        // which `&self` borrows.
        unsafe {
            core::slice::from_raw_parts(ffi::rind_fips_encoded_bytes(self.0.ptr(), &mut len), len)
        }
    }
}

/// A private key encoded as PKCS#8 DER, held in the module, which wipes it
/// on drop.
pub struct Pkcs8(pub(crate) Encoded);

impl AsRef<[u8]> for Pkcs8 {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for Pkcs8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Pkcs8").finish_non_exhaustive()
    }
}

/// A public key encoded as a `SubjectPublicKeyInfo` in DER.
#[derive(Clone)]
pub struct Spki {
    bytes: [u8; SPKI_MAX_LEN],
    len: usize,
}

/// ML-DSA-87's 2592-byte public key, the longest the module encodes, and its
/// framing, as rind bounds its `Spki`.
const SPKI_MAX_LEN: usize = 2592 + 32;

impl From<Encoded> for Spki {
    fn from(encoded: Encoded) -> Self {
        let bytes = encoded.bytes();
        let mut spki = Self {
            bytes: [0; SPKI_MAX_LEN],
            len: bytes.len(),
        };
        spki.bytes[..bytes.len()].copy_from_slice(bytes);
        spki
    }
}

impl AsRef<[u8]> for Spki {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl fmt::Debug for Spki {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Spki").field(&self.as_ref()).finish()
    }
}

/// An ECDSA private key encoded as a SEC1 (RFC 5915) `ECPrivateKey` in
/// DER, held in the module, which wipes it on drop.
pub struct Sec1(pub(crate) Encoded);

impl AsRef<[u8]> for Sec1 {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for Sec1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Sec1").finish_non_exhaustive()
    }
}
