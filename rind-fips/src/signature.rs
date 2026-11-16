// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! What the signature modules share: the module's public key handle, the
//! buffer signatures are written to, and the key pairs' loader.

use crate::Error;
use crate::encoding::{self, Encoded, Spki};
use crate::ffi::{self, Handle, Status, opaque};

pub(crate) mod ecdsa;
pub(crate) mod ed25519;
pub(crate) mod ml_dsa;
pub(crate) mod rsa;

opaque! {
    PublicKeyHandle => rind_fips_public_key_free,
}

unsafe extern "C" {
    fn rind_fips_public_key_new(
        id: u32,
        key: *const u8,
        len: usize,
        out: *mut *mut PublicKeyHandle,
    ) -> Status;
    fn rind_fips_public_key_from_spki(
        id: u32,
        der: *const u8,
        len: usize,
        out: *mut *mut PublicKeyHandle,
    ) -> Status;
    fn rind_fips_public_key_bytes(key: *const PublicKeyHandle, len: *mut usize) -> *const u8;
    fn rind_fips_public_key_clone(key: *const PublicKeyHandle) -> *mut PublicKeyHandle;
    fn rind_fips_public_key_to_spki(key: *const PublicKeyHandle) -> *mut ffi::Encoded;
    fn rind_fips_public_key_verify(
        key: *const PublicKeyHandle,
        message: *const u8,
        len: usize,
        signature: *const u8,
        signature_len: usize,
    ) -> Status;
}

/// The hash a signature algorithm applies to the message, as rind's
/// `Debug` shows it.
#[derive(Clone, Copy, Debug, PartialEq)]
enum HashId {
    Sha256,
    Sha384,
    Sha512,
}

/// A public key the module holds, of whichever algorithm.
struct Key(Handle<PublicKeyHandle>);

impl Key {
    /// Takes ownership of a key the module made.
    fn from_handle(handle: *mut PublicKeyHandle) -> Self {
        Self(Handle::new(handle))
    }

    /// Runs `parse`, which writes a key to its argument and returns its
    /// status.
    fn parse(parse: impl FnOnce(*mut *mut PublicKeyHandle) -> Status) -> Result<Self, Error> {
        let mut out = core::ptr::null_mut();
        let status = parse(&mut out);
        Handle::from_status(status, out).map(Self)
    }

    /// Parses `bytes` as a key for verification algorithm `id`, other than
    /// RSA's.
    fn new(id: u32, bytes: &[u8]) -> Result<Self, Error> {
        // SAFETY: `bytes` is readable, and `out` writable.
        Self::parse(|out| unsafe { rind_fips_public_key_new(id, bytes.as_ptr(), bytes.len(), out) })
    }

    /// Parses `der` as a `SubjectPublicKeyInfo` for verification algorithm
    /// `id`, other than RSA's.
    fn from_spki(id: u32, der: &[u8]) -> Result<Self, Error> {
        // SAFETY: `der` is readable, and `out` writable.
        Self::parse(|out| unsafe {
            rind_fips_public_key_from_spki(id, der.as_ptr(), der.len(), out)
        })
    }

    fn ptr(&self) -> *mut PublicKeyHandle {
        self.0.ptr()
    }

    fn bytes(&self) -> &[u8] {
        let mut len = 0;
        // SAFETY: the handle is live, and its bytes live as long as it,
        // which `&self` borrows.
        unsafe {
            core::slice::from_raw_parts(rind_fips_public_key_bytes(self.ptr(), &mut len), len)
        }
    }

    fn to_spki(&self) -> Spki {
        // SAFETY: the handle is live.
        Spki::from(Encoded::new(unsafe {
            rind_fips_public_key_to_spki(self.ptr())
        }))
    }

    /// Verifies with a key bound to its algorithm: any but RSA's.
    fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        // SAFETY: the handle is live, and `message` and `signature`
        // readable.
        ffi::check(unsafe {
            rind_fips_public_key_verify(
                self.ptr(),
                message.as_ptr(),
                message.len(),
                signature.as_ptr(),
                signature.len(),
            )
        })
    }
}

impl Clone for Key {
    fn clone(&self) -> Self {
        // SAFETY: the handle is live.
        Self::from_handle(unsafe { rind_fips_public_key_clone(self.ptr()) })
    }
}

/// Up to `N` bytes of a signature.
#[derive(Clone, Copy)]
struct Buffer<const N: usize> {
    bytes: [u8; N],
    len: usize,
}

impl<const N: usize> Buffer<N> {
    /// Runs `sign`, which writes a signature to the buffer it is given,
    /// with its capacity, and the signature's length to its last argument,
    /// returning its status.
    fn write(sign: impl FnOnce(*mut u8, usize, *mut usize) -> Status) -> Result<Self, Error> {
        let mut buffer = Self {
            bytes: [0; N],
            len: 0,
        };
        ffi::check(sign(buffer.bytes.as_mut_ptr(), N, &mut buffer.len))?;
        Ok(buffer)
    }

    fn bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

/// Encodes into an [`encoding::Pkcs8`] what the module wrote.
fn pkcs8(handle: *mut ffi::Encoded) -> encoding::Pkcs8 {
    encoding::Pkcs8(Encoded::new(handle))
}

/// Writes through `load` the handle of a key pair it loads, taking
/// ownership of it if its status is 0.
fn load<T: ffi::Opaque>(load: impl FnOnce(*mut *mut T) -> Status) -> Result<Handle<T>, Error> {
    let mut out = core::ptr::null_mut();
    let status = load(&mut out);
    Handle::from_status(status, out)
}
