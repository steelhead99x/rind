// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use super::{
    CurveId, Ecdsa, EcdsaEncoding, HashId, PublicKey, PublicKeyHandle, Signature, Verification,
    load, pkcs8,
};
use crate::Error;
use crate::digest::Digest;
use crate::encoding::{Encoded, Pkcs8, Sec1, Spki};
use crate::ffi::{self, Handle, Status, opaque};

opaque! {
    EcdsaHandle => rind_fips_ecdsa_free,
}

unsafe extern "C" {
    fn rind_fips_ecdsa_generate(id: u32, out: *mut *mut EcdsaHandle) -> Status;
    fn rind_fips_ecdsa_from_pkcs8(
        id: u32,
        der: *const u8,
        len: usize,
        out: *mut *mut EcdsaHandle,
    ) -> Status;
    fn rind_fips_ecdsa_from_sec1(
        id: u32,
        der: *const u8,
        len: usize,
        out: *mut *mut EcdsaHandle,
    ) -> Status;
    fn rind_fips_ecdsa_from_scalar_and_public_key(
        id: u32,
        scalar: *const u8,
        scalar_len: usize,
        public_key: *const u8,
        public_key_len: usize,
        out: *mut *mut EcdsaHandle,
    ) -> Status;
    fn rind_fips_ecdsa_public_key(key: *const EcdsaHandle) -> *mut PublicKeyHandle;
    fn rind_fips_ecdsa_sign(
        key: *const EcdsaHandle,
        message: *const u8,
        len: usize,
        out: *mut u8,
        cap: usize,
        out_len: *mut usize,
    ) -> Status;
    fn rind_fips_ecdsa_sign_digest(
        key: *const EcdsaHandle,
        hash: u32,
        value: *const u8,
        len: usize,
        out: *mut u8,
        cap: usize,
        out_len: *mut usize,
    ) -> Status;
    fn rind_fips_ecdsa_to_pkcs8(key: *const EcdsaHandle) -> *mut ffi::Encoded;
    fn rind_fips_ecdsa_to_scalar(key: *const EcdsaHandle) -> *mut ffi::Encoded;
    fn rind_fips_ecdsa_to_sec1(key: *const EcdsaHandle) -> *mut ffi::Encoded;
    fn rind_fips_ecdsa_to_spki(key: *const EcdsaHandle) -> *mut ffi::Encoded;
}

/// An ECDSA signing algorithm, which an [`EcdsaKeyPair`] is bound to.
pub struct EcdsaSigningAlgorithm {
    id: u32,
    ecdsa: Ecdsa,
}

impl EcdsaSigningAlgorithm {
    pub(super) const fn new(
        id: u32,
        curve: CurveId,
        hash: HashId,
        encoding: EcdsaEncoding,
    ) -> Self {
        Self {
            id,
            ecdsa: Ecdsa {
                curve,
                hash,
                encoding,
            },
        }
    }
}

impl fmt::Debug for EcdsaSigningAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("EcdsaSigningAlgorithm")
            .field(&self.ecdsa)
            .finish()
    }
}

/// An ECDSA private key and its public key, bound to one signing
/// algorithm; held in the module, which wipes it on drop.
pub struct EcdsaKeyPair {
    algorithm: &'static EcdsaSigningAlgorithm,
    handle: Handle<EcdsaHandle>,
}

impl EcdsaKeyPair {
    fn load(
        algorithm: &'static EcdsaSigningAlgorithm,
        load_with: impl FnOnce(*mut *mut EcdsaHandle) -> Status,
    ) -> Result<Self, Error> {
        load(load_with).map(|handle| Self { algorithm, handle })
    }

    /// Generates a key pair for `algorithm` from the module's random
    /// generator, then checks that it signs what its public key verifies.
    pub fn generate(algorithm: &'static EcdsaSigningAlgorithm) -> Result<Self, Error> {
        // SAFETY: `out` is writable.
        Self::load(algorithm, |out| unsafe {
            rind_fips_ecdsa_generate(algorithm.id, out)
        })
    }

    /// Loads a PKCS#8 v1 `ECPrivateKey` on `algorithm`'s curve.
    pub fn from_pkcs8(
        algorithm: &'static EcdsaSigningAlgorithm,
        der: &[u8],
    ) -> Result<Self, Error> {
        Self::load(algorithm, |out| {
            // SAFETY: `der` is readable, and `out` writable.
            unsafe { rind_fips_ecdsa_from_pkcs8(algorithm.id, der.as_ptr(), der.len(), out) }
        })
    }

    /// Loads a SEC1 (RFC 5915) `ECPrivateKey` on `algorithm`'s curve.
    ///
    /// This refuses PKCS#8, which [`Self::from_pkcs8`] takes: a caller always
    /// knows which of the two it holds.
    pub fn from_sec1(algorithm: &'static EcdsaSigningAlgorithm, der: &[u8]) -> Result<Self, Error> {
        Self::load(algorithm, |out| {
            // SAFETY: `der` is readable, and `out` writable.
            unsafe { rind_fips_ecdsa_from_sec1(algorithm.id, der.as_ptr(), der.len(), out) }
        })
    }

    /// Loads a fixed-length big-endian private scalar, refused unless
    /// `public_key`, an X9.62 uncompressed or compressed point, is its public
    /// key.
    ///
    /// This suits a JWK's `d` and `x`/`y`; prefer [`Self::from_pkcs8`] for
    /// stored keys.
    pub fn from_scalar_and_public_key(
        algorithm: &'static EcdsaSigningAlgorithm,
        scalar: &[u8],
        public_key: &[u8],
    ) -> Result<Self, Error> {
        Self::load(algorithm, |out| {
            // SAFETY: `scalar` and `public_key` are readable, and `out`
            // writable.
            unsafe {
                rind_fips_ecdsa_from_scalar_and_public_key(
                    algorithm.id,
                    scalar.as_ptr(),
                    scalar.len(),
                    public_key.as_ptr(),
                    public_key.len(),
                    out,
                )
            }
        })
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> PublicKey {
        // SAFETY: the handle is live.
        let handle = unsafe { rind_fips_ecdsa_public_key(self.handle.ptr()) };
        PublicKey::from_handle(handle, Verification::Ecdsa(self.algorithm.ecdsa))
    }

    /// Signs `message` with a fresh nonce.
    pub fn sign(&self, message: &[u8]) -> Result<Signature, Error> {
        Signature::write(|out, cap, len| {
            // SAFETY: the handle is live, `message` readable, `out` writable
            // for `cap`, and `len` writable.
            unsafe {
                rind_fips_ecdsa_sign(
                    self.handle.ptr(),
                    message.as_ptr(),
                    message.len(),
                    out,
                    cap,
                    len,
                )
            }
        })
    }

    /// Signs the message `digest` hashes, with a fresh nonce.
    ///
    /// The digest's hash, SHA-256, SHA-384, or SHA-512, replaces the
    /// algorithm's, which still fixes the signature's encoding, so
    /// [`Self::public_key`] verifies the signature over the message only if
    /// the hashes match; [`PublicKey::verify_digest`] verifies it in any
    /// case. Another hash is refused as [`Error::Unsupported`].
    pub fn sign_digest(&self, digest: &Digest) -> Result<Signature, Error> {
        let value = digest.as_ref();
        Signature::write(|out, cap, len| {
            // SAFETY: the handle is live, `value` readable, `out` writable
            // for `cap`, and `len` writable.
            unsafe {
                rind_fips_ecdsa_sign_digest(
                    self.handle.ptr(),
                    digest.algorithm.id,
                    value.as_ptr(),
                    value.len(),
                    out,
                    cap,
                    len,
                )
            }
        })
    }

    /// Encodes the private key as PKCS#8.
    pub fn to_pkcs8(&self) -> Pkcs8 {
        // SAFETY: the handle is live.
        pkcs8(unsafe { rind_fips_ecdsa_to_pkcs8(self.handle.ptr()) })
    }

    /// Encodes the private key as a big-endian scalar exactly the curve's
    /// length, as a JWK's `d` and SEC1's `privateKey` hold it.
    ///
    /// This is what [`Self::from_scalar_and_public_key`] loads; prefer
    /// [`Self::to_pkcs8`] for stored keys.
    pub fn to_scalar(&self) -> EcdsaScalar {
        // SAFETY: the handle is live.
        EcdsaScalar(Encoded::new(unsafe {
            rind_fips_ecdsa_to_scalar(self.handle.ptr())
        }))
    }

    /// Encodes the private key as a SEC1 (RFC 5915) `ECPrivateKey` naming
    /// its curve and holding its public key, as OpenSSL writes it.
    ///
    /// This is what [`Self::from_sec1`] loads; [`Self::to_pkcs8`] holds the
    /// same `ECPrivateKey` without its curve, which PKCS#8 names instead.
    pub fn to_sec1(&self) -> Sec1 {
        // SAFETY: the handle is live.
        Sec1(Encoded::new(unsafe {
            rind_fips_ecdsa_to_sec1(self.handle.ptr())
        }))
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`.
    pub fn to_spki(&self) -> Spki {
        // SAFETY: the handle is live.
        Spki::from(Encoded::new(unsafe {
            rind_fips_ecdsa_to_spki(self.handle.ptr())
        }))
    }
}

impl fmt::Debug for EcdsaKeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let public_key = self.public_key();
        f.debug_struct("EcdsaKeyPair")
            .field("algorithm", &self.algorithm.ecdsa)
            .field("public_key", &public_key.as_ref())
            .finish_non_exhaustive()
    }
}

/// An ECDSA private key as a big-endian scalar exactly the curve's length,
/// held in the module, which wipes it on drop.
pub struct EcdsaScalar(Encoded);

impl AsRef<[u8]> for EcdsaScalar {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for EcdsaScalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("EcdsaScalar").finish_non_exhaustive()
    }
}
