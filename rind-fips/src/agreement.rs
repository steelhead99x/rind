// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::Error;
use crate::encoding::{Encoded, Pkcs8, Spki};
use crate::ffi::{self, Handle, Status, ids, opaque};

opaque! {
    AgreementKey => rind_fips_agreement_key_free,
}

unsafe extern "C" {
    fn rind_fips_agreement_generate(id: u32, out: *mut *mut AgreementKey) -> Status;
    fn rind_fips_agreement_from_scalar(
        id: u32,
        scalar: *const u8,
        len: usize,
        out: *mut *mut AgreementKey,
    ) -> Status;
    fn rind_fips_agreement_from_pkcs8(
        id: u32,
        der: *const u8,
        len: usize,
        out: *mut *mut AgreementKey,
    ) -> Status;
    fn rind_fips_agreement_from_sec1(
        id: u32,
        der: *const u8,
        len: usize,
        out: *mut *mut AgreementKey,
    ) -> Status;
    fn rind_fips_agreement_public_key(key: *const AgreementKey, out: *mut u8) -> usize;
    fn rind_fips_agreement_agree(
        key: *const AgreementKey,
        peer: *const u8,
        len: usize,
        out: *mut *mut ffi::Encoded,
    ) -> Status;
    fn rind_fips_agreement_to_pkcs8(key: *const AgreementKey) -> *mut ffi::Encoded;
    fn rind_fips_agreement_to_scalar(key: *const AgreementKey) -> *mut ffi::Encoded;
    fn rind_fips_agreement_public_key_new(
        id: u32,
        key: *const u8,
        len: usize,
        out: *mut u8,
        out_len: *mut usize,
    ) -> Status;
    fn rind_fips_agreement_public_key_from_spki(
        id: u32,
        der: *const u8,
        len: usize,
        out: *mut u8,
        out_len: *mut usize,
    ) -> Status;
    fn rind_fips_agreement_public_key_to_spki(
        id: u32,
        key: *const u8,
        len: usize,
    ) -> *mut ffi::Encoded;
}

/// A key agreement algorithm: a curve and its public key encoding.
pub struct Algorithm {
    id: u32,
    name: &'static str,
}

impl PartialEq for Algorithm {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Algorithm {}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name)
    }
}

/// ECDH on P-256, with X9.62 uncompressed public keys.
///
/// [`PublicKey::new`] also takes compressed ones.
///
/// P-256 is also known as "NISTP256", "prime256v1", or "secp256r1".
pub static ECDH_P256: Algorithm = Algorithm {
    id: ids::curve::P256,
    name: "EcdhP256",
};

/// ECDH on P-384, with X9.62 uncompressed public keys.
///
/// [`PublicKey::new`] also takes compressed ones.
///
/// P-384 is also known as "NISTP384", or "secp384r1".
pub static ECDH_P384: Algorithm = Algorithm {
    id: ids::curve::P384,
    name: "EcdhP384",
};

/// ECDH on P-521, with X9.62 uncompressed public keys.
///
/// [`PublicKey::new`] also takes compressed ones.
///
/// P-521 is also known as "NISTP521", or "secp521r1".
pub static ECDH_P521: Algorithm = Algorithm {
    id: ids::curve::P521,
    name: "EcdhP521",
};

/// A private key, which agrees with any number of peers; held in the
/// module, which wipes it on drop.
///
/// It keeps its public key, computed once when it is generated or loaded.
pub struct PrivateKey {
    handle: Handle<AgreementKey>,
    public: PublicKey,
}

impl PrivateKey {
    /// Generates a private key for `algorithm` from the module's DRBG, after
    /// checking that its public key recomputes from it.
    pub fn generate(algorithm: &'static Algorithm) -> Result<Self, Error> {
        let mut out = core::ptr::null_mut();
        // SAFETY: `out` is writable.
        let status = unsafe { rind_fips_agreement_generate(algorithm.id, &mut out) };
        Self::from_status(algorithm, status, out)
    }

    /// Loads a private key for `algorithm` from its big-endian scalar,
    /// exactly the curve's length and refused unless it is from 1 to n - 1.
    ///
    /// This suits a JWK's `d`; prefer [`Self::from_pkcs8`] for stored keys.
    pub fn from_scalar(algorithm: &'static Algorithm, scalar: &[u8]) -> Result<Self, Error> {
        let mut out = core::ptr::null_mut();
        // SAFETY: `scalar` is readable, and `out` writable.
        let status = unsafe {
            rind_fips_agreement_from_scalar(algorithm.id, scalar.as_ptr(), scalar.len(), &mut out)
        };
        Self::from_status(algorithm, status, out)
    }

    /// Loads a PKCS#8 v1 `ECPrivateKey` on `algorithm`'s curve, as
    /// [`EcdsaKeyPair::from_pkcs8`](crate::signature::EcdsaKeyPair::from_pkcs8)
    /// does.
    pub fn from_pkcs8(algorithm: &'static Algorithm, der: &[u8]) -> Result<Self, Error> {
        let mut out = core::ptr::null_mut();
        // SAFETY: `der` is readable, and `out` writable.
        let status = unsafe {
            rind_fips_agreement_from_pkcs8(algorithm.id, der.as_ptr(), der.len(), &mut out)
        };
        Self::from_status(algorithm, status, out)
    }

    /// Loads a SEC1 (RFC 5915) `ECPrivateKey` on `algorithm`'s curve, as
    /// [`EcdsaKeyPair::from_sec1`](crate::signature::EcdsaKeyPair::from_sec1)
    /// does.
    pub fn from_sec1(algorithm: &'static Algorithm, der: &[u8]) -> Result<Self, Error> {
        let mut out = core::ptr::null_mut();
        // SAFETY: `der` is readable, and `out` writable.
        let status = unsafe {
            rind_fips_agreement_from_sec1(algorithm.id, der.as_ptr(), der.len(), &mut out)
        };
        Self::from_status(algorithm, status, out)
    }

    /// Takes the key a service wrote to `out` if `status` is 0, and copies
    /// its public key.
    fn from_status(
        algorithm: &'static Algorithm,
        status: Status,
        out: *mut AgreementKey,
    ) -> Result<Self, Error> {
        let handle = Handle::from_status(status, out)?;
        let mut public = PublicKey::empty(algorithm);
        // SAFETY: the handle is live, and `public.bytes` holds 133 bytes.
        public.len =
            unsafe { rind_fips_agreement_public_key(handle.ptr(), public.bytes.as_mut_ptr()) };
        Ok(Self { handle, public })
    }

    /// Returns the public key to send to the peer.
    pub fn public_key(&self) -> &PublicKey {
        &self.public
    }

    /// Returns the key's algorithm.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.public.algorithm()
    }

    /// Agrees on a secret with the peer's encoded public key.
    ///
    /// The peer's key is parsed for this key's algorithm, and refused if it
    /// is malformed or off the curve. It is an uncompressed point, as TLS
    /// sends it; [`PublicKey::new`] decompresses a compressed one.
    pub fn agree(&self, peer: &[u8]) -> Result<SharedSecret, Error> {
        let mut out = core::ptr::null_mut();
        // SAFETY: the handle is live, `peer` readable, and `out` writable.
        let status = unsafe {
            rind_fips_agreement_agree(self.handle.ptr(), peer.as_ptr(), peer.len(), &mut out)
        };
        Encoded::from_status(status, out).map(SharedSecret)
    }

    /// Encodes the private key as PKCS#8, as
    /// [`EcdsaKeyPair::to_pkcs8`](crate::signature::EcdsaKeyPair::to_pkcs8)
    /// does, with its public key.
    pub fn to_pkcs8(&self) -> Pkcs8 {
        // SAFETY: the handle is live.
        Pkcs8(Encoded::new(unsafe {
            rind_fips_agreement_to_pkcs8(self.handle.ptr())
        }))
    }

    /// Encodes the private key as the scalar [`Self::from_scalar`] loads.
    pub fn to_scalar(&self) -> Scalar {
        // SAFETY: the handle is live.
        Scalar(Encoded::new(unsafe {
            rind_fips_agreement_to_scalar(self.handle.ptr())
        }))
    }
}

impl fmt::Debug for PrivateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrivateKey")
            .field("algorithm", self.algorithm())
            .finish_non_exhaustive()
    }
}

/// A private key as its scalar, which [`PrivateKey::from_scalar`] loads;
/// held in the module, which wipes it on drop.
pub struct Scalar(Encoded);

impl AsRef<[u8]> for Scalar {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Scalar").finish_non_exhaustive()
    }
}

/// A public key: an X9.62 uncompressed point.
#[derive(Clone)]
pub struct PublicKey {
    algorithm: &'static Algorithm,
    bytes: [u8; Self::MAX_LEN],
    len: usize,
}

impl PublicKey {
    // P-521's uncompressed point.
    const MAX_LEN: usize = 133;

    fn empty(algorithm: &'static Algorithm) -> Self {
        Self {
            algorithm,
            bytes: [0; Self::MAX_LEN],
            len: 0,
        }
    }

    /// Parses a peer's public key for `algorithm`: an X9.62 point,
    /// uncompressed or compressed, refused off the curve.
    ///
    /// Its bytes are then what [`PrivateKey::agree`] takes, the point
    /// uncompressed.
    pub fn new(algorithm: &'static Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        let mut key = Self::empty(algorithm);
        // SAFETY: `bytes` is readable, `key.bytes` holds 133 writable
        // bytes, and `key.len` is writable.
        ffi::check(unsafe {
            rind_fips_agreement_public_key_new(
                algorithm.id,
                bytes.as_ptr(),
                bytes.len(),
                key.bytes.as_mut_ptr(),
                &mut key.len,
            )
        })?;
        Ok(key)
    }

    /// Parses a public key for `algorithm` from its `SubjectPublicKeyInfo`
    /// DER, as [`Self::new`] parses the key it holds.
    ///
    /// It names `id-ecPublicKey` and the curve, or, as WebCrypto also takes
    /// for ECDH, `id-ecDH`.
    pub fn from_spki(algorithm: &'static Algorithm, der: &[u8]) -> Result<Self, Error> {
        let mut key = Self::empty(algorithm);
        // SAFETY: as for `new`.
        ffi::check(unsafe {
            rind_fips_agreement_public_key_from_spki(
                algorithm.id,
                der.as_ptr(),
                der.len(),
                key.bytes.as_mut_ptr(),
                &mut key.len,
            )
        })?;
        Ok(key)
    }

    /// Returns the key's algorithm.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`: `id-ecPublicKey`
    /// on the key's curve.
    pub fn to_spki(&self) -> Spki {
        let key = self.as_ref();
        // SAFETY: `key` is readable.
        let spki = unsafe {
            rind_fips_agreement_public_key_to_spki(self.algorithm.id, key.as_ptr(), key.len())
        };
        Spki::from(Encoded::new(spki))
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PublicKey").field(&self.as_ref()).finish()
    }
}

/// The secret both parties agree on; held in the module, which wipes it on
/// drop.
pub struct SharedSecret(Encoded);

impl AsRef<[u8]> for SharedSecret {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for SharedSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SharedSecret").finish_non_exhaustive()
    }
}
