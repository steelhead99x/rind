// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use super::{
    HashId, PublicKey, PublicKeyHandle, Signature, Verification, VerificationAlgorithm, load, pkcs8,
};
use crate::Error;
use crate::encoding::{Encoded, Pkcs8, Spki};
use crate::ffi::{self, Handle, Status, ids, opaque};

opaque! {
    RsaHandle => rind_fips_rsa_free,
}

unsafe extern "C" {
    fn rind_fips_rsa_generate(size: u32, out: *mut *mut RsaHandle) -> Status;
    fn rind_fips_rsa_from_pkcs8(der: *const u8, len: usize, out: *mut *mut RsaHandle) -> Status;
    fn rind_fips_rsa_from_pkcs1(der: *const u8, len: usize, out: *mut *mut RsaHandle) -> Status;
    fn rind_fips_rsa_public_key(key: *const RsaHandle, id: u32) -> *mut PublicKeyHandle;
    fn rind_fips_rsa_sign(
        key: *const RsaHandle,
        id: u32,
        message: *const u8,
        len: usize,
        out: *mut u8,
        cap: usize,
        out_len: *mut usize,
    ) -> Status;
    fn rind_fips_rsa_to_pkcs8(key: *const RsaHandle) -> *mut ffi::Encoded;
    fn rind_fips_rsa_to_spki(key: *const RsaHandle) -> *mut ffi::Encoded;
}

/// The modulus size of an RSA key pair to generate.
#[derive(Clone, Copy, Debug, PartialEq)]
#[non_exhaustive]
pub enum KeySize {
    /// A 2048-bit modulus.
    Rsa2048,
    /// A 3072-bit modulus.
    Rsa3072,
    /// A 4096-bit modulus.
    Rsa4096,
    /// A 6144-bit modulus.
    Rsa6144,
    /// An 8192-bit modulus.
    Rsa8192,
}

impl KeySize {
    fn id(self) -> u32 {
        use ids::rsa_size::*;
        match self {
            Self::Rsa2048 => RSA_2048,
            Self::Rsa3072 => RSA_3072,
            Self::Rsa4096 => RSA_4096,
            Self::Rsa6144 => RSA_6144,
            Self::Rsa8192 => RSA_8192,
        }
    }
}

/// An RSA public key as its big-endian modulus and exponent, as a JWK
/// carries it, rather than DER.
#[derive(Clone, Copy, Debug)]
pub struct PublicKeyComponents<B> {
    /// The modulus, without leading zero bytes.
    pub n: B,
    /// The public exponent, without leading zero bytes.
    pub e: B,
}

/// How long an RSASSA-PSS salt is: always the hash's length here.
#[derive(Clone, Copy, Debug, PartialEq)]
enum PssSalt {
    Hash,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum RsaPadding {
    /// RSASSA-PKCS1-v1_5.
    Pkcs1,
    /// RSASSA-PSS, with MGF1 on the same hash and a salt of this length.
    Pss(PssSalt),
}

#[derive(Clone, Copy, Debug)]
#[allow(dead_code, reason = "only `Debug` reads it, as rind's")]
pub(super) struct RsaScheme {
    padding: RsaPadding,
    hash: HashId,
}

impl RsaScheme {
    pub(super) const fn pkcs1(hash: HashId) -> Self {
        Self {
            padding: RsaPadding::Pkcs1,
            hash,
        }
    }

    pub(super) const fn pss(hash: HashId) -> Self {
        Self {
            padding: RsaPadding::Pss(PssSalt::Hash),
            hash,
        }
    }
}

/// What an RSA verification algorithm verifies: a scheme rind-fips also
/// signs with, or PKCS#1 v1.5 with SHA-1, which it only verifies.
#[derive(Clone, Copy, Debug)]
#[allow(dead_code, reason = "only `Debug` reads it, as rind's")]
pub(super) enum RsaVerification {
    Scheme(RsaScheme),
    Pkcs1Sha1,
}

/// An RSA verification algorithm: what it verifies and the smallest
/// modulus it accepts.
#[derive(Clone, Copy)]
pub(super) struct Rsa {
    pub(super) verification: RsaVerification,
    min_bits: usize,
}

impl fmt::Debug for Rsa {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Rsa")
            .field("verification", &self.verification)
            .field("min_bits", &self.min_bits)
            .finish()
    }
}

/// An RSA signature verification algorithm, which
/// [`PublicKey::from_components`] also takes.
pub struct RsaVerificationAlgorithm {
    rsa: Rsa,
    algorithm: VerificationAlgorithm,
}

impl RsaVerificationAlgorithm {
    const fn new(id: u32, verification: RsaVerification, min_bits: usize) -> Self {
        let rsa = Rsa {
            verification,
            min_bits,
        };
        Self {
            rsa,
            algorithm: VerificationAlgorithm {
                id,
                verification: Verification::Rsa(rsa),
            },
        }
    }

    pub(super) const fn scheme(id: u32, scheme: RsaScheme, min_bits: usize) -> Self {
        Self::new(id, RsaVerification::Scheme(scheme), min_bits)
    }

    pub(super) const fn sha1(id: u32, min_bits: usize) -> Self {
        Self::new(id, RsaVerification::Pkcs1Sha1, min_bits)
    }
}

impl AsRef<VerificationAlgorithm> for RsaVerificationAlgorithm {
    fn as_ref(&self) -> &VerificationAlgorithm {
        &self.algorithm
    }
}

impl fmt::Debug for RsaVerificationAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.rsa.fmt(f)
    }
}

/// An RSA signing algorithm: a padding and a hash, for [`RsaKeyPair::sign`].
pub struct RsaSigningAlgorithm {
    id: u32,
    scheme: RsaScheme,
}

impl RsaSigningAlgorithm {
    pub(super) const fn new(id: u32, scheme: RsaScheme) -> Self {
        Self { id, scheme }
    }
}

impl fmt::Debug for RsaSigningAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("RsaSigningAlgorithm")
            .field(&self.scheme)
            .finish()
    }
}

/// A two-prime RSA private key, with a modulus of an even number of bits
/// from 2048 to 8192, and its public key; held in the module, which wipes
/// it on drop.
pub struct RsaKeyPair {
    handle: Handle<RsaHandle>,
}

impl RsaKeyPair {
    /// Generates a key pair of `size` from the module's random generator,
    /// then checks that it signs what its public key verifies.
    ///
    /// This is slow: about 30 milliseconds for 2048 bits, and 15 seconds or
    /// more for 8192 bits, with no upper bound. Its timing reveals only which
    /// candidate primes it discards.
    pub fn generate(size: KeySize) -> Result<Self, Error> {
        // SAFETY: `out` is writable.
        load(|out| unsafe { rind_fips_rsa_generate(size.id(), out) }).map(|handle| Self { handle })
    }

    /// Loads a PKCS#8 v1 RSA private key, named `rsaEncryption`,
    /// `id-RSAES-OAEP`, or `id-ea-rsa`.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        // SAFETY: `der` is readable, and `out` writable.
        load(|out| unsafe { rind_fips_rsa_from_pkcs8(der.as_ptr(), der.len(), out) })
            .map(|handle| Self { handle })
    }

    /// Loads a PKCS#1 `RSAPrivateKey`.
    pub fn from_pkcs1(der: &[u8]) -> Result<Self, Error> {
        // SAFETY: `der` is readable, and `out` writable.
        load(|out| unsafe { rind_fips_rsa_from_pkcs1(der.as_ptr(), der.len(), out) })
            .map(|handle| Self { handle })
    }

    /// Returns the public key, which verifies what this key pair signs with
    /// `algorithm`.
    ///
    /// Unlike an ECDSA key pair, an RSA key pair signs with any padding and
    /// hash, so the public key needs the one it verifies.
    pub fn public_key(&self, algorithm: &RsaSigningAlgorithm) -> PublicKey {
        // SAFETY: the handle is live.
        let handle = unsafe { rind_fips_rsa_public_key(self.handle.ptr(), algorithm.id) };
        let rsa = Rsa {
            verification: RsaVerification::Scheme(algorithm.scheme),
            min_bits: 2048,
        };
        PublicKey::from_handle(handle, Verification::Rsa(rsa))
    }

    /// Signs `message` with `algorithm`, as long as the modulus.
    pub fn sign(
        &self,
        algorithm: &RsaSigningAlgorithm,
        message: &[u8],
    ) -> Result<Signature, Error> {
        Signature::write(|out, cap, len| {
            // SAFETY: the handle is live, `message` readable, `out` writable
            // for `cap`, and `len` writable.
            unsafe {
                rind_fips_rsa_sign(
                    self.handle.ptr(),
                    algorithm.id,
                    message.as_ptr(),
                    message.len(),
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
        pkcs8(unsafe { rind_fips_rsa_to_pkcs8(self.handle.ptr()) })
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`.
    pub fn to_spki(&self) -> Spki {
        // SAFETY: the handle is live.
        Spki::from(Encoded::new(unsafe {
            rind_fips_rsa_to_spki(self.handle.ptr())
        }))
    }
}

impl fmt::Debug for RsaKeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let public_key = self.public_key(&super::sign::RSA_PKCS1_SHA256);
        f.debug_struct("RsaKeyPair")
            .field("public_key", &public_key.as_ref())
            .finish_non_exhaustive()
    }
}
