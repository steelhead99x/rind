// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use super::{Buffer, HashId, Key, PublicKeyHandle, load, pkcs8};
use crate::Error;
use crate::digest::Digest;
use crate::encoding::{Encoded, Pkcs8, Sec1, Spki};
use crate::ffi::{self, Handle, Status, opaque};

opaque! {
    EcdsaHandle => rind_fips_ecdsa_free,
}

unsafe extern "C" {
    fn rind_fips_public_key_verify_digest(
        key: *const PublicKeyHandle,
        hash: u32,
        value: *const u8,
        len: usize,
        signature: *const u8,
        signature_len: usize,
    ) -> Status;
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
}

// What the algorithms are, as rind's `Debug` shows them.

#[derive(Clone, Copy, Debug, PartialEq)]
enum CurveId {
    P256,
    P384,
    P521,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum EcdsaEncoding {
    /// A DER `Ecdsa-Sig-Value`, as X.509 and TLS use.
    Asn1,
    /// `r || s`, each the curve's scalar length, as JWS uses.
    Fixed,
}

/// A curve, a hash, and a signature encoding.
#[derive(Clone, Copy, Debug)]
#[allow(dead_code, reason = "only `Debug` reads it, as rind's")]
struct Ecdsa {
    curve: CurveId,
    hash: HashId,
    encoding: EcdsaEncoding,
}

/// An ECDSA verification algorithm: a curve, a hash, and a signature
/// encoding, which a [`PublicKey`] is bound to.
pub struct VerificationAlgorithm {
    id: u32,
    ecdsa: Ecdsa,
}

impl fmt::Debug for VerificationAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VerificationAlgorithm")
            .field(&self.ecdsa)
            .finish()
    }
}

/// An ECDSA public key, bound to the one algorithm it verifies signatures
/// with.
///
/// Its bytes are its X9.62 uncompressed point.
#[derive(Clone)]
pub struct PublicKey {
    key: Key,
    algorithm: Ecdsa,
}

impl PublicKey {
    /// Parses an X9.62 uncompressed point for `algorithm`, refusing a
    /// malformed key, or a compressed point, before any signature arrives.
    pub fn new(algorithm: &VerificationAlgorithm, point: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            key: Key::new(algorithm.id, point)?,
            algorithm: algorithm.ecdsa,
        })
    }

    /// Parses a public key for `algorithm` from its `SubjectPublicKeyInfo`
    /// DER, naming `id-ecPublicKey` and the algorithm's curve, refusing one
    /// that names another.
    ///
    /// Its point may be compressed (RFC 5480), which this decompresses.
    pub fn from_spki(algorithm: &VerificationAlgorithm, der: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            key: Key::from_spki(algorithm.id, der)?,
            algorithm: algorithm.ecdsa,
        })
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`: `id-ecPublicKey`
    /// on its curve, with its uncompressed point.
    pub fn to_spki(&self) -> Spki {
        self.key.to_spki()
    }

    /// Verifies `signature` over `message`, refusing a malformed signature.
    ///
    /// ECDSA signatures are malleable: `(r, s)` and `(r, n - s)` both verify,
    /// so don't identify a message by its signature's bytes.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        self.key.verify(message, signature)
    }

    /// Verifies `signature` over the message `digest` hashes.
    ///
    /// The digest's hash, SHA-256, SHA-384, or SHA-512, replaces the
    /// algorithm's, which still fixes the curve and the signature's encoding.
    /// Another hash is refused as [`Error::Unsupported`].
    ///
    /// So unlike [`Self::verify`], this does not pin the hash: hash with the
    /// one your protocol names, never one the signed data or its sender
    /// picks. A signature over one SHA-2 hash verifies over another only
    /// for a message whose digest collides with it, which no one can find.
    pub fn verify_digest(&self, digest: &Digest, signature: &[u8]) -> Result<(), Error> {
        let value = digest.as_ref();
        // SAFETY: the handle is live, and `value` and `signature` readable.
        ffi::check(unsafe {
            rind_fips_public_key_verify_digest(
                self.key.ptr(),
                digest.algorithm.id,
                value.as_ptr(),
                value.len(),
                signature.as_ptr(),
                signature.len(),
            )
        })
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.key.bytes()
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicKey")
            .field("algorithm", &self.algorithm)
            .field("bytes", &self.as_ref())
            .finish()
    }
}

/// An ECDSA signature: a DER `Ecdsa-Sig-Value`, or `r || s` for the
/// `FIXED` algorithms.
#[derive(Clone, Copy)]
pub struct Signature(Buffer<SIGNATURE_MAX_LEN>);

/// P-521's longest DER `Ecdsa-Sig-Value`, as rind bounds it.
const SIGNATURE_MAX_LEN: usize = 3 + 2 * (2 + 66 + 1);

impl Signature {
    fn write(sign: impl FnOnce(*mut u8, usize, *mut usize) -> Status) -> Result<Self, Error> {
        Buffer::write(sign).map(Self)
    }
}

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Signature").field(&self.as_ref()).finish()
    }
}

/// An ECDSA private key as a big-endian scalar exactly the curve's length,
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

/// An ECDSA signing algorithm, which a [`KeyPair`] is bound to.
pub struct SigningAlgorithm {
    id: u32,
    ecdsa: Ecdsa,
}

impl fmt::Debug for SigningAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SigningAlgorithm")
            .field(&self.ecdsa)
            .finish()
    }
}

/// An ECDSA private key and its public key, bound to one signing
/// algorithm; held in the module, which wipes it on drop.
pub struct KeyPair {
    handle: Handle<EcdsaHandle>,
    public: PublicKey,
}

impl KeyPair {
    fn load(
        algorithm: &'static SigningAlgorithm,
        load_with: impl FnOnce(*mut *mut EcdsaHandle) -> Status,
    ) -> Result<Self, Error> {
        let handle = load(load_with)?;
        // SAFETY: the handle is live.
        let public = unsafe { rind_fips_ecdsa_public_key(handle.ptr()) };
        Ok(Self {
            handle,
            public: PublicKey {
                key: Key::from_handle(public),
                algorithm: algorithm.ecdsa,
            },
        })
    }

    /// Generates a key pair for `algorithm` from the module's random
    /// generator, then checks that it signs what its public key verifies.
    pub fn generate(algorithm: &'static SigningAlgorithm) -> Result<Self, Error> {
        // SAFETY: `out` is writable.
        Self::load(algorithm, |out| unsafe {
            rind_fips_ecdsa_generate(algorithm.id, out)
        })
    }

    /// Loads a PKCS#8 v1 `ECPrivateKey` on `algorithm`'s curve.
    pub fn from_pkcs8(algorithm: &'static SigningAlgorithm, der: &[u8]) -> Result<Self, Error> {
        Self::load(algorithm, |out| {
            // SAFETY: `der` is readable, and `out` writable.
            unsafe { rind_fips_ecdsa_from_pkcs8(algorithm.id, der.as_ptr(), der.len(), out) }
        })
    }

    /// Loads a SEC1 (RFC 5915) `ECPrivateKey` on `algorithm`'s curve.
    ///
    /// This refuses PKCS#8, which [`Self::from_pkcs8`] takes: a caller always
    /// knows which of the two it holds.
    pub fn from_sec1(algorithm: &'static SigningAlgorithm, der: &[u8]) -> Result<Self, Error> {
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
        algorithm: &'static SigningAlgorithm,
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
    pub fn public_key(&self) -> &PublicKey {
        &self.public
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
    pub fn to_scalar(&self) -> Scalar {
        // SAFETY: the handle is live.
        Scalar(Encoded::new(unsafe {
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
}

impl fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair")
            .field("algorithm", &self.public.algorithm)
            .field("public_key", &self.public.as_ref())
            .finish_non_exhaustive()
    }
}

const fn ecdsa(curve: CurveId, hash: HashId, encoding: EcdsaEncoding) -> Ecdsa {
    Ecdsa {
        curve,
        hash,
        encoding,
    }
}

/// Algorithms a key pair signs with.
pub(crate) mod sign {
    use super::{CurveId, EcdsaEncoding, HashId, SigningAlgorithm, ecdsa};
    use crate::ffi::ids::signature as id;

    const fn signing(
        id: u32,
        curve: CurveId,
        hash: HashId,
        encoding: EcdsaEncoding,
    ) -> SigningAlgorithm {
        SigningAlgorithm {
            id,
            ecdsa: ecdsa(curve, hash, encoding),
        }
    }

    /// ECDSA on P-256 with SHA-256, ASN.1 signatures.
    pub static P256_SHA256_ASN1: SigningAlgorithm = signing(
        id::ECDSA_P256_SHA256_ASN1,
        CurveId::P256,
        HashId::Sha256,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-384 with SHA-384, ASN.1 signatures.
    pub static P384_SHA384_ASN1: SigningAlgorithm = signing(
        id::ECDSA_P384_SHA384_ASN1,
        CurveId::P384,
        HashId::Sha384,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-521 with SHA-512, ASN.1 signatures.
    pub static P521_SHA512_ASN1: SigningAlgorithm = signing(
        id::ECDSA_P521_SHA512_ASN1,
        CurveId::P521,
        HashId::Sha512,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-256 with SHA-256, fixed-length `r || s` signatures (JWS's ES256).
    pub static P256_SHA256_FIXED: SigningAlgorithm = signing(
        id::ECDSA_P256_SHA256_FIXED,
        CurveId::P256,
        HashId::Sha256,
        EcdsaEncoding::Fixed,
    );

    /// ECDSA on P-384 with SHA-384, fixed-length `r || s` signatures (JWS's ES384).
    pub static P384_SHA384_FIXED: SigningAlgorithm = signing(
        id::ECDSA_P384_SHA384_FIXED,
        CurveId::P384,
        HashId::Sha384,
        EcdsaEncoding::Fixed,
    );

    /// ECDSA on P-521 with SHA-512, fixed-length `r || s` signatures (JWS's ES512).
    pub static P521_SHA512_FIXED: SigningAlgorithm = signing(
        id::ECDSA_P521_SHA512_FIXED,
        CurveId::P521,
        HashId::Sha512,
        EcdsaEncoding::Fixed,
    );
}

/// Algorithms a public key verifies with.
pub(crate) mod verify {
    use super::{CurveId, EcdsaEncoding, HashId, VerificationAlgorithm, ecdsa};
    use crate::ffi::ids::signature as id;

    const fn verification(
        id: u32,
        curve: CurveId,
        hash: HashId,
        encoding: EcdsaEncoding,
    ) -> VerificationAlgorithm {
        VerificationAlgorithm {
            id,
            ecdsa: ecdsa(curve, hash, encoding),
        }
    }

    /// ECDSA on P-256 with SHA-256, ASN.1 signatures.
    pub static P256_SHA256_ASN1: VerificationAlgorithm = verification(
        id::ECDSA_P256_SHA256_ASN1,
        CurveId::P256,
        HashId::Sha256,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-256 with SHA-384, ASN.1 signatures.
    pub static P256_SHA384_ASN1: VerificationAlgorithm = verification(
        id::ECDSA_P256_SHA384_ASN1,
        CurveId::P256,
        HashId::Sha384,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-256 with SHA-512, ASN.1 signatures.
    pub static P256_SHA512_ASN1: VerificationAlgorithm = verification(
        id::ECDSA_P256_SHA512_ASN1,
        CurveId::P256,
        HashId::Sha512,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-384 with SHA-256, ASN.1 signatures.
    pub static P384_SHA256_ASN1: VerificationAlgorithm = verification(
        id::ECDSA_P384_SHA256_ASN1,
        CurveId::P384,
        HashId::Sha256,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-384 with SHA-384, ASN.1 signatures.
    pub static P384_SHA384_ASN1: VerificationAlgorithm = verification(
        id::ECDSA_P384_SHA384_ASN1,
        CurveId::P384,
        HashId::Sha384,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-384 with SHA-512, ASN.1 signatures.
    pub static P384_SHA512_ASN1: VerificationAlgorithm = verification(
        id::ECDSA_P384_SHA512_ASN1,
        CurveId::P384,
        HashId::Sha512,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-521 with SHA-256, ASN.1 signatures.
    pub static P521_SHA256_ASN1: VerificationAlgorithm = verification(
        id::ECDSA_P521_SHA256_ASN1,
        CurveId::P521,
        HashId::Sha256,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-521 with SHA-384, ASN.1 signatures.
    pub static P521_SHA384_ASN1: VerificationAlgorithm = verification(
        id::ECDSA_P521_SHA384_ASN1,
        CurveId::P521,
        HashId::Sha384,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-521 with SHA-512, ASN.1 signatures.
    pub static P521_SHA512_ASN1: VerificationAlgorithm = verification(
        id::ECDSA_P521_SHA512_ASN1,
        CurveId::P521,
        HashId::Sha512,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-256 with SHA-256, fixed-length `r || s` signatures (JWS's ES256).
    pub static P256_SHA256_FIXED: VerificationAlgorithm = verification(
        id::ECDSA_P256_SHA256_FIXED,
        CurveId::P256,
        HashId::Sha256,
        EcdsaEncoding::Fixed,
    );

    /// ECDSA on P-384 with SHA-384, fixed-length `r || s` signatures (JWS's ES384).
    pub static P384_SHA384_FIXED: VerificationAlgorithm = verification(
        id::ECDSA_P384_SHA384_FIXED,
        CurveId::P384,
        HashId::Sha384,
        EcdsaEncoding::Fixed,
    );

    /// ECDSA on P-521 with SHA-512, fixed-length `r || s` signatures (JWS's ES512).
    pub static P521_SHA512_FIXED: VerificationAlgorithm = verification(
        id::ECDSA_P521_SHA512_FIXED,
        CurveId::P521,
        HashId::Sha512,
        EcdsaEncoding::Fixed,
    );
}
