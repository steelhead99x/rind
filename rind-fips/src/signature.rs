// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::digest::Digest;
use crate::encoding::{Encoded, Spki};
use crate::ffi::{self, Handle, Status, ids, opaque};
use crate::{Error, encoding};

mod ecdsa;
mod ed25519;
mod ml_dsa;
pub(crate) mod rsa;

pub use ecdsa::{EcdsaKeyPair, EcdsaScalar, EcdsaSigningAlgorithm};
pub use ed25519::{Ed25519KeyPair, Ed25519Seed};
use rsa::{PublicKeyComponents, Rsa};
pub use rsa::{RsaKeyPair, RsaSigningAlgorithm, RsaVerificationAlgorithm};

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
    fn rind_fips_public_key_from_components(
        id: u32,
        n: *const u8,
        n_len: usize,
        e: *const u8,
        e_len: usize,
        out: *mut *mut PublicKeyHandle,
    ) -> Status;
    fn rind_fips_public_key_bytes(key: *const PublicKeyHandle, len: *mut usize) -> *const u8;
    fn rind_fips_public_key_to_spki(key: *const PublicKeyHandle) -> *mut ffi::Encoded;
    fn rind_fips_public_key_verify(
        key: *const PublicKeyHandle,
        message: *const u8,
        len: usize,
        signature: *const u8,
        signature_len: usize,
    ) -> Status;
    fn rind_fips_public_key_verify_digest(
        key: *const PublicKeyHandle,
        hash: u32,
        value: *const u8,
        len: usize,
        signature: *const u8,
        signature_len: usize,
    ) -> Status;
}

// What the algorithms are, as rind's `Debug` shows them.

/// The hash a signature algorithm applies to the message.
#[derive(Clone, Copy, Debug, PartialEq)]
enum HashId {
    Sha256,
    Sha384,
    Sha512,
}

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

/// What a verification algorithm verifies.
#[derive(Clone, Copy)]
enum Verification {
    Ecdsa(Ecdsa),
    Rsa(Rsa),
    Ed25519,
    /// An ML-DSA parameter set, by name.
    MlDsa(&'static str),
}

impl fmt::Debug for Verification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ecdsa(ecdsa) => f.debug_tuple("Ecdsa").field(ecdsa).finish(),
            Self::Rsa(rsa) => f.debug_tuple("Rsa").field(rsa).finish(),
            Self::Ed25519 => f.write_str("Ed25519"),
            Self::MlDsa(name) => f.write_str(name),
        }
    }
}

/// A signature verification algorithm, which a [`PublicKey`] is bound to.
pub struct VerificationAlgorithm {
    id: u32,
    verification: Verification,
}

impl fmt::Debug for VerificationAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.verification.fmt(f)
    }
}

impl AsRef<Self> for VerificationAlgorithm {
    fn as_ref(&self) -> &Self {
        self
    }
}

/// A public key, bound to the one algorithm it verifies signatures with.
///
/// Its bytes are its encoding, as [`PublicKey::new`] takes it, but an RSA
/// key's are always its PKCS#1 `RSAPublicKey` DER.
pub struct PublicKey {
    handle: Handle<PublicKeyHandle>,
    verification: Verification,
}

impl PublicKey {
    /// Takes ownership of a key the module made, which verifies as
    /// `verification`.
    fn from_handle(handle: *mut PublicKeyHandle, verification: Verification) -> Self {
        Self {
            handle: Handle::new(handle),
            verification,
        }
    }

    /// Runs `parse`, which writes a key verifying as `algorithm` to its
    /// argument and returns its status.
    fn parse(
        algorithm: &VerificationAlgorithm,
        parse: impl FnOnce(*mut *mut PublicKeyHandle) -> Status,
    ) -> Result<Self, Error> {
        let mut out = core::ptr::null_mut();
        let handle = Handle::from_status(parse(&mut out), out)?;
        Ok(Self {
            handle,
            verification: algorithm.verification,
        })
    }

    /// Parses a public key for `algorithm`, any `verify` constant,
    /// refusing a malformed key before any signature arrives.
    ///
    /// ECDSA keys are X9.62 uncompressed points, RSA keys are PKCS#1
    /// `RSAPublicKey` or `SubjectPublicKeyInfo` DER, Ed25519 keys are their
    /// 32 bytes, and ML-DSA keys are FIPS 204's encoding. A compressed ECDSA
    /// point is refused. So is an Ed25519 point of small order, which
    /// verifies signatures nobody made, and an RSA modulus FIPS 186-5 does
    /// not approve: one of an odd number of bits, or under 2048 bits but
    /// for the `legacy` algorithms' 1024.
    pub fn new(algorithm: &impl AsRef<VerificationAlgorithm>, bytes: &[u8]) -> Result<Self, Error> {
        let algorithm = algorithm.as_ref();
        Self::parse(algorithm, |out| {
            // SAFETY: `bytes` is readable, and `out` writable.
            unsafe { rind_fips_public_key_new(algorithm.id, bytes.as_ptr(), bytes.len(), out) }
        })
    }

    /// Loads an RSA key for `algorithm` from its big-endian modulus and
    /// exponent, as a JWK carries them.
    pub fn from_components(
        algorithm: &RsaVerificationAlgorithm,
        components: &PublicKeyComponents<impl AsRef<[u8]>>,
    ) -> Result<Self, Error> {
        let algorithm = algorithm.as_ref();
        let (n, e) = (components.n.as_ref(), components.e.as_ref());
        Self::parse(algorithm, |out| {
            // SAFETY: `n` and `e` are readable, and `out` writable.
            unsafe {
                rind_fips_public_key_from_components(
                    algorithm.id,
                    n.as_ptr(),
                    n.len(),
                    e.as_ptr(),
                    e.len(),
                    out,
                )
            }
        })
    }

    /// Parses a public key for `algorithm` from its `SubjectPublicKeyInfo`
    /// DER, refusing one that names another algorithm or curve.
    ///
    /// An ECDSA key names `id-ecPublicKey` and the algorithm's curve, and
    /// its point may be compressed (RFC 5480), which this decompresses. An
    /// RSA key names `rsaEncryption`, `id-RSAES-OAEP`, or `id-ea-rsa`, an
    /// Ed25519 key `id-Ed25519`, and an ML-DSA key its parameter set's OID
    /// (RFC 9881).
    pub fn from_spki(
        algorithm: &impl AsRef<VerificationAlgorithm>,
        der: &[u8],
    ) -> Result<Self, Error> {
        let algorithm = algorithm.as_ref();
        Self::parse(algorithm, |out| {
            // SAFETY: `der` is readable, and `out` writable.
            unsafe { rind_fips_public_key_from_spki(algorithm.id, der.as_ptr(), der.len(), out) }
        })
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`: ECDSA's
    /// `id-ecPublicKey` on its curve, with its uncompressed point, RSA's
    /// `rsaEncryption`, Ed25519's `id-Ed25519`, or ML-DSA's parameter set.
    pub fn to_spki(&self) -> Spki {
        // SAFETY: the handle is live.
        Spki::from(Encoded::new(unsafe {
            rind_fips_public_key_to_spki(self.handle.ptr())
        }))
    }

    /// Verifies `signature` over `message`, refusing a malformed signature.
    ///
    /// ECDSA signatures are malleable: `(r, s)` and `(r, n - s)` both verify,
    /// unlike Ed25519, PKCS#1, and PSS signatures, so don't identify a message
    /// by its ECDSA signature's bytes.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        // SAFETY: the handle is live, and `message` and `signature`
        // readable.
        ffi::check(unsafe {
            rind_fips_public_key_verify(
                self.handle.ptr(),
                message.as_ptr(),
                message.len(),
                signature.as_ptr(),
                signature.len(),
            )
        })
    }

    /// Verifies an ECDSA `signature` over the message `digest` hashes.
    ///
    /// The digest's hash, SHA-256, SHA-384, or SHA-512, replaces the
    /// algorithm's, which still fixes the curve and the signature's encoding.
    /// Another hash, or a key other than ECDSA, is refused as
    /// [`Error::Unsupported`].
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
                self.handle.ptr(),
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
        let mut len = 0;
        // SAFETY: the handle is live, and its bytes live as long as it,
        // which `&self` borrows.
        unsafe {
            core::slice::from_raw_parts(
                rind_fips_public_key_bytes(self.handle.ptr(), &mut len),
                len,
            )
        }
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_struct("PublicKey");
        match &self.verification {
            Verification::Ecdsa(ecdsa) => f.field("algorithm", ecdsa),
            Verification::Rsa(rsa) => f.field("algorithm", &rsa.verification),
            Verification::Ed25519 => f.field("algorithm", &format_args!("Ed25519")),
            Verification::MlDsa(name) => f.field("algorithm", &format_args!("{name}")),
        };
        f.field("bytes", &self.as_ref()).finish()
    }
}

/// A signature from any key pair.
#[derive(Clone, Copy)]
pub struct Signature {
    bytes: [u8; SIGNATURE_MAX_LEN],
    len: usize,
}

/// RSA's, as long as the largest modulus the module takes, 8192 bits, is
/// longer than any ECDSA signature.
const SIGNATURE_MAX_LEN: usize = 1024;

impl Signature {
    /// Runs `sign`, which writes a signature to the buffer it is given,
    /// with its capacity, and the signature's length to its last argument,
    /// returning its status.
    fn write(sign: impl FnOnce(*mut u8, usize, *mut usize) -> Status) -> Result<Self, Error> {
        let mut signature = Self {
            bytes: [0; SIGNATURE_MAX_LEN],
            len: 0,
        };
        ffi::check(sign(
            signature.bytes.as_mut_ptr(),
            SIGNATURE_MAX_LEN,
            &mut signature.len,
        ))?;
        Ok(signature)
    }
}

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Signature").field(&self.as_ref()).finish()
    }
}

/// Algorithms a key pair signs with, and ML-DSA's key pair, whose
/// parameter set is a type.
///
/// Each signs as the [`verify`] algorithm of the same name verifies:
/// [`MlDsaKeyPair<MlDsa65>`] as [`verify::ML_DSA_65`].
///
/// RSA signs with moduli of an even number of bits from 2048 to 8192,
/// and RSA-PSS with a salt as long as its hash, the length aws-lc's
/// module approves: there is no `RsaPssSaltLength`.
///
/// ```
/// use rind_fips::signature::sign::{MlDsa65, MlDsaKeyPair};
/// use rind_fips::signature::{PublicKey, verify};
///
/// let key = MlDsaKeyPair::<MlDsa65>::generate().unwrap();
/// let signature = key.sign(b"hello").unwrap();
///
/// let public_key = PublicKey::new(&verify::ML_DSA_65, key.public_key().as_ref()).unwrap();
/// public_key.verify(b"hello", signature.as_ref()).unwrap();
/// ```
pub mod sign {
    use ids::signature as id;

    pub use super::ml_dsa::{
        MlDsa44, MlDsa65, MlDsa87, MlDsaKeyPair, MlDsaParameterSet, MlDsaSeed, MlDsaSignature,
    };
    use super::rsa::RsaScheme;
    use super::{CurveId, EcdsaEncoding, EcdsaSigningAlgorithm, HashId, RsaSigningAlgorithm, ids};

    /// ECDSA on P-256 with SHA-256, ASN.1 signatures.
    pub static ECDSA_P256_SHA256_ASN1: EcdsaSigningAlgorithm = EcdsaSigningAlgorithm::new(
        id::ECDSA_P256_SHA256_ASN1,
        CurveId::P256,
        HashId::Sha256,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-384 with SHA-384, ASN.1 signatures.
    pub static ECDSA_P384_SHA384_ASN1: EcdsaSigningAlgorithm = EcdsaSigningAlgorithm::new(
        id::ECDSA_P384_SHA384_ASN1,
        CurveId::P384,
        HashId::Sha384,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-521 with SHA-512, ASN.1 signatures.
    pub static ECDSA_P521_SHA512_ASN1: EcdsaSigningAlgorithm = EcdsaSigningAlgorithm::new(
        id::ECDSA_P521_SHA512_ASN1,
        CurveId::P521,
        HashId::Sha512,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-256 with SHA-256, fixed-length `r || s` signatures (JWS's ES256).
    pub static ECDSA_P256_SHA256_FIXED: EcdsaSigningAlgorithm = EcdsaSigningAlgorithm::new(
        id::ECDSA_P256_SHA256_FIXED,
        CurveId::P256,
        HashId::Sha256,
        EcdsaEncoding::Fixed,
    );

    /// ECDSA on P-384 with SHA-384, fixed-length `r || s` signatures (JWS's ES384).
    pub static ECDSA_P384_SHA384_FIXED: EcdsaSigningAlgorithm = EcdsaSigningAlgorithm::new(
        id::ECDSA_P384_SHA384_FIXED,
        CurveId::P384,
        HashId::Sha384,
        EcdsaEncoding::Fixed,
    );

    /// ECDSA on P-521 with SHA-512, fixed-length `r || s` signatures (JWS's ES512).
    pub static ECDSA_P521_SHA512_FIXED: EcdsaSigningAlgorithm = EcdsaSigningAlgorithm::new(
        id::ECDSA_P521_SHA512_FIXED,
        CurveId::P521,
        HashId::Sha512,
        EcdsaEncoding::Fixed,
    );

    /// RSASSA-PKCS1-v1_5 with SHA-256.
    pub static RSA_PKCS1_SHA256: RsaSigningAlgorithm =
        RsaSigningAlgorithm::new(id::RSA_PKCS1_SHA256, RsaScheme::pkcs1(HashId::Sha256));

    /// RSASSA-PKCS1-v1_5 with SHA-384.
    pub static RSA_PKCS1_SHA384: RsaSigningAlgorithm =
        RsaSigningAlgorithm::new(id::RSA_PKCS1_SHA384, RsaScheme::pkcs1(HashId::Sha384));

    /// RSASSA-PKCS1-v1_5 with SHA-512.
    pub static RSA_PKCS1_SHA512: RsaSigningAlgorithm =
        RsaSigningAlgorithm::new(id::RSA_PKCS1_SHA512, RsaScheme::pkcs1(HashId::Sha512));

    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a 32-byte salt.
    pub static RSA_PSS_SHA256: RsaSigningAlgorithm =
        RsaSigningAlgorithm::new(id::RSA_PSS_SHA256, RsaScheme::pss(HashId::Sha256));

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a 48-byte salt.
    pub static RSA_PSS_SHA384: RsaSigningAlgorithm =
        RsaSigningAlgorithm::new(id::RSA_PSS_SHA384, RsaScheme::pss(HashId::Sha384));

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a 64-byte salt.
    pub static RSA_PSS_SHA512: RsaSigningAlgorithm =
        RsaSigningAlgorithm::new(id::RSA_PSS_SHA512, RsaScheme::pss(HashId::Sha512));
}

/// Algorithms a public key verifies with.
///
/// RSA algorithms accept moduli of an even number of bits from 2048 to
/// 8192. RSA-PSS takes only a salt as long as its hash: there is no
/// `RSA_PSS_*_ANY_SALT`.
pub mod verify {
    use ids::signature as id;

    use super::rsa::RsaScheme;
    use super::{
        CurveId, EcdsaEncoding, HashId, RsaVerificationAlgorithm, Verification,
        VerificationAlgorithm, ids,
    };

    const fn ecdsa(
        id: u32,
        curve: CurveId,
        hash: HashId,
        encoding: EcdsaEncoding,
    ) -> VerificationAlgorithm {
        VerificationAlgorithm {
            id,
            verification: Verification::Ecdsa(super::Ecdsa {
                curve,
                hash,
                encoding,
            }),
        }
    }

    /// ECDSA on P-256 with SHA-256, ASN.1 signatures.
    pub static ECDSA_P256_SHA256_ASN1: VerificationAlgorithm = ecdsa(
        id::ECDSA_P256_SHA256_ASN1,
        CurveId::P256,
        HashId::Sha256,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-256 with SHA-384, ASN.1 signatures.
    pub static ECDSA_P256_SHA384_ASN1: VerificationAlgorithm = ecdsa(
        id::ECDSA_P256_SHA384_ASN1,
        CurveId::P256,
        HashId::Sha384,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-256 with SHA-512, ASN.1 signatures.
    pub static ECDSA_P256_SHA512_ASN1: VerificationAlgorithm = ecdsa(
        id::ECDSA_P256_SHA512_ASN1,
        CurveId::P256,
        HashId::Sha512,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-384 with SHA-256, ASN.1 signatures.
    pub static ECDSA_P384_SHA256_ASN1: VerificationAlgorithm = ecdsa(
        id::ECDSA_P384_SHA256_ASN1,
        CurveId::P384,
        HashId::Sha256,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-384 with SHA-384, ASN.1 signatures.
    pub static ECDSA_P384_SHA384_ASN1: VerificationAlgorithm = ecdsa(
        id::ECDSA_P384_SHA384_ASN1,
        CurveId::P384,
        HashId::Sha384,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-384 with SHA-512, ASN.1 signatures.
    pub static ECDSA_P384_SHA512_ASN1: VerificationAlgorithm = ecdsa(
        id::ECDSA_P384_SHA512_ASN1,
        CurveId::P384,
        HashId::Sha512,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-521 with SHA-256, ASN.1 signatures.
    pub static ECDSA_P521_SHA256_ASN1: VerificationAlgorithm = ecdsa(
        id::ECDSA_P521_SHA256_ASN1,
        CurveId::P521,
        HashId::Sha256,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-521 with SHA-384, ASN.1 signatures.
    pub static ECDSA_P521_SHA384_ASN1: VerificationAlgorithm = ecdsa(
        id::ECDSA_P521_SHA384_ASN1,
        CurveId::P521,
        HashId::Sha384,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-521 with SHA-512, ASN.1 signatures.
    pub static ECDSA_P521_SHA512_ASN1: VerificationAlgorithm = ecdsa(
        id::ECDSA_P521_SHA512_ASN1,
        CurveId::P521,
        HashId::Sha512,
        EcdsaEncoding::Asn1,
    );

    /// ECDSA on P-256 with SHA-256, fixed-length `r || s` signatures (JWS's ES256).
    pub static ECDSA_P256_SHA256_FIXED: VerificationAlgorithm = ecdsa(
        id::ECDSA_P256_SHA256_FIXED,
        CurveId::P256,
        HashId::Sha256,
        EcdsaEncoding::Fixed,
    );

    /// ECDSA on P-384 with SHA-384, fixed-length `r || s` signatures (JWS's ES384).
    pub static ECDSA_P384_SHA384_FIXED: VerificationAlgorithm = ecdsa(
        id::ECDSA_P384_SHA384_FIXED,
        CurveId::P384,
        HashId::Sha384,
        EcdsaEncoding::Fixed,
    );

    /// ECDSA on P-521 with SHA-512, fixed-length `r || s` signatures (JWS's ES512).
    pub static ECDSA_P521_SHA512_FIXED: VerificationAlgorithm = ecdsa(
        id::ECDSA_P521_SHA512_FIXED,
        CurveId::P521,
        HashId::Sha512,
        EcdsaEncoding::Fixed,
    );

    /// RSASSA-PKCS1-v1_5 with SHA-256, for moduli of 2048 to 8192 bits.
    pub static RSA_PKCS1_SHA256: RsaVerificationAlgorithm = RsaVerificationAlgorithm::scheme(
        id::RSA_PKCS1_SHA256,
        RsaScheme::pkcs1(HashId::Sha256),
        2048,
    );

    /// RSASSA-PKCS1-v1_5 with SHA-384, for moduli of 2048 to 8192 bits.
    pub static RSA_PKCS1_SHA384: RsaVerificationAlgorithm = RsaVerificationAlgorithm::scheme(
        id::RSA_PKCS1_SHA384,
        RsaScheme::pkcs1(HashId::Sha384),
        2048,
    );

    /// RSASSA-PKCS1-v1_5 with SHA-512, for moduli of 2048 to 8192 bits.
    pub static RSA_PKCS1_SHA512: RsaVerificationAlgorithm = RsaVerificationAlgorithm::scheme(
        id::RSA_PKCS1_SHA512,
        RsaScheme::pkcs1(HashId::Sha512),
        2048,
    );

    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a 32-byte salt, for moduli of 2048 to 8192 bits.
    pub static RSA_PSS_SHA256: RsaVerificationAlgorithm =
        RsaVerificationAlgorithm::scheme(id::RSA_PSS_SHA256, RsaScheme::pss(HashId::Sha256), 2048);

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a 48-byte salt, for moduli of 2048 to 8192 bits.
    pub static RSA_PSS_SHA384: RsaVerificationAlgorithm =
        RsaVerificationAlgorithm::scheme(id::RSA_PSS_SHA384, RsaScheme::pss(HashId::Sha384), 2048);

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a 64-byte salt, for moduli of 2048 to 8192 bits.
    pub static RSA_PSS_SHA512: RsaVerificationAlgorithm =
        RsaVerificationAlgorithm::scheme(id::RSA_PSS_SHA512, RsaScheme::pss(HashId::Sha512), 2048);

    /// Ed25519, with 32-byte public keys and 64-byte signatures.
    ///
    /// See [RFC8032](https://datatracker.ietf.org/doc/html/rfc8032).
    pub static ED25519: VerificationAlgorithm = VerificationAlgorithm {
        id: id::ED25519,
        verification: Verification::Ed25519,
    };

    /// ML-DSA-44 (FIPS 204), pure with the empty context: 1312-byte public
    /// keys and 2420-byte signatures.
    pub static ML_DSA_44: VerificationAlgorithm = VerificationAlgorithm {
        id: id::ML_DSA_44,
        verification: Verification::MlDsa("ML-DSA-44"),
    };

    /// ML-DSA-65 (FIPS 204), pure with the empty context: 1952-byte public
    /// keys and 3309-byte signatures.
    pub static ML_DSA_65: VerificationAlgorithm = VerificationAlgorithm {
        id: id::ML_DSA_65,
        verification: Verification::MlDsa("ML-DSA-65"),
    };

    /// ML-DSA-87 (FIPS 204), pure with the empty context: 2592-byte public
    /// keys and 4627-byte signatures.
    pub static ML_DSA_87: VerificationAlgorithm = VerificationAlgorithm {
        id: id::ML_DSA_87,
        verification: Verification::MlDsa("ML-DSA-87"),
    };

    /// RSA algorithms with another modulus floor, or SHA-1, for old keys
    /// and signatures, as SP 800-131A approves them for verifying only: a
    /// 1024-bit modulus, but none between it and 2048 bits.
    pub mod legacy {
        use super::super::rsa::RsaScheme;
        use super::{HashId, RsaVerificationAlgorithm, id};

        /// RSASSA-PKCS1-v1_5 with SHA-1, for old signatures only: SHA-1 collisions are practical.
        pub static RSA_PKCS1_SHA1: RsaVerificationAlgorithm =
            RsaVerificationAlgorithm::sha1(id::RSA_PKCS1_SHA1, 2048);

        /// RSASSA-PKCS1-v1_5 with SHA-1, for old signatures by keys with 1024-bit moduli too.
        pub static RSA_PKCS1_1024_SHA1: RsaVerificationAlgorithm =
            RsaVerificationAlgorithm::sha1(id::RSA_PKCS1_1024_SHA1, 1024);

        /// RSASSA-PKCS1-v1_5 with SHA-256, for old keys with 1024-bit moduli too.
        pub static RSA_PKCS1_1024_SHA256: RsaVerificationAlgorithm =
            RsaVerificationAlgorithm::scheme(
                id::RSA_PKCS1_1024_SHA256,
                RsaScheme::pkcs1(HashId::Sha256),
                1024,
            );

        /// RSASSA-PKCS1-v1_5 with SHA-512, for old keys with 1024-bit moduli too.
        pub static RSA_PKCS1_1024_SHA512: RsaVerificationAlgorithm =
            RsaVerificationAlgorithm::scheme(
                id::RSA_PKCS1_1024_SHA512,
                RsaScheme::pkcs1(HashId::Sha512),
                1024,
            );

        /// RSASSA-PKCS1-v1_5 with SHA-384, for moduli of 3072 to 8192 bits.
        pub static RSA_PKCS1_3072_SHA384: RsaVerificationAlgorithm =
            RsaVerificationAlgorithm::scheme(
                id::RSA_PKCS1_3072_SHA384,
                RsaScheme::pkcs1(HashId::Sha384),
                3072,
            );
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
