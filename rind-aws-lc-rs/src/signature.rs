//! Public key signatures: ECDSA on P-256, P-384, and P-521, RSA, Ed25519,
//! and ML-DSA.
//!
//! Calls that take a [`rand::SecureRandom`] to sign draw from the system
//! random source inside rind, which `rng`, the only `SecureRandom`, also is.

use alloc::boxed::Box;
use alloc::sync::Arc;
use core::any::Any;
use core::fmt;
use core::marker::PhantomData;
use core::ops::Deref;

use crate::digest::{self, Digest};
use crate::encoding::{
    AsBigEndian, AsDer, Curve25519SeedBin, EcPrivateKeyBin, EcPrivateKeyRfc5915Der,
    EcPublicKeyCompressedBin, EcPublicKeyUncompressedBin, Pkcs8V1Der, Pkcs8V2Der, PublicKeyX509Der,
};
use crate::error::{KeyRejected, Unspecified, unspecified};
pub use crate::rsa::signing::{
    RSA_PKCS1_SHA256, RSA_PKCS1_SHA384, RSA_PKCS1_SHA512, RSA_PSS_SHA256, RSA_PSS_SHA384,
    RSA_PSS_SHA512, RsaEncoding, RsaSignatureEncoding,
};
pub use crate::rsa::verification::{
    RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY, RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY,
    RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY, RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY,
    RSA_PKCS1_2048_8192_SHA256, RSA_PKCS1_2048_8192_SHA384, RSA_PKCS1_2048_8192_SHA512,
    RSA_PKCS1_3072_8192_SHA384, RSA_PSS_2048_8192_SHA256, RSA_PSS_2048_8192_SHA384,
    RSA_PSS_2048_8192_SHA512,
};
pub use crate::rsa::{
    KeyPair as RsaKeyPair, PublicKey as RsaSubjectPublicKey,
    PublicKeyComponents as RsaPublicKeyComponents, RsaParameters, RsaPssSaltLength,
};
use crate::wipe::Wiped;
use crate::{pkcs8, rand, sealed};

/// A signature.
#[derive(Clone, Copy)]
pub struct Signature(rind::signature::Signature);

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

/// A key pair, whose public key verifies what it signs.
pub trait KeyPair: fmt::Debug + Send + Sized + Sync {
    /// The public key's type.
    type PublicKey: AsRef<[u8]> + fmt::Debug + Clone + Send + Sized + Sync;

    /// The public key.
    fn public_key(&self) -> &Self::PublicKey;
}

pub(crate) mod private {
    use crate::digest::Digest;
    use crate::error::{KeyRejected, Unspecified};

    /// How a verification algorithm parses keys and verifies with rind,
    /// which only rind-aws-lc-rs can name.
    pub trait Verify {
        /// Parses an encoded public key.
        fn parse(&self, public_key: &[u8]) -> Result<rind::signature::PublicKey, KeyRejected>;

        /// Parses an encoded public key to keep, also returning whether it
        /// can verify for this algorithm. aws-lc-rs keeps an RSA key outside
        /// the algorithm's range and fails its verifications.
        fn parse_kept(
            &self,
            public_key: &[u8],
        ) -> Result<(rind::signature::PublicKey, bool), KeyRejected> {
            self.parse(public_key).map(|key| (key, true))
        }

        /// Verifies `signature` over `msg`.
        fn verify_parsed(
            &self,
            key: &rind::signature::PublicKey,
            msg: &[u8],
            signature: &[u8],
        ) -> Result<(), Unspecified>;

        /// Verifies `signature` over the message `digest` hashes.
        fn verify_parsed_digest(
            &self,
            key: &rind::signature::PublicKey,
            digest: &Digest,
            signature: &[u8],
        ) -> Result<(), Unspecified>;
    }
}

/// A signature verification algorithm.
pub trait VerificationAlgorithm:
    fmt::Debug + Sync + Any + sealed::Sealed + private::Verify
{
    /// Verifies `signature` over `msg` with the encoded `public_key`.
    #[cfg(feature = "ring-sig-verify")]
    #[deprecated(
        since = "1.0.0",
        note = "please use `VerificationAlgorithm::verify_sig` instead"
    )]
    fn verify(
        &self,
        public_key: untrusted::Input<'_>,
        msg: untrusted::Input<'_>,
        signature: untrusted::Input<'_>,
    ) -> Result<(), Unspecified>;

    /// Verifies `signature` over `msg` with the encoded `public_key`.
    fn verify_sig(
        &self,
        public_key: &[u8],
        msg: &[u8],
        signature: &[u8],
    ) -> Result<(), Unspecified>;

    /// Verifies `signature` over the message `digest` hashes with the
    /// encoded `public_key`. Only ECDSA verifies over a digest.
    fn verify_digest_sig(
        &self,
        public_key: &[u8],
        digest: &Digest,
        signature: &[u8],
    ) -> Result<(), Unspecified>;
}

/// Implements [`VerificationAlgorithm`] through [`private::Verify`].
macro_rules! verification_algorithm {
    ($ty:ty) => {
        impl $crate::sealed::Sealed for $ty {}

        impl $crate::signature::VerificationAlgorithm for $ty {
            #[cfg(feature = "ring-sig-verify")]
            fn verify(
                &self,
                public_key: untrusted::Input<'_>,
                msg: untrusted::Input<'_>,
                signature: untrusted::Input<'_>,
            ) -> Result<(), $crate::error::Unspecified> {
                self.verify_sig(
                    public_key.as_slice_less_safe(),
                    msg.as_slice_less_safe(),
                    signature.as_slice_less_safe(),
                )
            }

            fn verify_sig(
                &self,
                public_key: &[u8],
                msg: &[u8],
                signature: &[u8],
            ) -> Result<(), $crate::error::Unspecified> {
                use $crate::signature::private::Verify;
                let key = self
                    .parse(public_key)
                    .map_err(|_| $crate::error::Unspecified)?;
                self.verify_parsed(&key, msg, signature)
            }

            fn verify_digest_sig(
                &self,
                public_key: &[u8],
                digest: &$crate::digest::Digest,
                signature: &[u8],
            ) -> Result<(), $crate::error::Unspecified> {
                use $crate::signature::private::Verify;
                let key = self
                    .parse(public_key)
                    .map_err(|_| $crate::error::Unspecified)?;
                self.verify_parsed_digest(&key, digest, signature)
            }
        }
    };
}
pub(crate) use verification_algorithm;

/// A peer's encoded public key, parsed only when it verifies.
#[derive(Clone)]
pub struct UnparsedPublicKey<B: AsRef<[u8]>> {
    algorithm: &'static dyn VerificationAlgorithm,
    bytes: B,
}

impl<B: Copy + AsRef<[u8]>> Copy for UnparsedPublicKey<B> {}

impl<B: AsRef<[u8]>> UnparsedPublicKey<B> {
    /// Wraps the encoded key for `algorithm`.
    pub fn new(algorithm: &'static dyn VerificationAlgorithm, bytes: B) -> Self {
        Self { algorithm, bytes }
    }

    /// Verifies `signature` over `message`.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Unspecified> {
        self.algorithm
            .verify_sig(self.bytes.as_ref(), message, signature)
    }

    /// Verifies `signature` over the message `digest` hashes.
    pub fn verify_digest(&self, digest: &Digest, signature: &[u8]) -> Result<(), Unspecified> {
        self.algorithm
            .verify_digest_sig(self.bytes.as_ref(), digest, signature)
    }

    /// Parses the key, to verify many signatures.
    pub fn parse(&self) -> Result<ParsedPublicKey, KeyRejected> {
        ParsedPublicKey::new(self.algorithm, self.bytes.as_ref())
    }
}

impl<B: AsRef<[u8]>> AsRef<[u8]> for UnparsedPublicKey<B> {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl<B: AsRef<[u8]>> fmt::Debug for UnparsedPublicKey<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "UnparsedPublicKey {{ algorithm: {:?}, bytes: ",
            self.algorithm
        )?;
        fmt::Debug::fmt(&crate::Hex(self.bytes.as_ref()), f)?;
        f.write_str(" }")
    }
}

/// A public key, parsed once to verify many signatures.
#[derive(Clone)]
pub struct ParsedPublicKey {
    algorithm: &'static dyn VerificationAlgorithm,
    key: Arc<rind::signature::PublicKey>,
    /// Whether `key` can verify for `algorithm`, false for an RSA key
    /// outside its range.
    verifies: bool,
    bytes: Box<[u8]>,
}

impl ParsedPublicKey {
    /// Parses `bytes` for `algorithm`.
    pub fn new<B: AsRef<[u8]>>(
        algorithm: &'static dyn VerificationAlgorithm,
        bytes: B,
    ) -> Result<Self, KeyRejected> {
        let (key, verifies) = algorithm.parse_kept(bytes.as_ref())?;
        Ok(Self::from_parts(algorithm, key, verifies, bytes.as_ref()))
    }

    pub(crate) fn from_parts(
        algorithm: &'static dyn VerificationAlgorithm,
        key: rind::signature::PublicKey,
        verifies: bool,
        bytes: &[u8],
    ) -> Self {
        Self {
            algorithm,
            key: Arc::new(key),
            verifies,
            bytes: bytes.into(),
        }
    }

    /// The key's algorithm.
    #[must_use]
    pub fn algorithm(&self) -> &'static dyn VerificationAlgorithm {
        self.algorithm
    }

    /// Verifies `signature` over `message`.
    pub fn verify_sig(&self, message: &[u8], signature: &[u8]) -> Result<(), Unspecified> {
        if !self.verifies {
            return Err(Unspecified);
        }
        self.algorithm.verify_parsed(&self.key, message, signature)
    }

    /// Verifies `signature` over the message `digest` hashes.
    pub fn verify_digest_sig(&self, digest: &Digest, signature: &[u8]) -> Result<(), Unspecified> {
        if !self.verifies {
            return Err(Unspecified);
        }
        self.algorithm
            .verify_parsed_digest(&self.key, digest, signature)
    }
}

impl AsDer<PublicKeyX509Der<'static>> for ParsedPublicKey {
    fn as_der(&self) -> Result<PublicKeyX509Der<'static>, Unspecified> {
        Ok(PublicKeyX509Der::new(self.key.to_spki().as_ref().to_vec()))
    }
}

impl AsRef<[u8]> for ParsedPublicKey {
    /// The bytes the key was parsed from.
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl fmt::Debug for ParsedPublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ParsedPublicKey {{ algorithm: {:?}, bytes: ",
            self.algorithm
        )?;
        fmt::Debug::fmt(&crate::Hex(&self.bytes), f)?;
        f.write_str(" }")
    }
}

#[allow(non_camel_case_types)]
#[derive(Debug, Eq, PartialEq)]
enum EcdsaCurve {
    ECDSA_P256,
    ECDSA_P384,
    ECDSA_P521,
}

#[derive(Debug, Eq, PartialEq)]
enum EcdsaSignatureFormat {
    ASN1,
    Fixed,
}

/// An ECDSA verification algorithm: a curve, a hash, and a signature
/// encoding.
///
/// It takes a public key as an X9.62 point, uncompressed or compressed, or
/// as a `SubjectPublicKeyInfo`, as aws-lc-rs does.
#[derive(Debug, Eq, PartialEq)]
pub struct EcdsaVerificationAlgorithm {
    id: EcdsaCurve,
    digest: &'static digest::Algorithm,
    sig_format: EcdsaSignatureFormat,
}

impl EcdsaVerificationAlgorithm {
    /// rind's algorithm with this curve and signature encoding, whose hash
    /// [`rind::signature::PublicKey::verify_digest`] replaces.
    fn rind(&self) -> &'static rind::signature::VerificationAlgorithm {
        use rind::signature::verify;
        match (&self.id, &self.sig_format) {
            (EcdsaCurve::ECDSA_P256, EcdsaSignatureFormat::ASN1) => &verify::ECDSA_P256_SHA256_ASN1,
            (EcdsaCurve::ECDSA_P256, EcdsaSignatureFormat::Fixed) => {
                &verify::ECDSA_P256_SHA256_FIXED
            }
            (EcdsaCurve::ECDSA_P384, EcdsaSignatureFormat::ASN1) => &verify::ECDSA_P384_SHA384_ASN1,
            (EcdsaCurve::ECDSA_P384, EcdsaSignatureFormat::Fixed) => {
                &verify::ECDSA_P384_SHA384_FIXED
            }
            (EcdsaCurve::ECDSA_P521, EcdsaSignatureFormat::ASN1) => &verify::ECDSA_P521_SHA512_ASN1,
            (EcdsaCurve::ECDSA_P521, EcdsaSignatureFormat::Fixed) => {
                &verify::ECDSA_P521_SHA512_FIXED
            }
        }
    }

    /// rind's signing algorithm with this curve and signature encoding,
    /// whose hash [`rind::signature::EcdsaKeyPair::sign_digest`] replaces.
    fn rind_signing(&self) -> &'static rind::signature::EcdsaSigningAlgorithm {
        use rind::signature::sign;
        match (&self.id, &self.sig_format) {
            (EcdsaCurve::ECDSA_P256, EcdsaSignatureFormat::ASN1) => &sign::ECDSA_P256_SHA256_ASN1,
            (EcdsaCurve::ECDSA_P256, EcdsaSignatureFormat::Fixed) => &sign::ECDSA_P256_SHA256_FIXED,
            (EcdsaCurve::ECDSA_P384, EcdsaSignatureFormat::ASN1) => &sign::ECDSA_P384_SHA384_ASN1,
            (EcdsaCurve::ECDSA_P384, EcdsaSignatureFormat::Fixed) => &sign::ECDSA_P384_SHA384_FIXED,
            (EcdsaCurve::ECDSA_P521, EcdsaSignatureFormat::ASN1) => &sign::ECDSA_P521_SHA512_ASN1,
            (EcdsaCurve::ECDSA_P521, EcdsaSignatureFormat::Fixed) => &sign::ECDSA_P521_SHA512_FIXED,
        }
    }

    /// ECDH on the same curve, whose parser decompresses a point.
    fn ecdh(&self) -> &'static rind::agreement::Algorithm {
        match self.id {
            EcdsaCurve::ECDSA_P256 => &rind::agreement::ECDH_P256,
            EcdsaCurve::ECDSA_P384 => &rind::agreement::ECDH_P384,
            EcdsaCurve::ECDSA_P521 => &rind::agreement::ECDH_P521,
        }
    }
}

impl private::Verify for EcdsaVerificationAlgorithm {
    fn parse(&self, public_key: &[u8]) -> Result<rind::signature::PublicKey, KeyRejected> {
        let algorithm = self.rind();
        if let Ok(key) = rind::signature::PublicKey::from_spki(algorithm, public_key) {
            return Ok(key);
        }
        match public_key.first() {
            Some(0x02 | 0x03) => {
                let point = rind::agreement::PublicKey::new(self.ecdh(), public_key)
                    .map_err(KeyRejected::rind)?;
                rind::signature::PublicKey::new(algorithm, point.as_ref())
            }
            _ => rind::signature::PublicKey::new(algorithm, public_key),
        }
        .map_err(KeyRejected::rind)
    }

    fn verify_parsed(
        &self,
        key: &rind::signature::PublicKey,
        msg: &[u8],
        signature: &[u8],
    ) -> Result<(), Unspecified> {
        let digest = rind::digest::digest(self.digest.rind(), msg);
        key.verify_digest(&digest, signature).map_err(unspecified)
    }

    fn verify_parsed_digest(
        &self,
        key: &rind::signature::PublicKey,
        digest: &Digest,
        signature: &[u8],
    ) -> Result<(), Unspecified> {
        if digest.algorithm() != self.digest {
            return Err(Unspecified);
        }
        key.verify_digest(digest.rind(), signature)
            .map_err(unspecified)
    }
}

verification_algorithm!(EcdsaVerificationAlgorithm);

/// An ECDSA signing algorithm, which an [`EcdsaKeyPair`] is bound to.
#[derive(Debug, Eq, PartialEq)]
pub struct EcdsaSigningAlgorithm(&'static EcdsaVerificationAlgorithm);

impl Deref for EcdsaSigningAlgorithm {
    type Target = EcdsaVerificationAlgorithm;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl sealed::Sealed for EcdsaSigningAlgorithm {}

macro_rules! ecdsa {
    ($verify:ident, $curve:ident, $digest:ident, $format:ident, $doc:expr) => {
        #[doc = $doc]
        pub const $verify: EcdsaVerificationAlgorithm = EcdsaVerificationAlgorithm {
            id: EcdsaCurve::$curve,
            digest: &digest::$digest,
            sig_format: EcdsaSignatureFormat::$format,
        };
    };
    ($verify:ident, $sign:ident, $curve:ident, $digest:ident, $format:ident, $doc:expr) => {
        ecdsa!($verify, $curve, $digest, $format, $doc);

        #[doc = $doc]
        pub const $sign: EcdsaSigningAlgorithm = EcdsaSigningAlgorithm(&$verify);
    };
}

ecdsa!(
    ECDSA_P256_SHA256_ASN1,
    ECDSA_P256_SHA256_ASN1_SIGNING,
    ECDSA_P256,
    SHA256,
    ASN1,
    "ECDSA on P-256 with SHA-256, ASN.1 DER signatures."
);
ecdsa!(
    ECDSA_P256_SHA256_FIXED,
    ECDSA_P256_SHA256_FIXED_SIGNING,
    ECDSA_P256,
    SHA256,
    Fixed,
    "ECDSA on P-256 with SHA-256, `r || s` signatures."
);
ecdsa!(
    ECDSA_P256_SHA384_ASN1,
    ECDSA_P256,
    SHA384,
    ASN1,
    "ECDSA on P-256 with SHA-384, ASN.1 DER signatures."
);
ecdsa!(
    ECDSA_P256_SHA512_ASN1,
    ECDSA_P256,
    SHA512,
    ASN1,
    "ECDSA on P-256 with SHA-512, ASN.1 DER signatures."
);
ecdsa!(
    ECDSA_P384_SHA256_ASN1,
    ECDSA_P384,
    SHA256,
    ASN1,
    "ECDSA on P-384 with SHA-256, ASN.1 DER signatures."
);
ecdsa!(
    ECDSA_P384_SHA384_ASN1,
    ECDSA_P384_SHA384_ASN1_SIGNING,
    ECDSA_P384,
    SHA384,
    ASN1,
    "ECDSA on P-384 with SHA-384, ASN.1 DER signatures."
);
ecdsa!(
    ECDSA_P384_SHA384_FIXED,
    ECDSA_P384_SHA384_FIXED_SIGNING,
    ECDSA_P384,
    SHA384,
    Fixed,
    "ECDSA on P-384 with SHA-384, `r || s` signatures."
);
ecdsa!(
    ECDSA_P384_SHA512_ASN1,
    ECDSA_P384,
    SHA512,
    ASN1,
    "ECDSA on P-384 with SHA-512, ASN.1 DER signatures."
);
ecdsa!(
    ECDSA_P521_SHA256_ASN1,
    ECDSA_P521_SHA256_ASN1_SIGNING,
    ECDSA_P521,
    SHA256,
    ASN1,
    "ECDSA on P-521 with SHA-256, ASN.1 DER signatures."
);
ecdsa!(
    ECDSA_P521_SHA256_FIXED,
    ECDSA_P521_SHA256_FIXED_SIGNING,
    ECDSA_P521,
    SHA256,
    Fixed,
    "ECDSA on P-521 with SHA-256, `r || s` signatures."
);
ecdsa!(
    ECDSA_P521_SHA384_ASN1,
    ECDSA_P521_SHA384_ASN1_SIGNING,
    ECDSA_P521,
    SHA384,
    ASN1,
    "ECDSA on P-521 with SHA-384, ASN.1 DER signatures."
);
ecdsa!(
    ECDSA_P521_SHA384_FIXED,
    ECDSA_P521_SHA384_FIXED_SIGNING,
    ECDSA_P521,
    SHA384,
    Fixed,
    "ECDSA on P-521 with SHA-384, `r || s` signatures."
);
ecdsa!(
    ECDSA_P521_SHA512_ASN1,
    ECDSA_P521_SHA512_ASN1_SIGNING,
    ECDSA_P521,
    SHA512,
    ASN1,
    "ECDSA on P-521 with SHA-512, ASN.1 DER signatures."
);
ecdsa!(
    ECDSA_P521_SHA512_FIXED,
    ECDSA_P521_SHA512_FIXED_SIGNING,
    ECDSA_P521,
    SHA512,
    Fixed,
    "ECDSA on P-521 with SHA-512, `r || s` signatures."
);

/// An ECDSA private key and its public key, bound to one signing algorithm.
#[derive(Clone)]
pub struct EcdsaKeyPair {
    algorithm: &'static EcdsaSigningAlgorithm,
    key: Arc<rind::signature::EcdsaKeyPair>,
    public_key: EcdsaPublicKey,
}

impl EcdsaKeyPair {
    fn new(algorithm: &'static EcdsaSigningAlgorithm, key: rind::signature::EcdsaKeyPair) -> Self {
        let public_key = EcdsaPublicKey {
            point: key.public_key().as_ref().into(),
            spki: key.to_spki().as_ref().into(),
        };
        Self {
            algorithm,
            key: Arc::new(key),
            public_key,
        }
    }

    /// Generates a key pair for `alg` from the system random source.
    pub fn generate(alg: &'static EcdsaSigningAlgorithm) -> Result<Self, Unspecified> {
        let key =
            rind::signature::EcdsaKeyPair::generate(alg.rind_signing()).map_err(unspecified)?;
        Ok(Self::new(alg, key))
    }

    /// Loads a PKCS#8 `ECPrivateKey` on `alg`'s curve.
    pub fn from_pkcs8(
        alg: &'static EcdsaSigningAlgorithm,
        pkcs8: &[u8],
    ) -> Result<Self, KeyRejected> {
        let key = rind::signature::EcdsaKeyPair::from_pkcs8(alg.rind_signing(), pkcs8)
            .map_err(KeyRejected::rind)?;
        Ok(Self::new(alg, key))
    }

    /// Generates a key pair for `alg` and returns it as PKCS#8 v1.
    pub fn generate_pkcs8(
        alg: &'static EcdsaSigningAlgorithm,
        rng: &dyn rand::SecureRandom,
    ) -> Result<pkcs8::Document, Unspecified> {
        let _ = rng;
        Self::generate(alg)?.to_pkcs8v1()
    }

    /// Encodes the key pair as PKCS#8 v1.
    pub fn to_pkcs8v1(&self) -> Result<pkcs8::Document, Unspecified> {
        Ok(pkcs8::Document::new(self.key.to_pkcs8().as_ref()))
    }

    /// Loads a big-endian private scalar, refused unless `public_key`, an
    /// X9.62 point, is its public key.
    pub fn from_private_key_and_public_key(
        alg: &'static EcdsaSigningAlgorithm,
        private_key: &[u8],
        public_key: &[u8],
    ) -> Result<Self, KeyRejected> {
        let key = rind::signature::EcdsaKeyPair::from_scalar_and_public_key(
            alg.rind_signing(),
            private_key,
            public_key,
        )
        .map_err(KeyRejected::rind)?;
        Ok(Self::new(alg, key))
    }

    /// Loads a private key from PKCS#8 or a SEC1 (RFC 5915) `ECPrivateKey`.
    pub fn from_private_key_der(
        alg: &'static EcdsaSigningAlgorithm,
        private_key: &[u8],
    ) -> Result<Self, KeyRejected> {
        let key = rind::signature::EcdsaKeyPair::from_pkcs8(alg.rind_signing(), private_key)
            .or_else(|_| rind::signature::EcdsaKeyPair::from_sec1(alg.rind_signing(), private_key))
            .map_err(KeyRejected::rind)?;
        Ok(Self::new(alg, key))
    }

    /// The private key, to serialize.
    #[must_use]
    pub fn private_key(&self) -> EcdsaPrivateKey<'_> {
        EcdsaPrivateKey(self)
    }

    /// The key pair's algorithm.
    #[must_use]
    pub fn algorithm(&self) -> &'static EcdsaSigningAlgorithm {
        self.algorithm
    }

    /// Signs `message` with a fresh random nonce.
    pub fn sign(
        &self,
        rng: &dyn rand::SecureRandom,
        message: &[u8],
    ) -> Result<Signature, Unspecified> {
        let _ = rng;
        let digest = rind::digest::digest(self.algorithm.digest.rind(), message);
        self.key
            .sign_digest(&digest)
            .map(Signature)
            .map_err(unspecified)
    }

    /// Signs the message `digest` hashes, which must be the algorithm's hash.
    pub fn sign_digest(&self, digest: &Digest) -> Result<Signature, Unspecified> {
        if digest.algorithm() != self.algorithm.digest {
            return Err(Unspecified);
        }
        self.key
            .sign_digest(digest.rind())
            .map(Signature)
            .map_err(unspecified)
    }
}

impl KeyPair for EcdsaKeyPair {
    type PublicKey = EcdsaPublicKey;

    fn public_key(&self) -> &EcdsaPublicKey {
        &self.public_key
    }
}

impl fmt::Debug for EcdsaKeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "EcdsaKeyPair {{ public_key: {:?} }}", self.public_key)
    }
}

/// An [`EcdsaKeyPair`]'s private key, to serialize.
pub struct EcdsaPrivateKey<'a>(&'a EcdsaKeyPair);

impl fmt::Debug for EcdsaPrivateKey<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "EcdsaPrivateKey({:?})", self.0.algorithm.id)
    }
}

impl AsBigEndian<EcPrivateKeyBin<'static>> for EcdsaPrivateKey<'_> {
    /// The big-endian scalar, the curve's length.
    fn as_be_bytes(&self) -> Result<EcPrivateKeyBin<'static>, Unspecified> {
        Ok(EcPrivateKeyBin::new(
            self.0.key.to_scalar().as_ref().to_vec(),
        ))
    }
}

impl AsDer<EcPrivateKeyRfc5915Der<'static>> for EcdsaPrivateKey<'_> {
    /// A SEC1 (RFC 5915) `ECPrivateKey` naming its curve and holding its
    /// public key.
    fn as_der(&self) -> Result<EcPrivateKeyRfc5915Der<'static>, Unspecified> {
        Ok(EcPrivateKeyRfc5915Der::new(
            self.0.key.to_sec1().as_ref().to_vec(),
        ))
    }
}

/// An ECDSA public key, whose bytes are its uncompressed point.
#[derive(Clone)]
pub struct EcdsaPublicKey {
    point: Box<[u8]>,
    spki: Box<[u8]>,
}

impl AsRef<[u8]> for EcdsaPublicKey {
    fn as_ref(&self) -> &[u8] {
        &self.point
    }
}

impl fmt::Debug for EcdsaPublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("EcdsaPublicKey(")?;
        fmt::Debug::fmt(&crate::Hex(&self.point), f)?;
        f.write_str(")")
    }
}

impl AsDer<PublicKeyX509Der<'static>> for EcdsaPublicKey {
    fn as_der(&self) -> Result<PublicKeyX509Der<'static>, Unspecified> {
        Ok(PublicKeyX509Der::new(self.spki.to_vec()))
    }
}

impl AsBigEndian<EcPublicKeyCompressedBin<'static>> for EcdsaPublicKey {
    fn as_be_bytes(&self) -> Result<EcPublicKeyCompressedBin<'static>, Unspecified> {
        Ok(EcPublicKeyCompressedBin::new(crate::agreement::compress(
            &self.point,
        )))
    }
}

impl AsBigEndian<EcPublicKeyUncompressedBin<'static>> for EcdsaPublicKey {
    fn as_be_bytes(&self) -> Result<EcPublicKeyUncompressedBin<'static>, Unspecified> {
        Ok(EcPublicKeyUncompressedBin::new(self.point.to_vec()))
    }
}

/// Ed25519 verification.
///
/// It takes a public key as its 32 bytes or as a `SubjectPublicKeyInfo`, as
/// aws-lc-rs does. A key of small order verifies no signature.
#[derive(Debug, Eq, PartialEq)]
pub struct EdDSAParameters;

impl private::Verify for EdDSAParameters {
    fn parse(&self, public_key: &[u8]) -> Result<rind::signature::PublicKey, KeyRejected> {
        let algorithm = &rind::signature::verify::ED25519;
        match public_key.len() {
            ED25519_PUBLIC_KEY_LEN => rind::signature::PublicKey::new(algorithm, public_key),
            _ => rind::signature::PublicKey::from_spki(algorithm, public_key),
        }
        .map_err(KeyRejected::rind)
    }

    fn verify_parsed(
        &self,
        key: &rind::signature::PublicKey,
        msg: &[u8],
        signature: &[u8],
    ) -> Result<(), Unspecified> {
        key.verify(msg, signature).map_err(unspecified)
    }

    fn verify_parsed_digest(
        &self,
        _: &rind::signature::PublicKey,
        _: &Digest,
        _: &[u8],
    ) -> Result<(), Unspecified> {
        Err(Unspecified)
    }
}

verification_algorithm!(EdDSAParameters);

/// Ed25519 verification.
pub const ED25519: EdDSAParameters = EdDSAParameters;

/// The length of an Ed25519 public key, in bytes.
pub const ED25519_PUBLIC_KEY_LEN: usize = 32;

/// An Ed25519 private key and its public key.
#[derive(Clone)]
pub struct Ed25519KeyPair {
    key: Arc<rind::signature::Ed25519KeyPair>,
    public_key: Ed25519PublicKey,
}

impl Ed25519KeyPair {
    fn new(key: rind::signature::Ed25519KeyPair) -> Self {
        let mut public_key = [0; ED25519_PUBLIC_KEY_LEN];
        public_key.copy_from_slice(key.public_key().as_ref());
        Self {
            key: Arc::new(key),
            public_key: Ed25519PublicKey(public_key),
        }
    }

    /// Generates a key pair from the system random source.
    pub fn generate() -> Result<Self, Unspecified> {
        Ok(Self::new(
            rind::signature::Ed25519KeyPair::generate().map_err(unspecified)?,
        ))
    }

    /// Generates a key pair and returns it as PKCS#8 v2, with its public key.
    pub fn generate_pkcs8(rng: &dyn rand::SecureRandom) -> Result<pkcs8::Document, Unspecified> {
        let _ = rng;
        Self::generate()?.to_pkcs8()
    }

    /// Encodes the key pair as PKCS#8 v2, with its public key.
    pub fn to_pkcs8(&self) -> Result<pkcs8::Document, Unspecified> {
        Ok(pkcs8::Document::new(self.key.to_pkcs8().as_ref()))
    }

    /// Generates a key pair and returns it as PKCS#8 v1, without its public
    /// key.
    pub fn generate_pkcs8v1(rng: &dyn rand::SecureRandom) -> Result<pkcs8::Document, Unspecified> {
        let _ = rng;
        Self::generate()?.to_pkcs8v1()
    }

    /// Encodes the private key as PKCS#8 v1, without its public key.
    pub fn to_pkcs8v1(&self) -> Result<pkcs8::Document, Unspecified> {
        Ok(pkcs8::Document::new(self.key.to_pkcs8v1().as_ref()))
    }

    /// Loads a 32-byte seed, refused unless `public_key` is its public key.
    pub fn from_seed_and_public_key(seed: &[u8], public_key: &[u8]) -> Result<Self, KeyRejected> {
        rind::signature::Ed25519KeyPair::from_seed_and_public_key(seed, public_key)
            .map(Self::new)
            .map_err(KeyRejected::rind)
    }

    /// Loads a 32-byte seed, deriving its public key.
    pub fn from_seed_unchecked(seed: &[u8]) -> Result<Self, KeyRejected> {
        rind::signature::Ed25519KeyPair::from_seed(seed)
            .map(Self::new)
            .map_err(KeyRejected::rind)
    }

    /// Loads a PKCS#8 v1 or v2 key, refused if a v2 public key does not
    /// match.
    pub fn from_pkcs8(pkcs8: &[u8]) -> Result<Self, KeyRejected> {
        rind::signature::Ed25519KeyPair::from_pkcs8(pkcs8)
            .map(Self::new)
            .map_err(KeyRejected::rind)
    }

    /// Loads a PKCS#8 v1 or v2 key, as [`Self::from_pkcs8`] does.
    pub fn from_pkcs8_maybe_unchecked(pkcs8: &[u8]) -> Result<Self, KeyRejected> {
        Self::from_pkcs8(pkcs8)
    }

    /// Signs `msg`.
    #[must_use]
    pub fn sign(&self, msg: &[u8]) -> Signature {
        Signature(self.key.sign(msg))
    }

    /// Signs `msg`, which never fails.
    pub fn try_sign(&self, msg: &[u8]) -> Result<Signature, Unspecified> {
        Ok(self.sign(msg))
    }

    /// The private key's seed.
    pub fn seed(&self) -> Result<Ed25519Seed<'static>, Unspecified> {
        let mut seed = Wiped::new([0; 32]);
        seed.copy_from_slice(self.key.to_seed().as_ref());
        Ok(Ed25519Seed {
            bytes: seed,
            phantom: PhantomData,
        })
    }
}

impl KeyPair for Ed25519KeyPair {
    type PublicKey = Ed25519PublicKey;

    fn public_key(&self) -> &Ed25519PublicKey {
        &self.public_key
    }
}

impl fmt::Debug for Ed25519KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ed25519KeyPair {{ public_key: {:?} }}", self.public_key)
    }
}

impl AsDer<Pkcs8V1Der<'static>> for Ed25519KeyPair {
    fn as_der(&self) -> Result<Pkcs8V1Der<'static>, Unspecified> {
        Ok(Pkcs8V1Der::new(self.key.to_pkcs8v1().as_ref().to_vec()))
    }
}

impl AsDer<Pkcs8V2Der<'static>> for Ed25519KeyPair {
    fn as_der(&self) -> Result<Pkcs8V2Der<'static>, Unspecified> {
        Ok(Pkcs8V2Der::new(self.key.to_pkcs8().as_ref().to_vec()))
    }
}

/// An Ed25519 private key's seed; wiped on drop under the `wipe` feature.
#[derive(Clone)]
pub struct Ed25519Seed<'a> {
    bytes: Wiped<[u8; 32]>,
    phantom: PhantomData<&'a [u8]>,
}

impl AsBigEndian<Curve25519SeedBin<'static>> for Ed25519Seed<'_> {
    fn as_be_bytes(&self) -> Result<Curve25519SeedBin<'static>, Unspecified> {
        Ok(Curve25519SeedBin::new(self.bytes.to_vec()))
    }
}

impl fmt::Debug for Ed25519Seed<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Ed25519Seed()")
    }
}

/// An Ed25519 public key's 32 bytes.
#[derive(Clone)]
pub struct Ed25519PublicKey([u8; ED25519_PUBLIC_KEY_LEN]);

impl AsRef<[u8]> for Ed25519PublicKey {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for Ed25519PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PublicKey(")?;
        fmt::Debug::fmt(&crate::Hex(&self.0), f)?;
        f.write_str(")")
    }
}

impl AsDer<PublicKeyX509Der<'static>> for Ed25519PublicKey {
    fn as_der(&self) -> Result<PublicKeyX509Der<'static>, Unspecified> {
        // RFC 8410's `SubjectPublicKeyInfo` prefix for an Ed25519 key.
        const PREFIX: [u8; 12] = [
            0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00,
        ];
        let mut der = PREFIX.to_vec();
        der.extend_from_slice(&self.0);
        Ok(PublicKeyX509Der::new(der))
    }
}

mod mldsa;
pub use mldsa::{
    ML_DSA_44, ML_DSA_44_SIGNING, ML_DSA_65, ML_DSA_65_SIGNING, ML_DSA_87, ML_DSA_87_SIGNING,
    PqdsaKeyPair, PqdsaPrivateKey, PqdsaPublicKey, PqdsaSigningAlgorithm,
    PqdsaVerificationAlgorithm,
};
