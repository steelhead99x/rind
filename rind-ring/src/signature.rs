//! Public key signatures: ECDSA on P-256 and P-384, RSA, and Ed25519.
//!
//! Calls that take a [`rand::SecureRandom`] to generate a key or sign draw
//! from the system random source inside rind, which `rng`, the only
//! `SecureRandom`, also is. ECDSA and RSA-PSS signatures are randomized, so
//! a signature never matches one a fixed source would give.

use core::fmt;

/// An RSA public key as its big-endian modulus and exponent.
pub use crate::rsa::PublicKeyComponents as RsaPublicKeyComponents;
pub use crate::rsa::{
    RsaParameters,
    padding::{
        RSA_PKCS1_SHA256, RSA_PKCS1_SHA384, RSA_PKCS1_SHA512, RSA_PSS_SHA256, RSA_PSS_SHA384,
        RSA_PSS_SHA512, RsaEncoding,
    },
    verification::{
        RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY,
        RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY,
        RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY,
        RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY, RSA_PKCS1_2048_8192_SHA256,
        RSA_PKCS1_2048_8192_SHA384, RSA_PKCS1_2048_8192_SHA512, RSA_PKCS1_3072_8192_SHA384,
        RSA_PSS_2048_8192_SHA256, RSA_PSS_2048_8192_SHA384, RSA_PSS_2048_8192_SHA512,
    },
};
use crate::{der, error, pkcs8, rand, sealed};

/// An RSA key pair, for signing.
pub type RsaKeyPair = crate::rsa::KeyPair;

/// A signature from an ECDSA or Ed25519 key pair.
#[derive(Clone, Copy)]
pub struct Signature {
    value: [u8; MAX_LEN],
    len: usize,
}

// The longest is a P-384 ASN.1 signature: a SEQUENCE, whose length takes two
// bytes, of two INTEGERs, each with a tag, a length, and a sign byte.
const MAX_LEN: usize = 3 + 2 * (3 + 48);

impl Signature {
    fn new(signature: &[u8]) -> Result<Self, error::Unspecified> {
        let mut value = [0; MAX_LEN];
        value
            .get_mut(..signature.len())
            .ok_or(error::Unspecified)?
            .copy_from_slice(signature);
        Ok(Self {
            value,
            len: signature.len(),
        })
    }
}

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        &self.value[..self.len]
    }
}

/// A key pair, whose public key verifies what it signs.
pub trait KeyPair: fmt::Debug + Send + Sized + Sync {
    /// The public key's type.
    type PublicKey: AsRef<[u8]> + fmt::Debug + Clone + Send + Sized + Sync;

    /// Returns the public key.
    fn public_key(&self) -> &Self::PublicKey;
}

/// A signature verification algorithm.
pub trait VerificationAlgorithm: fmt::Debug + Sync + sealed::Sealed {
    /// Verifies `signature` over `msg` with the encoded `public_key`.
    fn verify(
        &self,
        public_key: untrusted::Input<'_>,
        msg: untrusted::Input<'_>,
        signature: untrusted::Input<'_>,
    ) -> Result<(), error::Unspecified>;
}

/// Verifies with rind's `algorithm`, parsing `public_key` for it.
pub(crate) fn verify(
    algorithm: &'static impl AsRef<rind::signature::VerificationAlgorithm>,
    public_key: untrusted::Input<'_>,
    msg: untrusted::Input<'_>,
    signature: untrusted::Input<'_>,
) -> Result<(), error::Unspecified> {
    rind::signature::PublicKey::new(algorithm, public_key.as_slice_less_safe())
        .and_then(|key| key.verify(msg.as_slice_less_safe(), signature.as_slice_less_safe()))
        .map_err(|_| error::Unspecified)
}

/// A peer's encoded public key, parsed only when it verifies.
#[derive(Clone, Copy)]
pub struct UnparsedPublicKey<B> {
    algorithm: &'static dyn VerificationAlgorithm,
    bytes: B,
}

impl<B> UnparsedPublicKey<B> {
    /// Wraps the encoded key for `algorithm`.
    pub fn new(algorithm: &'static dyn VerificationAlgorithm, bytes: B) -> Self {
        Self { algorithm, bytes }
    }

    /// Verifies `signature` over `message`, failing for a malformed key or signature.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), error::Unspecified>
    where
        B: AsRef<[u8]>,
    {
        self.algorithm.verify(
            untrusted::Input::from(self.bytes.as_ref()),
            untrusted::Input::from(message),
            untrusted::Input::from(signature),
        )
    }
}

impl<B: AsRef<[u8]>> AsRef<[u8]> for UnparsedPublicKey<B> {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl<B: AsRef<[u8]> + fmt::Debug> fmt::Debug for UnparsedPublicKey<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("UnparsedPublicKey")
            .field("algorithm", &self.algorithm)
            .field("bytes", &crate::Hex(self.bytes.as_ref()))
            .finish()
    }
}

mod public_key {
    use core::fmt;

    /// An ECDSA key pair's uncompressed point, or an Ed25519 key pair's 32 bytes.
    #[derive(Clone)]
    pub struct PublicKey {
        bytes: [u8; MAX_LEN],
        len: usize,
    }

    // P-384's uncompressed point.
    const MAX_LEN: usize = 1 + 2 * 48;

    impl PublicKey {
        /// Copies `key`, which rind encoded for a curve rind-ring offers.
        pub(crate) fn new(key: &[u8]) -> Self {
            let mut bytes = [0; MAX_LEN];
            bytes[..key.len()].copy_from_slice(key);
            Self {
                bytes,
                len: key.len(),
            }
        }
    }

    impl AsRef<[u8]> for PublicKey {
        fn as_ref(&self) -> &[u8] {
            &self.bytes[..self.len]
        }
    }

    impl fmt::Debug for PublicKey {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_tuple("PublicKey")
                .field(&crate::Hex(self.as_ref()))
                .finish()
        }
    }
}

use public_key::PublicKey;

/// An ECDSA verification algorithm: a curve, a hash, and a signature encoding.
pub struct EcdsaVerificationAlgorithm {
    rind: &'static rind::signature::VerificationAlgorithm,
    id: &'static str,
}

impl fmt::Debug for EcdsaVerificationAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.id)
    }
}

impl sealed::Sealed for EcdsaVerificationAlgorithm {}

impl VerificationAlgorithm for EcdsaVerificationAlgorithm {
    fn verify(
        &self,
        public_key: untrusted::Input<'_>,
        msg: untrusted::Input<'_>,
        signature: untrusted::Input<'_>,
    ) -> Result<(), error::Unspecified> {
        verify(self.rind, public_key, msg, signature)
    }
}

macro_rules! ecdsa_verification {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        pub static $name: EcdsaVerificationAlgorithm = EcdsaVerificationAlgorithm {
            rind: &rind::signature::verify::$name,
            id: stringify!($name),
        };
    };
}

ecdsa_verification!(
    ECDSA_P256_SHA256_ASN1,
    "ECDSA on P-256 with SHA-256, ASN.1 DER signatures."
);
ecdsa_verification!(
    ECDSA_P256_SHA256_FIXED,
    "ECDSA on P-256 with SHA-256, `r || s` signatures."
);
ecdsa_verification!(
    ECDSA_P256_SHA384_ASN1,
    "ECDSA on P-256 with SHA-384, ASN.1 DER signatures."
);
ecdsa_verification!(
    ECDSA_P384_SHA256_ASN1,
    "ECDSA on P-384 with SHA-256, ASN.1 DER signatures."
);
ecdsa_verification!(
    ECDSA_P384_SHA384_ASN1,
    "ECDSA on P-384 with SHA-384, ASN.1 DER signatures."
);
ecdsa_verification!(
    ECDSA_P384_SHA384_FIXED,
    "ECDSA on P-384 with SHA-384, `r || s` signatures."
);

/// An ECDSA signing algorithm, which an [`EcdsaKeyPair`] is bound to.
pub struct EcdsaSigningAlgorithm {
    rind: &'static rind::signature::EcdsaSigningAlgorithm,
    id: &'static str,
}

impl fmt::Debug for EcdsaSigningAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.id)
    }
}

impl PartialEq for EcdsaSigningAlgorithm {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for EcdsaSigningAlgorithm {}

macro_rules! ecdsa_signing {
    ($name:ident, $rind:ident, $doc:expr) => {
        #[doc = $doc]
        pub static $name: EcdsaSigningAlgorithm = EcdsaSigningAlgorithm {
            rind: &rind::signature::sign::$rind,
            id: stringify!($name),
        };
    };
}

ecdsa_signing!(
    ECDSA_P256_SHA256_ASN1_SIGNING,
    ECDSA_P256_SHA256_ASN1,
    "ECDSA on P-256 with SHA-256, ASN.1 DER signatures."
);
ecdsa_signing!(
    ECDSA_P256_SHA256_FIXED_SIGNING,
    ECDSA_P256_SHA256_FIXED,
    "ECDSA on P-256 with SHA-256, `r || s` signatures."
);
ecdsa_signing!(
    ECDSA_P384_SHA384_ASN1_SIGNING,
    ECDSA_P384_SHA384_ASN1,
    "ECDSA on P-384 with SHA-384, ASN.1 DER signatures."
);
ecdsa_signing!(
    ECDSA_P384_SHA384_FIXED_SIGNING,
    ECDSA_P384_SHA384_FIXED,
    "ECDSA on P-384 with SHA-384, `r || s` signatures."
);

/// An ECDSA private key and its public key, bound to one signing algorithm.
pub struct EcdsaKeyPair {
    key: rind::signature::EcdsaKeyPair,
    public_key: PublicKey,
}

impl EcdsaKeyPair {
    /// Generates a key pair for `alg` and returns it as PKCS#8.
    pub fn generate_pkcs8(
        alg: &'static EcdsaSigningAlgorithm,
        rng: &dyn rand::SecureRandom,
    ) -> Result<pkcs8::Document, error::Unspecified> {
        let _ = rng;
        let key =
            rind::signature::EcdsaKeyPair::generate(alg.rind).map_err(|_| error::Unspecified)?;
        Ok(pkcs8::Document::new(key.to_pkcs8()))
    }

    /// Loads a PKCS#8 `ECPrivateKey` on `alg`'s curve, refused unless it
    /// carries its public key as an uncompressed point.
    pub fn from_pkcs8(
        alg: &'static EcdsaSigningAlgorithm,
        pkcs8: &[u8],
        rng: &dyn rand::SecureRandom,
    ) -> Result<Self, error::KeyRejected> {
        let _ = rng;
        let key = rind::signature::EcdsaKeyPair::from_pkcs8(alg.rind, pkcs8)
            .map_err(error::KeyRejected::rind)?;
        // ring requires the public key, uncompressed, where rind also takes
        // it compressed.
        match der::ecdsa_pkcs8_public_key(pkcs8) == Some(key.public_key().as_ref()) {
            true => Ok(Self::new(key)),
            false => Err(error::KeyRejected::invalid_encoding()),
        }
    }

    /// Loads a big-endian private scalar, refused unless `public_key`, an
    /// uncompressed point, is its public key.
    pub fn from_private_key_and_public_key(
        alg: &'static EcdsaSigningAlgorithm,
        private_key: &[u8],
        public_key: &[u8],
        rng: &dyn rand::SecureRandom,
    ) -> Result<Self, error::KeyRejected> {
        let _ = rng;
        let key = rind::signature::EcdsaKeyPair::from_scalar_and_public_key(
            alg.rind,
            private_key,
            public_key,
        )
        .map_err(error::KeyRejected::rind)?;
        // rind also takes the point compressed, which ring refuses.
        match key.public_key().as_ref() == public_key {
            true => Ok(Self::new(key)),
            false => Err(error::KeyRejected::inconsistent_components()),
        }
    }

    fn new(key: rind::signature::EcdsaKeyPair) -> Self {
        let public_key = PublicKey::new(key.public_key().as_ref());
        Self { key, public_key }
    }

    /// Signs `message` with a fresh random nonce.
    pub fn sign(
        &self,
        rng: &dyn rand::SecureRandom,
        message: &[u8],
    ) -> Result<Signature, error::Unspecified> {
        let _ = rng;
        let signature = self.key.sign(message).map_err(|_| error::Unspecified)?;
        Signature::new(signature.as_ref())
    }
}

impl KeyPair for EcdsaKeyPair {
    type PublicKey = PublicKey;

    fn public_key(&self) -> &PublicKey {
        &self.public_key
    }
}

impl fmt::Debug for EcdsaKeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EcdsaKeyPair")
            .field("public_key", &self.public_key)
            .finish()
    }
}

/// Ed25519 verification.
pub struct EdDSAParameters;

impl fmt::Debug for EdDSAParameters {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ring::signature::ED25519")
    }
}

impl sealed::Sealed for EdDSAParameters {}

impl VerificationAlgorithm for EdDSAParameters {
    fn verify(
        &self,
        public_key: untrusted::Input<'_>,
        msg: untrusted::Input<'_>,
        signature: untrusted::Input<'_>,
    ) -> Result<(), error::Unspecified> {
        verify(
            &rind::signature::verify::ED25519,
            public_key,
            msg,
            signature,
        )
    }
}

/// Ed25519 verification, with 32-byte public keys.
pub static ED25519: EdDSAParameters = EdDSAParameters;

/// The length of an Ed25519 public key, in bytes.
pub const ED25519_PUBLIC_KEY_LEN: usize = 32;

// RFC 8410's PKCS#8 v1 prefix for an Ed25519 key, before its 32-byte seed.
const ED25519_PKCS8_V1_PREFIX: [u8; 16] = [
    0x30, 0x2e, 0x02, 0x01, 0x00, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x04, 0x22, 0x04, 0x20,
];

/// An Ed25519 private key and its public key.
pub struct Ed25519KeyPair {
    key: rind::signature::Ed25519KeyPair,
    public_key: PublicKey,
}

impl Ed25519KeyPair {
    /// Generates a key pair and returns it as PKCS#8 v2, with its public key.
    pub fn generate_pkcs8(
        rng: &dyn rand::SecureRandom,
    ) -> Result<pkcs8::Document, error::Unspecified> {
        let _ = rng;
        let key = rind::signature::Ed25519KeyPair::generate().map_err(|_| error::Unspecified)?;
        Ok(pkcs8::Document::new(key.to_pkcs8()))
    }

    /// Loads a PKCS#8 v2 key, refused unless its public key matches.
    ///
    /// A v1 document, which carries no public key, is refused: load it with
    /// [`Self::from_pkcs8_maybe_unchecked`].
    pub fn from_pkcs8(pkcs8: &[u8]) -> Result<Self, error::KeyRejected> {
        Self::from_pkcs8_(pkcs8, false)
    }

    /// Loads a PKCS#8 v1 key, or a v2 key, refused unless its public key matches.
    pub fn from_pkcs8_maybe_unchecked(pkcs8: &[u8]) -> Result<Self, error::KeyRejected> {
        Self::from_pkcs8_(pkcs8, true)
    }

    fn from_pkcs8_(pkcs8: &[u8], v1: bool) -> Result<Self, error::KeyRejected> {
        let key = der::ed25519_pkcs8(pkcs8, v1)?;
        match key.public_key {
            Some(public_key) => Self::from_seed_and_public_key(key.seed, public_key),
            None => Self::from_seed_unchecked(key.seed),
        }
    }

    /// Loads a 32-byte seed, refused unless `public_key` is its public key.
    pub fn from_seed_and_public_key(
        seed: &[u8],
        public_key: &[u8],
    ) -> Result<Self, error::KeyRejected> {
        rind::signature::Ed25519KeyPair::from_seed_and_public_key(seed, public_key)
            .map(Self::new)
            .map_err(error::KeyRejected::rind)
    }

    /// Loads a 32-byte seed, computing its public key.
    pub fn from_seed_unchecked(seed: &[u8]) -> Result<Self, error::KeyRejected> {
        if seed.len() != 32 {
            return Err(error::KeyRejected::invalid_encoding());
        }
        let mut pkcs8 = [0u8; ED25519_PKCS8_V1_PREFIX.len() + 32];
        let (prefix, key) = pkcs8.split_at_mut(ED25519_PKCS8_V1_PREFIX.len());
        prefix.copy_from_slice(&ED25519_PKCS8_V1_PREFIX);
        key.copy_from_slice(seed);
        rind::signature::Ed25519KeyPair::from_pkcs8(&pkcs8[..])
            .map(Self::new)
            .map_err(error::KeyRejected::rind)
    }

    fn new(key: rind::signature::Ed25519KeyPair) -> Self {
        let public_key = PublicKey::new(key.public_key().as_ref());
        Self { key, public_key }
    }

    /// Signs `msg`.
    pub fn sign(&self, msg: &[u8]) -> Signature {
        Signature::new(self.key.sign(msg).as_ref()).expect("an Ed25519 signature is 64 bytes")
    }
}

impl KeyPair for Ed25519KeyPair {
    type PublicKey = PublicKey;

    fn public_key(&self) -> &PublicKey {
        &self.public_key
    }
}

impl fmt::Debug for Ed25519KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ed25519KeyPair")
            .field("public_key", &self.public_key)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::Signature;

    #[test]
    fn signature_buffer_fits_a_p384_asn1_signature_only() {
        // P-384's longest ASN.1 signature is the size `MAX_LEN` is built for:
        // a two-byte SEQUENCE length and two INTEGERs that each need a sign
        // byte. Turning either `+` into `*` grows the buffer, so a signature
        // one byte past that size must still be refused.
        let longest = [0x30; 3 + 2 * (3 + 48)];
        assert!(Signature::new(&longest).is_ok());
        let mut longer = longest.to_vec();
        longer.push(0x30);
        assert!(Signature::new(&longer).is_err());
    }
}
