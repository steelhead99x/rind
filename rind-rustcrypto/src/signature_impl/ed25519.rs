//! Ed25519 as `signature`'s `Signer` and `Verifier`, with `ed25519_dalek`'s
//! `SigningKey` and `VerifyingKey` names and the `ed25519` crate's `Signature`.
//!
//! rind refuses what `ed25519_dalek`'s lenient `verify` lets through: a
//! small-order public key and a non-canonical signature, as its `verify_strict`
//! does.

use core::fmt;

use signature::{Error, KeypairRef, MultipartSigner, MultipartVerifier, Signer, Verifier};

pub use ::ed25519::Signature;

/// The secret key bytes: Ed25519's 32-byte seed.
pub type SecretKey = [u8; 32];

/// A public key, with `ed25519_dalek::VerifyingKey`'s name.
#[derive(Clone)]
pub struct VerifyingKey {
    key: rind::ed25519::PublicKey,
}

impl VerifyingKey {
    /// A public key from its 32-byte encoding, refused as `rind` refuses one.
    pub fn from_bytes(bytes: &[u8; 32]) -> Result<Self, Error> {
        Self::try_from(bytes.as_slice())
    }

    /// The 32-byte encoding.
    pub fn to_bytes(&self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(self.key.as_ref());
        bytes
    }

    /// The encoding, borrowed.
    pub fn as_bytes(&self) -> &[u8; 32] {
        self.key
            .as_ref()
            .try_into()
            .expect("an Ed25519 public key is 32 bytes")
    }
}

impl TryFrom<&[u8]> for VerifyingKey {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Error> {
        rind::ed25519::PublicKey::new(bytes)
            .map(|key| Self { key })
            .map_err(|_| Error::new())
    }
}

impl AsRef<[u8]> for VerifyingKey {
    fn as_ref(&self) -> &[u8] {
        self.key.as_ref()
    }
}

impl PartialEq for VerifyingKey {
    fn eq(&self, other: &Self) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl Eq for VerifyingKey {}

impl fmt::Debug for VerifyingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "VerifyingKey({:02x?})", self.as_bytes())
    }
}

impl Verifier<Signature> for VerifyingKey {
    fn verify(&self, msg: &[u8], signature: &Signature) -> Result<(), Error> {
        self.key
            .verify(msg, &signature.to_bytes())
            .map_err(|_| Error::new())
    }
}

impl MultipartVerifier<Signature> for VerifyingKey {
    fn multipart_verify(&self, msg: &[&[u8]], signature: &Signature) -> Result<(), Error> {
        self.verify(&msg.concat(), signature)
    }
}

/// A signing key, with `ed25519_dalek::SigningKey`'s name: rind's key pair,
/// which wipes itself on drop. The wrapper holds no other copy of the seed.
pub struct SigningKey {
    pair: rind::ed25519::KeyPair,
    verifying: VerifyingKey,
}

impl SigningKey {
    /// The key a 32-byte seed makes.
    pub fn from_bytes(secret_key: &SecretKey) -> Self {
        Self::try_from(secret_key.as_slice()).expect("a 32-byte seed is a key")
    }

    /// The public key.
    pub fn verifying_key(&self) -> VerifyingKey {
        self.verifying.clone()
    }
}

impl TryFrom<&[u8]> for SigningKey {
    type Error = Error;

    /// Fails unless `seed` is 32 bytes.
    fn try_from(seed: &[u8]) -> Result<Self, Error> {
        let pair = rind::ed25519::KeyPair::from_seed(seed).map_err(|_| Error::new())?;
        let verifying = VerifyingKey {
            key: pair.public_key().clone(),
        };
        Ok(Self { pair, verifying })
    }
}

impl fmt::Debug for SigningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SigningKey")
            .field("verifying_key", &self.verifying)
            .finish_non_exhaustive()
    }
}

impl AsRef<VerifyingKey> for SigningKey {
    fn as_ref(&self) -> &VerifyingKey {
        &self.verifying
    }
}

impl KeypairRef for SigningKey {
    type VerifyingKey = VerifyingKey;
}

impl Signer<Signature> for SigningKey {
    fn try_sign(&self, msg: &[u8]) -> Result<Signature, Error> {
        let signature = self.pair.sign(msg);
        Signature::from_slice(signature.as_ref())
    }
}

impl MultipartSigner<Signature> for SigningKey {
    fn try_multipart_sign(&self, msg: &[&[u8]]) -> Result<Signature, Error> {
        self.try_sign(&msg.concat())
    }
}

impl Verifier<Signature> for SigningKey {
    fn verify(&self, msg: &[u8], signature: &Signature) -> Result<(), Error> {
        self.verifying.verify(msg, signature)
    }
}

impl MultipartVerifier<Signature> for SigningKey {
    fn multipart_verify(&self, msg: &[&[u8]], signature: &Signature) -> Result<(), Error> {
        self.verifying.multipart_verify(msg, signature)
    }
}
