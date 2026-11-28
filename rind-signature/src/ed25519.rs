//! Ed25519 as `signature`'s `Signer` and `Verifier`, with `ed25519_dalek`'s
//! `SigningKey` and `VerifyingKey` names and the `ed25519` crate's `Signature`.
//!
//! rind refuses what `ed25519_dalek`'s lenient `verify` lets through: a
//! small-order public key and a non-canonical signature, as its `verify_strict`
//! does.

use core::fmt;

pub use ::ed25519::{self, Signature};
use crypto_common::rand_core::{CryptoRng, TryCryptoRng};
use crypto_common::{Generate, InvalidKey, Key, KeySizeUser, TryKeyInit, typenum::U32};
use signature::{Error, KeypairRef, MultipartSigner, MultipartVerifier};
pub use signature::{Signer, Verifier};

/// The error signing, verifying, and loading keys returns.
pub type SignatureError = Error;

/// The secret key bytes: Ed25519's 32-byte seed.
pub type SecretKey = [u8; 32];

/// The length of a signature.
pub const SIGNATURE_LENGTH: usize = 64;
/// The length of a secret key, the seed.
pub const SECRET_KEY_LENGTH: usize = 32;
/// The length of a public key.
pub const PUBLIC_KEY_LENGTH: usize = 32;
/// The length of a secret key followed by its public key.
pub const KEYPAIR_LENGTH: usize = SECRET_KEY_LENGTH + PUBLIC_KEY_LENGTH;

/// A public key, with `ed25519_dalek::VerifyingKey`'s name.
#[derive(Clone)]
#[repr(transparent)]
pub struct VerifyingKey {
    key: rind::ed25519::PublicKey,
}

impl VerifyingKey {
    /// rind's public key as this wrapper, borrowed rather than copied, so a
    /// signing key's public key is the one inside rind's key pair, which that
    /// pair wipes on drop.
    fn from_rind(key: &rind::ed25519::PublicKey) -> &Self {
        // SAFETY: `VerifyingKey` is `repr(transparent)` over rind's public key,
        // so the two share a layout and the borrow's lifetime carries over.
        unsafe { &*(key as *const rind::ed25519::PublicKey).cast::<Self>() }
    }

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
/// which wipes its whole value, public key included, on drop. The wrapper is
/// only that pair: it holds no other copy of the seed or the public key.
#[repr(transparent)]
pub struct SigningKey {
    pair: rind::ed25519::KeyPair,
}

impl SigningKey {
    /// The key a 32-byte seed makes.
    pub fn from_bytes(secret_key: &SecretKey) -> Self {
        Self::try_from(secret_key.as_slice()).expect("a 32-byte seed is a key")
    }

    /// The seed, the bytes [`Self::from_bytes`] takes.
    pub fn to_bytes(&self) -> SecretKey {
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(self.pair.to_seed().as_ref());
        bytes
    }

    /// The key a seed followed by its public key makes, refused unless the
    /// public key is the seed's.
    pub fn from_keypair_bytes(bytes: &[u8; 64]) -> Result<SigningKey, SignatureError> {
        let (seed, public_key) = bytes.split_at(SECRET_KEY_LENGTH);
        let pair = rind::ed25519::KeyPair::from_seed_and_public_key(seed, public_key)
            .map_err(|_| Error::new())?;
        Ok(Self { pair })
    }

    /// The seed followed by the public key, the bytes
    /// [`Self::from_keypair_bytes`] takes.
    pub fn to_keypair_bytes(&self) -> [u8; KEYPAIR_LENGTH] {
        let mut bytes = [0u8; KEYPAIR_LENGTH];
        bytes[..SECRET_KEY_LENGTH].copy_from_slice(self.pair.to_seed().as_ref());
        bytes[SECRET_KEY_LENGTH..].copy_from_slice(self.verifying().as_bytes());
        bytes
    }

    /// A key from a seed of 32 bytes of `csprng`.
    pub fn generate<R: CryptoRng + ?Sized>(csprng: &mut R) -> SigningKey {
        let mut secret = SecretKey::default();
        csprng.fill_bytes(&mut secret);
        Self::from_bytes(&secret)
    }

    /// The public key.
    pub fn verifying_key(&self) -> VerifyingKey {
        self.verifying().clone()
    }

    fn verifying(&self) -> &VerifyingKey {
        VerifyingKey::from_rind(self.pair.public_key())
    }
}

impl TryFrom<&[u8]> for SigningKey {
    type Error = Error;

    /// Fails unless `seed` is 32 bytes.
    fn try_from(seed: &[u8]) -> Result<Self, Error> {
        let pair = rind::ed25519::KeyPair::from_seed(seed).map_err(|_| Error::new())?;
        Ok(Self { pair })
    }
}

impl From<SecretKey> for SigningKey {
    fn from(secret: SecretKey) -> Self {
        Self::from_bytes(&secret)
    }
}

impl From<&SecretKey> for SigningKey {
    fn from(secret: &SecretKey) -> Self {
        Self::from_bytes(secret)
    }
}

impl KeySizeUser for SigningKey {
    type KeySize = U32;
}

impl TryKeyInit for SigningKey {
    fn new(key: &Key<Self>) -> Result<Self, InvalidKey> {
        Ok(Self::from_bytes(&(*key).into()))
    }
}

impl Generate for SigningKey {
    /// A key from a seed of 32 bytes of `rng`, a stack temporary left
    /// unwiped, as rind leaves its own; rind's key pair wipes its copy.
    fn try_generate_from_rng<R: TryCryptoRng + ?Sized>(rng: &mut R) -> Result<Self, R::Error> {
        let mut secret = SecretKey::default();
        rng.try_fill_bytes(&mut secret)?;
        Ok(Self::from_bytes(&secret))
    }
}

// Compares the seeds in constant time, as `ed25519_dalek` does.
impl PartialEq for SigningKey {
    fn eq(&self, other: &Self) -> bool {
        rind::constant_time::verify(self.pair.to_seed().as_ref(), other.pair.to_seed().as_ref())
            .is_ok()
    }
}

impl Eq for SigningKey {}

impl fmt::Debug for SigningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SigningKey")
            .field("verifying_key", self.verifying())
            .finish_non_exhaustive()
    }
}

impl AsRef<VerifyingKey> for SigningKey {
    fn as_ref(&self) -> &VerifyingKey {
        self.verifying()
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
        self.verifying().verify(msg, signature)
    }
}

impl MultipartVerifier<Signature> for SigningKey {
    fn multipart_verify(&self, msg: &[&[u8]], signature: &Signature) -> Result<(), Error> {
        self.verifying().multipart_verify(msg, signature)
    }
}
