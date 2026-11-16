// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Ed25519's public API: key pairs and public keys.

use core::fmt;

use super::{Buffer, Pkcs8, Spki};
use crate::error::{Error, KeyFormatError};
use crate::high::asn1;
use crate::high::ed25519::{Ed25519SigningKey, Ed25519VerifyingKey};
use crate::high::spki;
use crate::low::{self, Zeroable};

/// An Ed25519 public key: its 32 bytes, and the point they decode to.
#[derive(Clone)]
pub struct PublicKey(Ed25519VerifyingKey);

// Bytes and a point's limbs.
impl Zeroable for PublicKey {}

impl PublicKey {
    /// Parses a public key from its 32 bytes, refusing one off the curve or
    /// of small order, which verifies signatures nobody made.
    pub fn new(bytes: &[u8]) -> Result<Self, Error> {
        Ed25519VerifyingKey::from_bytes(bytes).map(Self)
    }

    /// Parses a public key from its `SubjectPublicKeyInfo` DER, which names
    /// `id-Ed25519` (RFC 8410).
    pub fn from_spki(der: &[u8]) -> Result<Self, Error> {
        Self::new(spki::decode(der, &[&asn1::oid::id_ed25519], None)?)
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo` naming
    /// `id-Ed25519`.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| self.0.to_spki_der(output)))
    }

    /// Verifies `signature` over `message`, refusing a malformed signature.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        self.0.verify(signature, message)
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PublicKey").field(&self.as_ref()).finish()
    }
}

/// An Ed25519 signature: 64 bytes.
#[derive(Clone, Copy)]
pub struct Signature([u8; 64]);

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Signature").field(&self.as_ref()).finish()
    }
}

/// An Ed25519 private key as its 32-byte seed, wiped on drop under the `wipe` feature.
pub struct Seed([u8; 32]);

impl AsRef<[u8]> for Seed {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for Seed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Seed").finish_non_exhaustive()
    }
}

impl Drop for Seed {
    fn drop(&mut self) {
        low::zeroise(&mut self.0);
    }
}

/// An Ed25519 private key and its public key.
pub struct KeyPair {
    key: Ed25519SigningKey,
    public: PublicKey,
}

impl KeyPair {
    /// Generates a key pair from the system random source.
    pub fn generate() -> Result<Self, Error> {
        Ok(Self::new(Ed25519SigningKey::generate()?))
    }

    /// Loads a PKCS#8 Ed25519 key, refused if it carries a public key
    /// (v2, RFC 5958) that does not match.
    ///
    /// This also takes PKCS#8 v1, which carries no public key: common tools
    /// write v1, and such a key is no less valid.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        Ok(Self::new(Ed25519SigningKey::from_pkcs8_der(der)?))
    }

    /// Loads a 32-byte seed, as a JWK's `d` holds it, deriving its public
    /// key.
    ///
    /// Prefer [`Self::from_seed_and_public_key`] when the public key is at
    /// hand, which checks it.
    pub fn from_seed(seed: &[u8]) -> Result<Self, Error> {
        Ok(Self::new(Ed25519SigningKey::from_bytes(seed)?))
    }

    /// Loads a 32-byte seed, refused unless `public_key` is its public key.
    ///
    /// This suits a JWK's `d` and `x`.
    pub fn from_seed_and_public_key(seed: &[u8], public_key: &[u8]) -> Result<Self, Error> {
        let pair = Self::new(Ed25519SigningKey::from_bytes(seed)?);
        match pair.public.as_ref() == public_key {
            true => Ok(pair),
            false => Err(KeyFormatError::MismatchedPublicKey.into()),
        }
    }

    fn new(key: Ed25519SigningKey) -> Self {
        let public = PublicKey(key.public_key());
        Self { key, public }
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> &PublicKey {
        &self.public
    }

    /// Signs `message`.
    pub fn sign(&self, message: &[u8]) -> Signature {
        Signature(self.key.sign(message))
    }

    /// Encodes the key pair as PKCS#8 v2 (RFC 5958).
    pub fn to_pkcs8(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| self.key.to_pkcs8_der(true, output)))
    }

    /// Encodes the private key as PKCS#8 v1 (RFC 8410), its seed without its
    /// public key, as OpenSSL and BoringSSL write it.
    pub fn to_pkcs8v1(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| {
            self.key.to_pkcs8_der(false, output)
        }))
    }

    /// Returns the private key's 32-byte seed, as a JWK's `d` holds it.
    ///
    /// This is what [`Self::from_seed_and_public_key`] loads; prefer
    /// [`Self::to_pkcs8`] for stored keys.
    pub fn to_seed(&self) -> Seed {
        Seed(*self.key.seed())
    }
}

impl fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair")
            .field("public_key", &self.public.as_ref())
            .finish_non_exhaustive()
    }
}

impl Drop for KeyPair {
    fn drop(&mut self) {
        // Not secret, but wiping it lets `tests/zeroing.rs` check every byte.
        low::zeroise_value(&mut self.public);
    }
}
