//! Ephemeral key agreement: X25519, and ECDH on P-256 and P-384.

use core::fmt;

use crate::{error, rand};

/// A key agreement algorithm, chosen by one of this module's statics.
pub struct Algorithm {
    rind: &'static rind::agreement::Algorithm,
    curve: CurveId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CurveId {
    Curve25519,
    P256,
    P384,
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Algorithm")
            .field("curve", &self.curve)
            .finish()
    }
}

impl PartialEq for Algorithm {
    fn eq(&self, other: &Self) -> bool {
        self.curve == other.curve
    }
}

impl Eq for Algorithm {}

/// X25519 (RFC 7748).
pub static X25519: Algorithm = Algorithm {
    rind: &rind::agreement::X25519,
    curve: CurveId::Curve25519,
};

/// ECDH on P-256, with uncompressed public keys.
pub static ECDH_P256: Algorithm = Algorithm {
    rind: &rind::agreement::ECDH_P256,
    curve: CurveId::P256,
};

/// ECDH on P-384, with uncompressed public keys.
pub static ECDH_P384: Algorithm = Algorithm {
    rind: &rind::agreement::ECDH_P384,
    curve: CurveId::P384,
};

/// A private key used for one key agreement; wiped on drop.
pub struct EphemeralPrivateKey {
    key: rind::agreement::PrivateKey,
    algorithm: &'static Algorithm,
}

impl EphemeralPrivateKey {
    /// Generates a private key for `alg` from the system random source.
    ///
    /// rind draws from that source itself, which `rng`, the only
    /// [`rand::SecureRandom`], also is.
    pub fn generate(
        alg: &'static Algorithm,
        rng: &dyn rand::SecureRandom,
    ) -> Result<Self, error::Unspecified> {
        let _ = rng;
        Ok(Self {
            key: rind::agreement::PrivateKey::generate(alg.rind).map_err(|_| error::Unspecified)?,
            algorithm: alg,
        })
    }

    /// Returns the public key to send to the peer.
    pub fn compute_public_key(&self) -> Result<PublicKey, error::Unspecified> {
        Ok(PublicKey {
            bytes: self.key.public_key().clone(),
            algorithm: self.algorithm,
        })
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }
}

impl fmt::Debug for EphemeralPrivateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EphemeralPrivateKey")
            .field("algorithm", self.algorithm)
            .finish()
    }
}

/// Our public key: 32 bytes for X25519, or an uncompressed point.
#[derive(Clone)]
pub struct PublicKey {
    bytes: rind::agreement::PublicKey,
    algorithm: &'static Algorithm,
}

impl PublicKey {
    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicKey")
            .field("algorithm", self.algorithm)
            .field("bytes", &crate::Hex(self.as_ref()))
            .finish()
    }
}

/// A peer's encoded public key, parsed only when [`agree_ephemeral`] uses it.
#[derive(Clone, Copy)]
pub struct UnparsedPublicKey<B> {
    algorithm: &'static Algorithm,
    bytes: B,
}

impl<B> UnparsedPublicKey<B> {
    /// Wraps the peer's encoded key for `algorithm`.
    pub fn new(algorithm: &'static Algorithm, bytes: B) -> Self {
        Self { algorithm, bytes }
    }

    /// The algorithm the key is for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    /// The encoded key.
    pub fn bytes(&self) -> &B {
        &self.bytes
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
            .field("algorithm", self.algorithm)
            .field("bytes", &crate::Hex(self.bytes.as_ref()))
            .finish()
    }
}

/// Agrees on a secret with the peer's public key, consuming `my_private_key`, and returns `kdf` of it.
///
/// Fails if the peer's key is for another algorithm, malformed, or off the
/// curve, or if X25519 agrees on all zeros.
pub fn agree_ephemeral<B: AsRef<[u8]>, R>(
    my_private_key: EphemeralPrivateKey,
    peer_public_key: &UnparsedPublicKey<B>,
    kdf: impl FnOnce(&[u8]) -> R,
) -> Result<R, error::Unspecified> {
    if peer_public_key.algorithm != my_private_key.algorithm {
        return Err(error::Unspecified);
    }
    let secret = my_private_key
        .key
        .agree(peer_public_key.as_ref())
        .map_err(|_| error::Unspecified)?;
    Ok(kdf(secret.as_ref()))
}
