//! Message authentication with HMAC.

use core::fmt;

use crate::{digest, error, hkdf, rand};

/// An HMAC algorithm, chosen by one of this module's statics.
#[derive(Clone, Copy)]
pub struct Algorithm {
    digest: &'static digest::Algorithm,
    rind: &'static rind::hmac::Algorithm,
}

impl Algorithm {
    /// The hash function this HMAC is built on.
    pub fn digest_algorithm(&self) -> &'static digest::Algorithm {
        self.digest
    }
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Algorithm").field(self.digest).finish()
    }
}

impl PartialEq for Algorithm {
    fn eq(&self, other: &Self) -> bool {
        self.digest == other.digest
    }
}

impl Eq for Algorithm {}

/// HMAC-SHA1, for legacy protocols only.
pub static HMAC_SHA1_FOR_LEGACY_USE_ONLY: Algorithm = Algorithm {
    digest: &digest::SHA1_FOR_LEGACY_USE_ONLY,
    rind: &rind::hmac::legacy::HMAC_SHA1,
};

/// HMAC-SHA256.
pub static HMAC_SHA256: Algorithm = Algorithm {
    digest: &digest::SHA256,
    rind: &rind::hmac::HMAC_SHA256,
};

/// HMAC-SHA384.
pub static HMAC_SHA384: Algorithm = Algorithm {
    digest: &digest::SHA384,
    rind: &rind::hmac::HMAC_SHA384,
};

/// HMAC-SHA512.
pub static HMAC_SHA512: Algorithm = Algorithm {
    digest: &digest::SHA512,
    rind: &rind::hmac::HMAC_SHA512,
};

/// An HMAC key is as long as the hash's output.
impl hkdf::KeyType for Algorithm {
    fn len(&self) -> usize {
        self.digest.output_len()
    }
}

/// An HMAC key, keyed once and reused for every message; wiped on drop.
#[derive(Clone)]
pub struct Key {
    inner: rind::hmac::Key,
    algorithm: Algorithm,
}

impl Key {
    /// Generates a key as long as the hash's output from `rng`.
    pub fn generate(
        algorithm: Algorithm,
        rng: &dyn rand::SecureRandom,
    ) -> Result<Self, error::Unspecified> {
        let mut key = [0u8; digest::MAX_OUTPUT_LEN];
        let key = &mut key[..algorithm.digest.output_len()];
        rng.fill(key)?;
        Ok(Self::new(algorithm, key))
    }

    /// Keys `algorithm` with `key_value`, which may be any length.
    pub fn new(algorithm: Algorithm, key_value: &[u8]) -> Self {
        Self {
            inner: rind::hmac::Key::new(algorithm.rind, key_value),
            algorithm,
        }
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> Algorithm {
        self.algorithm
    }
}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Key")
            .field("algorithm", self.algorithm.digest)
            .finish()
    }
}

impl From<hkdf::Okm<'_, Algorithm>> for Key {
    fn from(okm: hkdf::Okm<'_, Algorithm>) -> Self {
        let algorithm = *okm.len();
        let mut key = [0u8; digest::MAX_OUTPUT_LEN];
        let key = &mut key[..algorithm.digest.output_len()];
        okm.fill_exact(key);
        Self::new(algorithm, key)
    }
}

/// An in-progress tag computation; a clone forks it.
#[derive(Clone)]
pub struct Context {
    inner: rind::hmac::Context,
    algorithm: Algorithm,
}

impl Context {
    /// Starts a tag computation under `signing_key`.
    pub fn with_key(signing_key: &Key) -> Self {
        Self {
            inner: rind::hmac::Context::with_key(&signing_key.inner),
            algorithm: signing_key.algorithm,
        }
    }

    /// Adds `data` to the message.
    pub fn update(&mut self, data: &[u8]) {
        self.inner.update(data);
    }

    /// Returns the tag of the message.
    pub fn sign(self) -> Tag {
        Tag(digest::Digest::new(
            self.algorithm.digest,
            self.inner.sign().as_ref(),
        ))
    }
}

impl fmt::Debug for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Context")
            .field("algorithm", self.algorithm.digest)
            .finish()
    }
}

/// Returns the tag of `data` under `key`.
pub fn sign(key: &Key, data: &[u8]) -> Tag {
    Tag(digest::Digest::new(
        key.algorithm.digest,
        rind::hmac::sign(&key.inner, data).as_ref(),
    ))
}

/// Checks in constant time that `tag` is the whole tag of `data` under `key`.
pub fn verify(key: &Key, data: &[u8], tag: &[u8]) -> Result<(), error::Unspecified> {
    rind::hmac::verify(&key.inner, data, tag).map_err(|_| error::Unspecified)
}

/// An HMAC tag.
#[derive(Clone, Copy, Debug)]
pub struct Tag(digest::Digest);

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}
