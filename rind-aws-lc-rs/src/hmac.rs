//! Message authentication with HMAC.
//!
//! aws-lc-rs's `HMAC_SHA224` is not offered: rind lacks SHA-224.

use core::fmt;

use crate::{digest, error, hkdf, rand};

/// Renamed to [`Tag`].
#[deprecated(since = "1.0.0", note = "Renamed to `hmac::Tag`.")]
pub type Signature = Tag;

/// Renamed to [`Context`].
#[deprecated(since = "1.0.0", note = "Renamed to `hmac::Context`.")]
pub type SigningContext = Context;

/// Renamed to [`Key`].
#[deprecated(since = "1.0.0", note = "Renamed to `hmac::Key`.")]
pub type SigningKey = Key;

/// Merged into [`Key`].
#[deprecated(
    since = "1.0.0",
    note = "Merged into `hmac::Key`, which is used for both signing and verification."
)]
pub type VerificationKey = Key;

/// An HMAC algorithm, chosen by one of this module's constants.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Algorithm(&'static digest::Algorithm);

impl Algorithm {
    /// The hash function this HMAC is built on.
    pub fn digest_algorithm(&self) -> &'static digest::Algorithm {
        self.0
    }

    /// The length of a tag, in bytes.
    pub fn tag_len(&self) -> usize {
        self.0.output_len
    }

    fn rind(&self) -> &'static rind::hmac::Algorithm {
        use digest::AlgorithmId::*;
        match self.0.id {
            SHA1 => &rind::hmac::legacy::HMAC_SHA1,
            SHA256 => &rind::hmac::HMAC_SHA256,
            SHA384 => &rind::hmac::HMAC_SHA384,
            SHA512 => &rind::hmac::HMAC_SHA512,
            SHA512_256 | SHA3_256 | SHA3_384 | SHA3_512 => {
                unreachable!("only this module's constants make an Algorithm")
            }
        }
    }
}

/// HMAC-SHA1, for legacy protocols only.
pub const HMAC_SHA1_FOR_LEGACY_USE_ONLY: Algorithm = Algorithm(&digest::SHA1_FOR_LEGACY_USE_ONLY);

/// HMAC-SHA256.
pub const HMAC_SHA256: Algorithm = Algorithm(&digest::SHA256);

/// HMAC-SHA384.
pub const HMAC_SHA384: Algorithm = Algorithm(&digest::SHA384);

/// HMAC-SHA512.
pub const HMAC_SHA512: Algorithm = Algorithm(&digest::SHA512);

/// An HMAC key is as long as the hash's output.
impl hkdf::KeyType for Algorithm {
    fn len(&self) -> usize {
        self.tag_len()
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
        let key = &mut key[..algorithm.tag_len()];
        rng.fill(key)?;
        Ok(Self::new(algorithm, key))
    }

    /// Keys `algorithm` with `key_value`, which may be any length.
    pub fn new(algorithm: Algorithm, key_value: &[u8]) -> Self {
        Self {
            inner: rind::hmac::Key::new(algorithm.rind(), key_value),
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
            .field("algorithm", self.algorithm.0)
            .finish()
    }
}

impl From<hkdf::Okm<'_, Algorithm>> for Key {
    fn from(okm: hkdf::Okm<'_, Algorithm>) -> Self {
        let algorithm = *okm.len();
        let mut key = [0u8; digest::MAX_OUTPUT_LEN];
        let key = &mut key[..algorithm.tag_len()];
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
        Tag::new(self.inner.sign().as_ref())
    }
}

impl fmt::Debug for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Context")
            .field("algorithm", self.algorithm.0)
            .finish()
    }
}

/// Returns the tag of `data` under `key`.
pub fn sign(key: &Key, data: &[u8]) -> Tag {
    Tag::new(rind::hmac::sign(&key.inner, data).as_ref())
}

/// Writes the tag of `data` under `key` to the front of `output`, and
/// returns it, failing if `output` is shorter than a tag.
pub fn sign_to_buffer<'out>(
    key: &Key,
    data: &[u8],
    output: &'out mut [u8],
) -> Result<&'out mut [u8], error::Unspecified> {
    let output = output
        .get_mut(..key.algorithm.tag_len())
        .ok_or(error::Unspecified)?;
    output.copy_from_slice(sign(key, data).as_ref());
    Ok(output)
}

/// Checks in constant time that `tag` is the whole tag of `data` under `key`.
pub fn verify(key: &Key, data: &[u8], tag: &[u8]) -> Result<(), error::Unspecified> {
    rind::hmac::verify(&key.inner, data, tag).map_err(error::unspecified)
}

/// An HMAC tag.
#[derive(Clone, Copy, Debug)]
pub struct Tag {
    value: [u8; digest::MAX_OUTPUT_LEN],
    len: usize,
}

impl Tag {
    fn new(tag: &[u8]) -> Self {
        let mut value = [0; digest::MAX_OUTPUT_LEN];
        value[..tag.len()].copy_from_slice(tag);
        Self {
            value,
            len: tag.len(),
        }
    }
}

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        &self.value[..self.len]
    }
}
