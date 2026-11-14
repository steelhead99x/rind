//! Authenticated encryption with associated data.
//!
//! ring's OpenSSH ChaCha20-Poly1305 (`chacha20_poly1305_openssh`) is not
//! offered: rind refuses it, having no SSH consumer.

use core::fmt;
use core::ops::RangeFrom;
use std::sync::Arc;

use crate::{error, hkdf};

pub mod quic;

/// An AEAD algorithm, chosen by one of this module's statics.
pub struct Algorithm {
    rind: &'static rind::aead::Algorithm,
    id: AlgorithmId,
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AlgorithmId {
    AES_128_GCM,
    AES_256_GCM,
    CHACHA20_POLY1305,
}

impl Algorithm {
    /// The length of a key, in bytes.
    pub fn key_len(&self) -> usize {
        self.rind.key_len()
    }

    /// The length of a tag, in bytes.
    pub fn tag_len(&self) -> usize {
        self.rind.tag_len()
    }

    /// The length of a nonce, in bytes.
    pub fn nonce_len(&self) -> usize {
        self.rind.nonce_len()
    }
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl PartialEq for Algorithm {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Algorithm {}

/// An AEAD key is [`Algorithm::key_len`] bytes.
impl hkdf::KeyType for &'static Algorithm {
    fn len(&self) -> usize {
        self.key_len()
    }
}

/// AES-128 in GCM mode.
pub static AES_128_GCM: Algorithm = Algorithm {
    rind: &rind::aead::AES_128_GCM,
    id: AlgorithmId::AES_128_GCM,
};

/// AES-256 in GCM mode.
pub static AES_256_GCM: Algorithm = Algorithm {
    rind: &rind::aead::AES_256_GCM,
    id: AlgorithmId::AES_256_GCM,
};

/// ChaCha20-Poly1305, from RFC 8439.
pub static CHACHA20_POLY1305: Algorithm = Algorithm {
    rind: &rind::aead::CHACHA20_POLY1305,
    id: AlgorithmId::CHACHA20_POLY1305,
};

/// The length of a nonce, in bytes, for every algorithm.
pub const NONCE_LEN: usize = 12;

/// The longest tag of any algorithm, in bytes.
pub const MAX_TAG_LEN: usize = TAG_LEN;

const TAG_LEN: usize = 16;

/// A nonce, which the caller promises seals only once under a key.
pub struct Nonce([u8; NONCE_LEN]);

impl Nonce {
    /// Wraps `value`, failing unless it is [`NONCE_LEN`] bytes.
    pub fn try_assume_unique_for_key(value: &[u8]) -> Result<Self, error::Unspecified> {
        Ok(Self(value.try_into()?))
    }

    /// Wraps `value`, which the caller promises is never reused with the same key.
    pub fn assume_unique_for_key(value: [u8; NONCE_LEN]) -> Self {
        Self(value)
    }

    fn into_rind(self) -> rind::aead::Nonce {
        rind::aead::Nonce::assume_unique_for_key(self.0)
    }
}

impl AsRef<[u8; NONCE_LEN]> for Nonce {
    fn as_ref(&self) -> &[u8; NONCE_LEN] {
        &self.0
    }
}

/// A source of nonces for a [`SealingKey`] or [`OpeningKey`], each used once.
pub trait NonceSequence {
    /// Returns the next nonce, or fails once the sequence is exhausted.
    fn advance(&mut self) -> Result<Nonce, error::Unspecified>;
}

/// Associated data, authenticated but not encrypted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Aad<A>(A);

impl<A: AsRef<[u8]>> Aad<A> {
    /// Wraps `aad`.
    #[allow(clippy::should_implement_trait)]
    pub fn from(aad: A) -> Self {
        Self(aad)
    }
}

impl Aad<[u8; 0]> {
    /// No associated data.
    pub fn empty() -> Self {
        Self([])
    }
}

impl<A: AsRef<[u8]>> AsRef<[u8]> for Aad<A> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

/// An authentication tag.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Tag([u8; TAG_LEN]);

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl From<[u8; TAG_LEN]> for Tag {
    fn from(value: [u8; TAG_LEN]) -> Self {
        Self(value)
    }
}

/// Fails unless `value` is a tag's length.
impl TryFrom<&[u8]> for Tag {
    type Error = error::Unspecified;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        Ok(Self(value.try_into()?))
    }
}

/// A key not yet bound to a nonce sequence, for a [`SealingKey`], [`OpeningKey`], or [`LessSafeKey`].
pub struct UnboundKey(LessSafeKey);

impl UnboundKey {
    /// Expands `key_bytes` for `algorithm`, failing unless it is [`Algorithm::key_len`] bytes.
    pub fn new(
        algorithm: &'static Algorithm,
        key_bytes: &[u8],
    ) -> Result<Self, error::Unspecified> {
        let key =
            rind::aead::Key::new(algorithm.rind, key_bytes).map_err(|_| error::Unspecified)?;
        Ok(Self(LessSafeKey {
            key: Arc::new(key),
            algorithm,
        }))
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.0.algorithm
    }
}

impl fmt::Debug for UnboundKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt_debug("UnboundKey", f)
    }
}

impl From<hkdf::Okm<'_, &'static Algorithm>> for UnboundKey {
    fn from(okm: hkdf::Okm<'_, &'static Algorithm>) -> Self {
        let algorithm = *okm.len();
        let mut key = [0u8; 32];
        let key = &mut key[..algorithm.key_len()];
        okm.fill_exact(key);
        Self::new(algorithm, key).expect("key_len bytes are a valid key")
    }
}

/// A key that seals or opens with any nonce the caller gives it; wiped on drop under rind's `wipe` feature.
///
/// A clone shares the expanded key.
#[derive(Clone)]
pub struct LessSafeKey {
    key: Arc<rind::aead::Key>,
    algorithm: &'static Algorithm,
}

impl LessSafeKey {
    /// Wraps `key`.
    pub fn new(key: UnboundKey) -> Self {
        key.0
    }

    /// Opens `in_out[ciphertext]` against the separate `tag`, and returns the
    /// plaintext, moved to the front of `in_out`.
    pub fn open_in_place_separate_tag<'in_out, A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        tag: Tag,
        in_out: &'in_out mut [u8],
        ciphertext: RangeFrom<usize>,
    ) -> Result<&'in_out mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        let start = ciphertext.start;
        let opened = in_out.get_mut(ciphertext).ok_or(error::Unspecified)?;
        let len = opened.len();
        let tag = rind::aead::Tag::try_from(&tag.0[..]).map_err(|_| error::Unspecified)?;
        let opened = self
            .key
            .open_in_place_separate_tag(nonce.into_rind(), aad.as_ref(), tag, opened)
            .is_ok();
        if !opened {
            // As ring does, so a caller never reads unauthenticated bytes.
            in_out[..len].fill(0);
            return Err(error::Unspecified);
        }
        in_out.copy_within(start.., 0);
        Ok(&mut in_out[..len])
    }

    /// Opens `in_out`, the ciphertext followed by its tag, and returns the plaintext.
    pub fn open_in_place<'in_out, A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &'in_out mut [u8],
    ) -> Result<&'in_out mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        self.open_within(nonce, aad, in_out, 0..)
    }

    /// Opens `in_out[ciphertext_and_tag]`, and returns the plaintext, moved to the front of `in_out`.
    pub fn open_within<'in_out, A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &'in_out mut [u8],
        ciphertext_and_tag: RangeFrom<usize>,
    ) -> Result<&'in_out mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        let tag_offset = in_out
            .len()
            .checked_sub(TAG_LEN)
            .ok_or(error::Unspecified)?;
        let (in_out, tag) = in_out.split_at_mut(tag_offset);
        let tag = Tag::try_from(&*tag)?;
        self.open_in_place_separate_tag(nonce, aad, tag, in_out, ciphertext_and_tag)
    }

    /// Seals `in_out` in place and appends the tag to it.
    pub fn seal_in_place_append_tag<A, InOut>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &mut InOut,
    ) -> Result<(), error::Unspecified>
    where
        A: AsRef<[u8]>,
        InOut: AsMut<[u8]> + for<'in_out> Extend<&'in_out u8>,
    {
        let tag = self.seal_in_place_separate_tag(nonce, aad, in_out.as_mut())?;
        in_out.extend(tag.as_ref());
        Ok(())
    }

    /// Seals `in_out` in place and returns the tag.
    pub fn seal_in_place_separate_tag<A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &mut [u8],
    ) -> Result<Tag, error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        let tag = self
            .key
            .seal_in_place_separate_tag(nonce.into_rind(), aad.as_ref(), in_out)
            .map_err(|_| error::Unspecified)?;
        Tag::try_from(tag.as_ref())
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    fn fmt_debug(&self, name: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct(name)
            .field("algorithm", self.algorithm)
            .finish()
    }
}

impl fmt::Debug for LessSafeKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_debug("LessSafeKey", f)
    }
}

/// A key bound to a [`NonceSequence`]: a [`SealingKey`] or [`OpeningKey`].
pub trait BoundKey<N: NonceSequence>: fmt::Debug {
    /// Binds `key` to `nonce_sequence`.
    fn new(key: UnboundKey, nonce_sequence: N) -> Self;

    /// The algorithm this key was made for.
    fn algorithm(&self) -> &'static Algorithm;
}

/// A key that seals with each nonce its sequence gives.
pub struct SealingKey<N: NonceSequence> {
    key: LessSafeKey,
    nonce_sequence: N,
}

impl<N: NonceSequence> BoundKey<N> for SealingKey<N> {
    fn new(key: UnboundKey, nonce_sequence: N) -> Self {
        Self {
            key: key.0,
            nonce_sequence,
        }
    }

    fn algorithm(&self) -> &'static Algorithm {
        self.key.algorithm
    }
}

impl<N: NonceSequence> fmt::Debug for SealingKey<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.key.fmt_debug("SealingKey", f)
    }
}

impl<N: NonceSequence> SealingKey<N> {
    /// Seals `in_out` in place under the next nonce and appends the tag to it.
    pub fn seal_in_place_append_tag<A, InOut>(
        &mut self,
        aad: Aad<A>,
        in_out: &mut InOut,
    ) -> Result<(), error::Unspecified>
    where
        A: AsRef<[u8]>,
        InOut: AsMut<[u8]> + for<'in_out> Extend<&'in_out u8>,
    {
        let nonce = self.nonce_sequence.advance()?;
        self.key.seal_in_place_append_tag(nonce, aad, in_out)
    }

    /// Seals `in_out` in place under the next nonce and returns the tag.
    pub fn seal_in_place_separate_tag<A>(
        &mut self,
        aad: Aad<A>,
        in_out: &mut [u8],
    ) -> Result<Tag, error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        let nonce = self.nonce_sequence.advance()?;
        self.key.seal_in_place_separate_tag(nonce, aad, in_out)
    }
}

/// A key that opens with each nonce its sequence gives.
pub struct OpeningKey<N: NonceSequence> {
    key: LessSafeKey,
    nonce_sequence: N,
}

impl<N: NonceSequence> BoundKey<N> for OpeningKey<N> {
    fn new(key: UnboundKey, nonce_sequence: N) -> Self {
        Self {
            key: key.0,
            nonce_sequence,
        }
    }

    fn algorithm(&self) -> &'static Algorithm {
        self.key.algorithm
    }
}

impl<N: NonceSequence> fmt::Debug for OpeningKey<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.key.fmt_debug("OpeningKey", f)
    }
}

impl<N: NonceSequence> OpeningKey<N> {
    /// Opens `in_out`, the ciphertext followed by its tag, under the next nonce.
    pub fn open_in_place<'in_out, A>(
        &mut self,
        aad: Aad<A>,
        in_out: &'in_out mut [u8],
    ) -> Result<&'in_out mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        let nonce = self.nonce_sequence.advance()?;
        self.key.open_in_place(nonce, aad, in_out)
    }

    /// Opens `in_out[ciphertext_and_tag]` under the next nonce, and returns
    /// the plaintext, moved to the front of `in_out`.
    pub fn open_within<'in_out, A>(
        &mut self,
        aad: Aad<A>,
        in_out: &'in_out mut [u8],
        ciphertext_and_tag: RangeFrom<usize>,
    ) -> Result<&'in_out mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        let nonce = self.nonce_sequence.advance()?;
        self.key.open_within(nonce, aad, in_out, ciphertext_and_tag)
    }
}
