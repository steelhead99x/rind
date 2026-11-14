//! Authenticated encryption with associated data.
//!
//! Not offered, as rind lacks or refuses them: AES-GCM-SIV
//! (`AES_128_GCM_SIV`, `AES_256_GCM_SIV`) and OpenSSH's ChaCha20-Poly1305
//! (`chacha20_poly1305_openssh`).

use core::fmt;
use core::ops::RangeFrom;

use crate::{error, hkdf};

pub mod nonce_sequence;
pub mod quic;
mod tls;

pub use tls::{TlsProtocolId, TlsRecordOpeningKey, TlsRecordSealingKey};

/// An AEAD algorithm, chosen by one of this module's constants.
pub struct Algorithm {
    id: AlgorithmId,
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AlgorithmId {
    AES_128_GCM,
    AES_192_GCM,
    AES_256_GCM,
    CHACHA20_POLY1305,
}

impl Algorithm {
    /// The length of a key, in bytes.
    pub fn key_len(&self) -> usize {
        self.rind().key_len()
    }

    /// The length of a tag, in bytes.
    pub fn tag_len(&self) -> usize {
        TAG_LEN
    }

    /// The length of a nonce, in bytes.
    pub fn nonce_len(&self) -> usize {
        NONCE_LEN
    }

    fn rind(&self) -> &'static rind::aead::Algorithm {
        match self.id {
            AlgorithmId::AES_128_GCM => &rind::aead::AES_128_GCM,
            AlgorithmId::AES_192_GCM => &rind::aead::AES_192_GCM,
            AlgorithmId::AES_256_GCM => &rind::aead::AES_256_GCM,
            AlgorithmId::CHACHA20_POLY1305 => &rind::aead::CHACHA20_POLY1305,
        }
    }

    fn is_aes_gcm_128_or_256(&self) -> bool {
        matches!(self.id, AlgorithmId::AES_128_GCM | AlgorithmId::AES_256_GCM)
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
pub const AES_128_GCM: Algorithm = Algorithm {
    id: AlgorithmId::AES_128_GCM,
};

/// AES-192 in GCM mode.
pub const AES_192_GCM: Algorithm = Algorithm {
    id: AlgorithmId::AES_192_GCM,
};

/// AES-256 in GCM mode.
pub const AES_256_GCM: Algorithm = Algorithm {
    id: AlgorithmId::AES_256_GCM,
};

/// ChaCha20-Poly1305, from RFC 8439.
pub const CHACHA20_POLY1305: Algorithm = Algorithm {
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

impl From<&[u8; NONCE_LEN]> for Nonce {
    fn from(bytes: &[u8; NONCE_LEN]) -> Self {
        Self(*bytes)
    }
}

/// Encodes each word little-endian.
#[allow(useless_deprecated)]
#[deprecated(
    since = "1.6.0",
    note = "Use `Nonce::assume_unique_for_key` with explicitly encoded bytes."
)]
impl From<&[u32; NONCE_LEN / 4]> for Nonce {
    fn from(values: &[u32; NONCE_LEN / 4]) -> Self {
        let mut nonce = [0; NONCE_LEN];
        for (bytes, value) in nonce.as_chunks_mut::<4>().0.iter_mut().zip(values) {
            bytes.copy_from_slice(&value.to_le_bytes());
        }
        Self(nonce)
    }
}

/// Takes the first [`NONCE_LEN`] bytes of a 16-byte IV.
impl From<&[u8; 16]> for Nonce {
    fn from(bytes: &[u8; 16]) -> Self {
        let mut nonce = [0; NONCE_LEN];
        nonce.copy_from_slice(&bytes[..NONCE_LEN]);
        Self(nonce)
    }
}

/// A source of nonces for a [`SealingKey`] or [`OpeningKey`], each used once.
pub trait NonceSequence {
    /// Returns the next nonce, or fails once the sequence is exhausted.
    fn advance(&mut self) -> Result<Nonce, error::Unspecified>;
}

/// Associated data, authenticated but not encrypted.
pub struct Aad<A: AsRef<[u8]>>(A);

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
#[must_use]
#[repr(C)]
pub struct Tag([u8; TAG_LEN]);

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Tag").finish()
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
        let key = rind::aead::Key::new(algorithm.rind(), key_bytes).map_err(error::unspecified)?;
        Ok(Self(LessSafeKey { key, algorithm }))
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

/// A key that seals or opens with any nonce the caller gives it; wiped on drop under the `wipe` feature.
pub struct LessSafeKey {
    key: rind::aead::Key,
    algorithm: &'static Algorithm,
}

impl LessSafeKey {
    /// Wraps `key`.
    pub fn new(key: UnboundKey) -> Self {
        key.0
    }

    /// Opens the ciphertext `in_out` against the separate `tag`, and returns
    /// the plaintext, written over it.
    #[allow(clippy::needless_pass_by_value)]
    pub fn open_in_place_separate_tag<'in_out, A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        tag: &[u8],
        in_out: &'in_out mut [u8],
    ) -> Result<&'in_out mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        self.open(nonce, aad.as_ref(), tag, in_out, 0..)
    }

    fn open<'in_out>(
        &self,
        nonce: Nonce,
        aad: &[u8],
        tag: &[u8],
        in_out: &'in_out mut [u8],
        ciphertext: RangeFrom<usize>,
    ) -> Result<&'in_out mut [u8], error::Unspecified> {
        let start = ciphertext.start;
        let opened = in_out.get_mut(ciphertext).ok_or(error::Unspecified)?;
        let len = opened.len();
        let tag = rind::aead::Tag::try_from(tag).map_err(error::unspecified)?;
        // rind clears `opened` when the tag does not match.
        self.key
            .open_in_place_separate_tag(nonce.into_rind(), aad, tag, opened)
            .map_err(error::unspecified)?;
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
        self.open(nonce, aad.as_ref(), tag, in_out, ciphertext_and_tag)
    }

    /// Opens `in_ciphertext` against `in_tag` into `out_plaintext`, which must
    /// be the ciphertext's length.
    pub fn open_separate_gather<A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_ciphertext: &[u8],
        in_tag: &[u8],
        out_plaintext: &mut [u8],
    ) -> Result<(), error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        if in_ciphertext.len() != out_plaintext.len() {
            return Err(error::Unspecified);
        }
        out_plaintext.copy_from_slice(in_ciphertext);
        self.open(nonce, aad.as_ref(), in_tag, out_plaintext, 0..)
            .map(|_| ())
    }

    /// Renamed to [`Self::seal_in_place_append_tag`].
    #[deprecated(since = "1.0.0", note = "Renamed to `seal_in_place_append_tag`.")]
    pub fn seal_in_place<A, InOut>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &mut InOut,
    ) -> Result<(), error::Unspecified>
    where
        A: AsRef<[u8]>,
        InOut: AsMut<[u8]> + for<'in_out> Extend<&'in_out u8>,
    {
        self.seal_in_place_append_tag(nonce, aad, in_out)
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
            .map_err(error::unspecified)?;
        Ok(Tag(tag.as_ref().try_into()?))
    }

    /// Seals `in_plaintext` into `out_ciphertext`, its length, then
    /// `extra_in` into the front of `extra_out_and_tag`, followed by the tag.
    ///
    /// `extra_out_and_tag` must be `extra_in.len()` plus the tag's length;
    /// any other length fails before either output is written.
    pub fn seal_out_of_place_scatter<A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_plaintext: &[u8],
        out_ciphertext: &mut [u8],
        extra_in: &[u8],
        extra_out_and_tag: &mut [u8],
    ) -> Result<(), error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        check_scatter(in_plaintext, out_ciphertext, extra_in, extra_out_and_tag)?;
        out_ciphertext.copy_from_slice(in_plaintext);
        self.seal_in_place_scatter(nonce, aad, out_ciphertext, extra_in, extra_out_and_tag)
    }

    /// Seals `in_out` in place, then `extra_in` into the front of
    /// `extra_out_and_tag`, followed by the tag.
    ///
    /// `extra_out_and_tag` must be `extra_in.len()` plus the tag's length.
    pub fn seal_in_place_scatter<A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &mut [u8],
        extra_in: &[u8],
        extra_out_and_tag: &mut [u8],
    ) -> Result<(), error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        if extra_out_and_tag.len() != extra_in.len() + TAG_LEN {
            return Err(error::Unspecified);
        }
        let (extra_out, tag_out) = extra_out_and_tag.split_at_mut(extra_in.len());
        let tag = match extra_in.is_empty() {
            true => self.seal_in_place_separate_tag(nonce, aad, in_out)?,
            // rind seals one contiguous buffer, so join the two plaintexts.
            false => {
                let mut joined = Vec::new();
                let len = in_out.len().checked_add(extra_in.len());
                joined
                    .try_reserve_exact(len.ok_or(error::Unspecified)?)
                    .map_err(|_| error::Unspecified)?;
                joined.extend_from_slice(in_out);
                joined.extend_from_slice(extra_in);
                let tag = self.seal_in_place_separate_tag(nonce, aad, &mut joined)?;
                let (sealed, extra_sealed) = joined.split_at(in_out.len());
                in_out.copy_from_slice(sealed);
                extra_out.copy_from_slice(extra_sealed);
                tag
            }
        };
        tag_out.copy_from_slice(&tag.0);
        Ok(())
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
    /// Renamed to [`Self::seal_in_place_append_tag`].
    #[deprecated(since = "1.0.0", note = "Renamed to `seal_in_place_append_tag`.")]
    pub fn seal_in_place<A, InOut>(
        &mut self,
        aad: Aad<A>,
        in_out: &mut InOut,
    ) -> Result<(), error::Unspecified>
    where
        A: AsRef<[u8]>,
        InOut: AsMut<[u8]> + for<'in_out> Extend<&'in_out u8>,
    {
        self.seal_in_place_append_tag(aad, in_out)
    }

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
        self.prepare_nonce()?.seal_in_place_append_tag(aad, in_out)
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
        self.prepare_nonce()?
            .seal_in_place_separate_tag(aad, in_out)
    }

    /// Takes the next nonce now, to read before sealing with it; dropping the
    /// result skips that nonce.
    pub fn prepare_nonce(&mut self) -> Result<SealingKeyPreparedNonce<'_, N>, error::Unspecified> {
        let nonce = self.nonce_sequence.advance()?;
        Ok(SealingKeyPreparedNonce { key: self, nonce })
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
        self.prepare_nonce()?.open_in_place(aad, in_out)
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
        self.prepare_nonce()?
            .open_within(aad, in_out, ciphertext_and_tag)
    }

    /// Takes the next nonce now, to read before opening with it; dropping the
    /// result skips that nonce.
    pub fn prepare_nonce(&mut self) -> Result<OpeningKeyPreparedNonce<'_, N>, error::Unspecified> {
        let nonce = self.nonce_sequence.advance()?;
        Ok(OpeningKeyPreparedNonce { key: self, nonce })
    }
}

/// A [`SealingKey`] with its next nonce taken, from [`SealingKey::prepare_nonce`].
pub struct SealingKeyPreparedNonce<'a, N: NonceSequence> {
    key: &'a mut SealingKey<N>,
    nonce: Nonce,
}

impl<N: NonceSequence> SealingKeyPreparedNonce<'_, N> {
    /// The nonce this seals with.
    pub fn nonce(&self) -> &Nonce {
        &self.nonce
    }

    /// Seals `in_out` in place and appends the tag to it.
    pub fn seal_in_place_append_tag<A, InOut>(
        self,
        aad: Aad<A>,
        in_out: &mut InOut,
    ) -> Result<(), error::Unspecified>
    where
        A: AsRef<[u8]>,
        InOut: AsMut<[u8]> + for<'in_out> Extend<&'in_out u8>,
    {
        self.key
            .key
            .seal_in_place_append_tag(self.nonce, aad, in_out)
    }

    /// Seals `in_out` in place and returns the tag.
    pub fn seal_in_place_separate_tag<A>(
        self,
        aad: Aad<A>,
        in_out: &mut [u8],
    ) -> Result<Tag, error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        self.key
            .key
            .seal_in_place_separate_tag(self.nonce, aad, in_out)
    }
}

impl<N: NonceSequence> fmt::Debug for SealingKeyPreparedNonce<'_, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SealingKeyPreparedNonce")
            .finish_non_exhaustive()
    }
}

/// An [`OpeningKey`] with its next nonce taken, from [`OpeningKey::prepare_nonce`].
pub struct OpeningKeyPreparedNonce<'a, N: NonceSequence> {
    key: &'a mut OpeningKey<N>,
    nonce: Nonce,
}

impl<N: NonceSequence> OpeningKeyPreparedNonce<'_, N> {
    /// The nonce this opens with.
    pub fn nonce(&self) -> &Nonce {
        &self.nonce
    }

    /// Opens `in_out`, the ciphertext followed by its tag.
    pub fn open_in_place<A>(
        self,
        aad: Aad<A>,
        in_out: &mut [u8],
    ) -> Result<&mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        self.open_within(aad, in_out, 0..)
    }

    /// Opens `in_out[ciphertext_and_tag]`, and returns the plaintext, moved to the front of `in_out`.
    pub fn open_within<A>(
        self,
        aad: Aad<A>,
        in_out: &mut [u8],
        ciphertext_and_tag: RangeFrom<usize>,
    ) -> Result<&mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        self.key
            .key
            .open_within(self.nonce, aad, in_out, ciphertext_and_tag)
    }
}

impl<N: NonceSequence> fmt::Debug for OpeningKeyPreparedNonce<'_, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OpeningKeyPreparedNonce")
            .finish_non_exhaustive()
    }
}

/// An AES-GCM key that picks a random nonce for each seal and returns it.
///
/// Its nonces are 96 random bits, as aws-lc-rs picks them, so seal fewer
/// than 2^32 messages under one key.
pub struct RandomizedNonceKey(LessSafeKey);

impl RandomizedNonceKey {
    /// Expands `key_bytes` for `algorithm`, which must be [`AES_128_GCM`] or [`AES_256_GCM`].
    pub fn new(
        algorithm: &'static Algorithm,
        key_bytes: &[u8],
    ) -> Result<Self, error::Unspecified> {
        if !algorithm.is_aes_gcm_128_or_256() {
            return Err(error::Unspecified);
        }
        Ok(Self(LessSafeKey::new(UnboundKey::new(
            algorithm, key_bytes,
        )?)))
    }

    /// Opens `in_out`, the ciphertext followed by its tag, under the `nonce` sealing returned.
    pub fn open_in_place<'in_out, A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &'in_out mut [u8],
    ) -> Result<&'in_out mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        self.0.open_in_place(nonce, aad, in_out)
    }

    /// Seals `in_out` in place under a random nonce, appends the tag, and returns the nonce.
    pub fn seal_in_place_append_tag<A, InOut>(
        &self,
        aad: Aad<A>,
        in_out: &mut InOut,
    ) -> Result<Nonce, error::Unspecified>
    where
        A: AsRef<[u8]>,
        InOut: AsMut<[u8]> + for<'in_out> Extend<&'in_out u8>,
    {
        let nonce = random_nonce()?;
        self.0.seal_in_place_append_tag(Nonce(nonce), aad, in_out)?;
        Ok(Nonce(nonce))
    }

    /// Seals `in_out` in place under a random nonce, and returns the nonce and tag.
    pub fn seal_in_place_separate_tag<A>(
        &self,
        aad: Aad<A>,
        in_out: &mut [u8],
    ) -> Result<(Nonce, Tag), error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        let nonce = random_nonce()?;
        let tag = self
            .0
            .seal_in_place_separate_tag(Nonce(nonce), aad, in_out)?;
        Ok((Nonce(nonce), tag))
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.0.algorithm
    }
}

impl fmt::Debug for RandomizedNonceKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RandomizedNonceKey")
            .field("algorithm", self.0.algorithm)
            .finish()
    }
}

fn random_nonce() -> Result<[u8; NONCE_LEN], error::Unspecified> {
    let mut nonce = [0; NONCE_LEN];
    crate::rand::fill(&mut nonce)?;
    Ok(nonce)
}

/// Refuses scatter buffers whose lengths do not match, before a sealing key
/// takes the nonce: `out_ciphertext` as long as `in_plaintext`, and
/// `extra_out_and_tag` as `extra_in` and the tag.
pub(crate) fn check_scatter(
    in_plaintext: &[u8],
    out_ciphertext: &[u8],
    extra_in: &[u8],
    extra_out_and_tag: &[u8],
) -> Result<(), error::Unspecified> {
    match in_plaintext.len() == out_ciphertext.len()
        && extra_out_and_tag.len() == extra_in.len() + TAG_LEN
    {
        true => Ok(()),
        false => Err(error::Unspecified),
    }
}
