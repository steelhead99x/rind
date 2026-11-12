// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::mem::ManuallyDrop;

use crate::Error;
use crate::low::{Zeroable, ZeroableRef, zeroise_value};
use crate::mid::aes_gcm::AesGcm;
use crate::mid::chacha20poly1305::ChaCha20Poly1305;
use crate::mid::rng::{RandomSource, SystemRandom};
use crate::mid::xchacha20poly1305::XChaCha20Poly1305;

/// QUIC header protection (RFC 9001 section 5.4): the mask a key derives from
/// a sample of each packet's ciphertext.
///
/// ```
/// use rind::aead::quic::*;
///
/// // RFC 9001 appendix A.2
/// let hp = [
///     0x9f, 0x50, 0x44, 0x9e, 0x04, 0xa0, 0xe8, 0x10, 0x28, 0x3a, 0x1e, 0x99, 0x33, 0xad, 0xed,
///     0xd2,
/// ];
/// let key = HeaderProtectionKey::new(&AES_128, &hp).unwrap();
///
/// let sample = [
///     0xd1, 0xb1, 0xc9, 0x8d, 0xd7, 0x68, 0x9f, 0xb8, 0xec, 0x11, 0xd2, 0x42, 0xb1, 0x23, 0xdc,
///     0x9b,
/// ];
/// assert_eq!(key.mask(&sample), [0x43, 0x7b, 0x9a, 0xec, 0x36]);
/// ```
pub mod quic;

/// AES-GCM with an IV of any length and a tag of any length NIST allows, for
/// APIs such as WebCrypto's that let the caller pick them.
///
/// ```
/// use rind::aead::gcm::*;
/// use rind::cipher::AES_128;
///
/// let key = Key::new(&AES_128, &[0x42; 16], TagLength::Truncated96).unwrap();
///
/// let mut in_out = b"hello".to_vec();
/// let iv = || Iv::assume_unique_for_key(&[7; 16]).unwrap();
/// key.seal_in_place_append_tag(iv(), b"header", &mut in_out)
///     .unwrap();
/// assert_eq!(in_out.len(), 5 + 12);
///
/// let plaintext = key.open_in_place(iv(), b"header", &mut in_out).unwrap();
/// assert_eq!(plaintext, b"hello");
/// ```
pub mod gcm;

const NONCE_LEN: usize = 12;
const TAG_LEN: usize = 16;

/// An AEAD algorithm, which fixes the key length a key must have.
pub struct Algorithm {
    id: AlgorithmId,
    // The only path to the cipher's code, so a binary links only the ciphers
    // whose algorithms it names.
    expand: fn(&[u8]) -> Inner,
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Algorithm").field("id", &self.id).finish()
    }
}

#[derive(Debug)]
enum AlgorithmId {
    Aes128Gcm,
    Aes192Gcm,
    Aes256Gcm,
    ChaCha20Poly1305,
}

impl Algorithm {
    /// The length of a key, in bytes.
    pub fn key_len(&self) -> usize {
        match self.id {
            AlgorithmId::Aes128Gcm => 16,
            AlgorithmId::Aes192Gcm => 24,
            AlgorithmId::Aes256Gcm | AlgorithmId::ChaCha20Poly1305 => 32,
        }
    }

    /// The length of a tag, in bytes.
    pub fn tag_len(&self) -> usize {
        TAG_LEN
    }

    /// The length of a nonce, in bytes.
    pub fn nonce_len(&self) -> usize {
        NONCE_LEN
    }
}

/// AES-128 in GCM mode, with a 16-byte key.
pub static AES_128_GCM: Algorithm = Algorithm {
    id: AlgorithmId::Aes128Gcm,
    expand: Sealer::<AesGcm>::expand,
};

/// AES-192 in GCM mode, with a 24-byte key.
pub static AES_192_GCM: Algorithm = Algorithm {
    id: AlgorithmId::Aes192Gcm,
    expand: Sealer::<AesGcm>::expand,
};

/// AES-256 in GCM mode, with a 32-byte key.
pub static AES_256_GCM: Algorithm = Algorithm {
    id: AlgorithmId::Aes256Gcm,
    expand: Sealer::<AesGcm>::expand,
};

/// ChaCha20-Poly1305 from RFC 8439, with a 32-byte key.
pub static CHACHA20_POLY1305: Algorithm = Algorithm {
    id: AlgorithmId::ChaCha20Poly1305,
    expand: Sealer::<ChaCha20Poly1305>::expand,
};

/// An AEAD key that seals with any nonce the caller gives it; wiped on drop under the `wipe` feature.
///
/// The caller owns nonce uniqueness: sealing two messages with one nonce and
/// key loses confidentiality and lets anyone forge messages. Derive nonces
/// from protocol state that never repeats, such as a record sequence number,
/// or use [`RandomizedNonceKey`].
pub struct Key(Inner);

impl Key {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not [`Algorithm::key_len`] bytes.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        if key.len() != algorithm.key_len() {
            return Err(Error::WrongLength);
        }

        Ok(Self((algorithm.expand)(key)))
    }

    /// Encrypts `in_out` in place and returns the tag.
    ///
    /// Fails with [`Error::WrongLength`], leaving `in_out` unchanged, if
    /// `in_out` or `aad` is past the algorithm's limit: 2^36 - 32 and 2^61 - 1
    /// bytes for AES-GCM, and 2^38 - 64 bytes of `in_out` for
    /// ChaCha20-Poly1305.
    pub fn seal_in_place_separate_tag(
        &self,
        nonce: Nonce,
        aad: &[u8],
        in_out: &mut [u8],
    ) -> Result<Tag, Error> {
        let mut tag = [0u8; TAG_LEN];
        match &self.0 {
            Inner::AesGcm(key) => key.seal(&nonce.0, aad, in_out, &mut tag),
            Inner::ChaCha20Poly1305(key) => key.seal(&nonce.0, aad, in_out, &mut tag),
        }?;
        Ok(Tag(tag))
    }

    /// Encrypts `in_out` in place and appends the tag to it.
    ///
    /// Fails as [`Self::seal_in_place_separate_tag`] does.
    pub fn seal_in_place_append_tag<InOut>(
        &self,
        nonce: Nonce,
        aad: &[u8],
        in_out: &mut InOut,
    ) -> Result<(), Error>
    where
        InOut: AsMut<[u8]> + for<'a> Extend<&'a u8>,
    {
        let tag = self.seal_in_place_separate_tag(nonce, aad, in_out.as_mut())?;
        in_out.extend(tag.as_ref());
        Ok(())
    }

    /// Decrypts and verifies `in_out`, the ciphertext followed by its tag, and
    /// returns the plaintext at its front.
    ///
    /// Fails with [`Error::DecryptFailed`] if `in_out` is shorter than a tag or
    /// does not verify, clearing the ciphertext in the latter case, and with
    /// [`Error::WrongLength`] past the sealing limits.
    pub fn open_in_place<'a>(
        &self,
        nonce: Nonce,
        aad: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        let (in_out, tag) = in_out.split_last_chunk_mut().ok_or(Error::DecryptFailed)?;
        self.open_in_place_separate_tag(nonce, aad, Tag(*tag), in_out)
    }

    /// Decrypts and verifies `in_out` against the separate `tag`, and returns
    /// the plaintext.
    ///
    /// Fails with [`Error::DecryptFailed`], clearing `in_out`, if it does not
    /// verify, and with [`Error::WrongLength`] past the sealing limits.
    pub fn open_in_place_separate_tag<'a>(
        &self,
        nonce: Nonce,
        aad: &[u8],
        tag: Tag,
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        match &self.0 {
            Inner::AesGcm(key) => key.open(&nonce.0, aad, in_out, &tag.0),
            Inner::ChaCha20Poly1305(key) => key.open(&nonce.0, aad, in_out, &tag.0),
        }?;
        Ok(in_out)
    }
}

// All-zero is the `AesGcm` variant with an all-zero key and table and a
// `None` `ZeroableRef`, which `Zeroable` requires to be valid: every other
// field is a plain integer or vector. Neither cipher owns memory beyond
// itself, so its drop does nothing but wipe what `Inner`'s drop wipes anyway;
// `ManuallyDrop` skips that second pass.
//
// Boxing the AES-GCM table would allocate for every key to save space only on
// ChaCha20-Poly1305 keys; the 32-bit arm table is small, so the lint is allowed
// rather than expected.
#[allow(clippy::large_enum_variant)]
#[repr(u8)]
enum Inner {
    AesGcm(Sealer<AesGcm>),
    ChaCha20Poly1305(Sealer<ChaCha20Poly1305>),
}

/// An expanded key with its cipher's code, which it reaches only through
/// `ops`: matching on [`Inner`] then names no cipher's code.
struct Sealer<C: Cipher> {
    key: ManuallyDrop<C>,
    ops: ZeroableRef<Ops<C>>,
}

/// Seals in place: `(key, nonce, aad, in_out, tag)`.
type Seal<C> = fn(&C, &[u8; NONCE_LEN], &[u8], &mut [u8], &mut [u8; TAG_LEN]) -> Result<(), Error>;

/// Opens in place: `(key, nonce, aad, in_out, tag)`.
type Open<C> = fn(&C, &[u8; NONCE_LEN], &[u8], &mut [u8], &[u8; TAG_LEN]) -> Result<(), Error>;

struct Ops<C> {
    seal: Seal<C>,
    open: Open<C>,
}

/// A cipher's key, as an [`Inner`] variant holds it.
trait Cipher: Sized + 'static {
    /// Expands `key`, which the caller has checked is the algorithm's length.
    fn new(key: &[u8]) -> Self;

    fn inner(sealer: Sealer<Self>) -> Inner;

    fn seal(
        &self,
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        in_out: &mut [u8],
        tag: &mut [u8; TAG_LEN],
    ) -> Result<(), Error>;

    fn open(
        &self,
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        in_out: &mut [u8],
        tag: &[u8; TAG_LEN],
    ) -> Result<(), Error>;
}

impl<C: Cipher> Sealer<C> {
    /// Expands `key` into an [`Inner`].
    ///
    /// Not inlined, so each function wraps a value in one layer, and LLVM
    /// builds it in the caller's slot: two layers in one function, as
    /// `Ok(Key(Inner::AesGcm(..)))`, copied the whole key twice.
    #[inline(never)]
    fn expand(key: &[u8]) -> Inner {
        C::inner(Self {
            key: ManuallyDrop::new(C::new(key)),
            ops: ZeroableRef::new(
                const {
                    &Ops {
                        seal: C::seal,
                        open: C::open,
                    }
                },
            ),
        })
    }

    fn seal(
        &self,
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        in_out: &mut [u8],
        tag: &mut [u8; TAG_LEN],
    ) -> Result<(), Error> {
        (self.ops.get().seal)(&self.key, nonce, aad, in_out, tag)
    }

    fn open(
        &self,
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        in_out: &mut [u8],
        tag: &[u8; TAG_LEN],
    ) -> Result<(), Error> {
        (self.ops.get().open)(&self.key, nonce, aad, in_out, tag)
    }
}

impl Cipher for AesGcm {
    fn new(key: &[u8]) -> Self {
        Self::new(key)
    }

    fn inner(sealer: Sealer<Self>) -> Inner {
        Inner::AesGcm(sealer)
    }

    fn seal(
        &self,
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        in_out: &mut [u8],
        tag: &mut [u8; TAG_LEN],
    ) -> Result<(), Error> {
        self.encrypt(nonce, aad, in_out, tag)
    }

    fn open(
        &self,
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        in_out: &mut [u8],
        tag: &[u8; TAG_LEN],
    ) -> Result<(), Error> {
        self.decrypt(nonce, aad, in_out, tag)
    }
}

impl Cipher for ChaCha20Poly1305 {
    fn new(key: &[u8]) -> Self {
        Self::new(key.try_into().unwrap())
    }

    fn inner(sealer: Sealer<Self>) -> Inner {
        Inner::ChaCha20Poly1305(sealer)
    }

    fn seal(
        &self,
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        in_out: &mut [u8],
        tag: &mut [u8; TAG_LEN],
    ) -> Result<(), Error> {
        self.encrypt(nonce, aad, in_out, tag)
    }

    fn open(
        &self,
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        in_out: &mut [u8],
        tag: &[u8; TAG_LEN],
    ) -> Result<(), Error> {
        self.decrypt(nonce, aad, in_out, tag)
    }
}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // An id, not the static, so formatting links no other cipher's code.
        let algorithm = match &self.0 {
            Inner::AesGcm(sealer) => match sealer.key.key_len() {
                16 => AlgorithmId::Aes128Gcm,
                24 => AlgorithmId::Aes192Gcm,
                _ => AlgorithmId::Aes256Gcm,
            },
            Inner::ChaCha20Poly1305(_) => AlgorithmId::ChaCha20Poly1305,
        };
        f.debug_struct("Key")
            .field("algorithm", &algorithm)
            .finish_non_exhaustive()
    }
}

impl Drop for Inner {
    fn drop(&mut self) {
        // Wipes the discriminant and the space a smaller variant leaves unused,
        // not only the variant's own key.
        zeroise_value(self);
    }
}

impl Zeroable for Inner {}

/// A 96-bit nonce, which the caller promises seals only once under a key.
///
/// It is not `Clone`, so one value seals at most one message.
pub struct Nonce([u8; NONCE_LEN]);

impl Nonce {
    /// Wraps `nonce`, which the caller promises is never reused with the same key.
    pub fn assume_unique_for_key(nonce: [u8; NONCE_LEN]) -> Self {
        Self(nonce)
    }
}

impl fmt::Debug for Nonce {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Nonce").finish_non_exhaustive()
    }
}

/// An authentication tag: returned by sealing, or parsed from received bytes for opening.
#[derive(Clone, Copy, Debug)]
pub struct Tag([u8; TAG_LEN]);

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

/// Fails with [`Error::WrongLength`] unless `tag` is [`Algorithm::tag_len`] bytes.
impl TryFrom<&[u8]> for Tag {
    type Error = Error;

    fn try_from(tag: &[u8]) -> Result<Self, Error> {
        tag.try_into().map(Self).map_err(|_| Error::WrongLength)
    }
}

/// An XChaCha20-Poly1305 key that picks a random 192-bit nonce for every seal.
///
/// A 192-bit nonce is long enough that random ones never collide in
/// practice, so the caller tracks no nonce state.
pub struct RandomizedNonceKey(XChaCha20Poly1305);

impl RandomizedNonceKey {
    /// Makes a key from 32 bytes of key material.
    pub fn new(key: &[u8; 32]) -> Self {
        Self(XChaCha20Poly1305::new(*key))
    }

    /// Encrypts `in_out` in place under a fresh random nonce, appends the tag,
    /// and returns the nonce, which the opener needs.
    ///
    /// Fails with [`Error::RngFailed`] if the system random source does, or
    /// with [`Error::WrongLength`], leaving `in_out` unchanged, if it is longer
    /// than 2^38 - 64 bytes.
    pub fn seal_in_place_append_tag<InOut>(
        &self,
        aad: &[u8],
        in_out: &mut InOut,
    ) -> Result<RandomNonce, Error>
    where
        InOut: AsMut<[u8]> + for<'a> Extend<&'a u8>,
    {
        let mut nonce = [0u8; 24];
        SystemRandom.fill(&mut nonce)?;
        let mut tag = [0u8; TAG_LEN];
        self.0.encrypt(&nonce, aad, in_out.as_mut(), &mut tag)?;
        in_out.extend(&tag);
        Ok(RandomNonce(nonce))
    }

    /// Encrypts `in_out` in place under `nonce`, which the caller promises
    /// never to repeat with this key, and appends the tag.
    ///
    /// Repeating a nonce loses confidentiality and lets anyone forge
    /// messages, as with [`Nonce::assume_unique_for_key`]. Prefer
    /// [`Self::seal_in_place_append_tag`], which picks the nonce.
    ///
    /// Fails with [`Error::WrongLength`], leaving `in_out` unchanged, if it
    /// is longer than 2^38 - 64 bytes.
    pub fn seal_in_place_append_tag_with_nonce<InOut>(
        &self,
        nonce: RandomNonce,
        aad: &[u8],
        in_out: &mut InOut,
    ) -> Result<(), Error>
    where
        InOut: AsMut<[u8]> + for<'a> Extend<&'a u8>,
    {
        let mut tag = [0u8; TAG_LEN];
        self.0.encrypt(&nonce.0, aad, in_out.as_mut(), &mut tag)?;
        in_out.extend(&tag);
        Ok(())
    }

    /// Decrypts and verifies `in_out`, the ciphertext followed by its tag,
    /// sealed under `nonce`, and returns the plaintext at its front.
    ///
    /// Fails as [`Key::open_in_place`] does.
    pub fn open_in_place<'a>(
        &self,
        nonce: RandomNonce,
        aad: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        let (in_out, tag) = in_out.split_last_chunk_mut().ok_or(Error::DecryptFailed)?;
        self.0.decrypt(&nonce.0, aad, in_out, tag)?;
        Ok(in_out)
    }
}

impl fmt::Debug for RandomizedNonceKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RandomizedNonceKey").finish_non_exhaustive()
    }
}

/// The 192-bit nonce a [`RandomizedNonceKey`] picked, to send with its ciphertext.
#[derive(Clone, Copy, Debug)]
pub struct RandomNonce([u8; 24]);

impl AsRef<[u8]> for RandomNonce {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl From<[u8; 24]> for RandomNonce {
    fn from(nonce: [u8; 24]) -> Self {
        Self(nonce)
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    const ALGORITHMS: [&Algorithm; 4] =
        [&AES_128_GCM, &AES_192_GCM, &AES_256_GCM, &CHACHA20_POLY1305];

    #[test]
    fn key_length_must_match_algorithm() {
        let key = [0u8; 33];
        for algorithm in ALGORITHMS {
            for len in 0..=key.len() {
                assert_eq!(
                    Key::new(algorithm, &key[..len]).is_ok(),
                    len == algorithm.key_len(),
                    "{algorithm:?} len {len}"
                );
            }
        }
    }

    #[test]
    fn seal_and_open() {
        for algorithm in ALGORITHMS {
            let key = Key::new(algorithm, &[7u8; 32][..algorithm.key_len()]).unwrap();
            assert_eq!(algorithm.nonce_len(), 12);
            let nonce = || Nonce::assume_unique_for_key([9; 12]);

            let mut sealed = b"hello".to_vec();
            key.seal_in_place_append_tag(nonce(), b"aad", &mut sealed)
                .unwrap();
            assert_eq!(sealed.len(), 5 + algorithm.tag_len());

            let mut separate = b"hello".to_vec();
            let tag = key
                .seal_in_place_separate_tag(nonce(), b"aad", &mut separate)
                .unwrap();
            assert_eq!([&separate[..], tag.as_ref()].concat(), sealed);

            let mut opened = sealed.clone();
            assert_eq!(
                key.open_in_place(nonce(), b"aad", &mut opened).unwrap(),
                b"hello"
            );
            assert_eq!(
                key.open_in_place_separate_tag(nonce(), b"aad", tag, &mut separate)
                    .unwrap(),
                b"hello"
            );

            // A wrong AAD fails and clears the ciphertext, leaving the tag.
            let mut wrong = sealed.clone();
            assert_eq!(
                key.open_in_place(nonce(), &[], &mut wrong),
                Err(Error::DecryptFailed)
            );
            assert_eq!(wrong[..5], [0; 5]);
            assert_eq!(wrong[5..], sealed[5..]);
        }
    }

    #[test]
    fn open_refuses_input_shorter_than_tag() {
        for algorithm in ALGORITHMS {
            let key = Key::new(algorithm, &[7u8; 32][..algorithm.key_len()]).unwrap();
            let mut short = [0xaau8; TAG_LEN - 1];
            assert_eq!(
                key.open_in_place(Nonce::assume_unique_for_key([0; 12]), &[], &mut short),
                Err(Error::DecryptFailed)
            );
            assert_eq!(short, [0xaa; TAG_LEN - 1]);
        }
    }

    #[test]
    fn tag_must_be_whole() {
        let bytes = [0u8; TAG_LEN + 1];
        for len in 0..=bytes.len() {
            assert_eq!(
                Tag::try_from(&bytes[..len]).is_ok(),
                len == TAG_LEN,
                "len {len}"
            );
        }
    }

    #[test]
    fn randomized_nonce_key() {
        let key = RandomizedNonceKey::new(&[3u8; 32]);

        let mut first = b"ticket".to_vec();
        let nonce = key.seal_in_place_append_tag(b"name", &mut first).unwrap();
        let mut second = b"ticket".to_vec();
        let other = key.seal_in_place_append_tag(b"name", &mut second).unwrap();
        assert_ne!(nonce.as_ref(), other.as_ref());
        assert_ne!(first, second);

        let received = RandomNonce::from(<[u8; 24]>::try_from(nonce.as_ref()).unwrap());
        assert_eq!(
            key.open_in_place(received, b"name", &mut first).unwrap(),
            b"ticket"
        );
        assert_eq!(
            key.open_in_place(nonce, b"name", &mut second),
            Err(Error::DecryptFailed)
        );
        assert_eq!(
            key.open_in_place(nonce, &[], &mut [0u8; TAG_LEN - 1]),
            Err(Error::DecryptFailed)
        );

        let chosen = RandomNonce::from([9u8; 24]);
        let mut with_nonce = b"ticket".to_vec();
        key.seal_in_place_append_tag_with_nonce(chosen, b"name", &mut with_nonce)
            .unwrap();
        let mut again = b"ticket".to_vec();
        key.seal_in_place_append_tag_with_nonce(chosen, b"name", &mut again)
            .unwrap();
        assert_eq!(with_nonce, again);
        assert_eq!(
            key.open_in_place(chosen, b"name", &mut with_nonce).unwrap(),
            b"ticket"
        );
    }
}
