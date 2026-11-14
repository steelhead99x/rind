// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES-GCM sealing with an IV the module generates.
//!
//! IG C.H approves two constructions here. A [`RandomizedNonceKey`] draws a
//! fresh 96-bit IV from the module DRBG for each seal (SP 800-38D section
//! 8.2.2, scenario 2). A [`TlsRecordSealingKey`] is TLS 1.3: the caller
//! passes `static_iv XOR seq`, and the key owns the sequence counter,
//! refusing a repeat, a step backward, or `u64::MAX` so the counter never
//! wraps (scenario 5). Opening still takes the peer's nonce.
//!
//! TLS 1.2's explicit nonce is not offered. rind-rustls's FIPS build needs
//! only TLS 1.3, which SP 800-52r2 allows.

use core::fmt;

use super::{AeadKey, Algorithm, Key, NONCE_LEN, Nonce, TAG_LEN, Tag};
use crate::Error;
use crate::cipher::new_handle;
use crate::ffi::{self, Handle, Status, opaque};

opaque! {
    TlsSealKey => rind_fips_tls_seal_free,
}

unsafe extern "C" {
    fn rind_fips_aead_seal_random(
        key: *const AeadKey,
        aad: *const u8,
        aad_len: usize,
        in_out: *mut u8,
        len: usize,
        nonce: *mut [u8; NONCE_LEN],
        tag: *mut [u8; TAG_LEN],
    ) -> Status;
    fn rind_fips_tls_seal_new(
        id: u32,
        key: *const u8,
        len: usize,
        out: *mut *mut TlsSealKey,
    ) -> Status;
    fn rind_fips_tls_seal(
        key: *mut TlsSealKey,
        nonce: *const [u8; NONCE_LEN],
        aad: *const u8,
        aad_len: usize,
        in_out: *mut u8,
        len: usize,
        tag: *mut [u8; TAG_LEN],
    ) -> Status;
}

/// The TLS version a record key checks nonces for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TlsProtocolId {
    /// TLS 1.2 (RFC 5288). Not offered: its explicit nonce waits for a consumer.
    TLS12,
    /// TLS 1.3 (RFC 8446). The module owns the record sequence counter.
    TLS13,
}

/// An AES-GCM key that picks a random 96-bit IV for each seal and returns it.
///
/// The IV is drawn inside the module, from its DRBG. Seal fewer than 2^32
/// messages under one key: past that, random 96-bit IVs collide too often
/// for SP 800-38D. The key is held in the module, which wipes it on drop.
///
/// ```
/// use rind_fips::aead::{AES_256_GCM, RandomizedNonceKey};
///
/// let key = RandomizedNonceKey::new(&AES_256_GCM, &[0x42; 32]).unwrap();
/// let mut message = b"hello".to_vec();
/// let nonce = key
///     .seal_in_place_append_tag(b"aad", &mut message)
///     .unwrap();
/// let plain = key.open_in_place(nonce, b"aad", &mut message).unwrap();
/// assert_eq!(plain, b"hello");
/// ```
pub struct RandomizedNonceKey {
    algorithm: &'static Algorithm,
    key: Key,
}

impl RandomizedNonceKey {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not [`Algorithm::key_len`] bytes.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            algorithm,
            key: Key::new(algorithm, key)?,
        })
    }

    /// Seals `in_out` under a fresh IV, appends the tag, and returns the IV.
    ///
    /// Fails with [`Error::WrongLength`], leaving `in_out` unchanged, past
    /// GCM's limits, and with [`Error::RngFailed`] if the DRBG does.
    pub fn seal_in_place_append_tag<InOut>(
        &self,
        aad: &[u8],
        in_out: &mut InOut,
    ) -> Result<Nonce, Error>
    where
        InOut: AsMut<[u8]> + for<'a> Extend<&'a u8>,
    {
        let (nonce, tag) = self.seal_random(aad, in_out.as_mut())?;
        in_out.extend(tag.as_ref());
        Ok(nonce)
    }

    /// Seals `in_out` under a fresh IV, and returns the IV and the tag.
    ///
    /// Fails as [`Self::seal_in_place_append_tag`] does.
    pub fn seal_in_place_separate_tag(
        &self,
        aad: &[u8],
        in_out: &mut [u8],
    ) -> Result<(Nonce, Tag), Error> {
        self.seal_random(aad, in_out)
    }

    /// Decrypts and verifies `in_out`, the ciphertext followed by its tag,
    /// under the `nonce` sealing returned.
    ///
    /// Fails with [`Error::DecryptFailed`] if `in_out` is shorter than a tag
    /// or does not verify, clearing the ciphertext in the latter case, and
    /// with [`Error::WrongLength`] past the sealing limits.
    pub fn open_in_place<'a>(
        &self,
        nonce: Nonce,
        aad: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        self.key.open_in_place(nonce, aad, in_out)
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    fn seal_random(&self, aad: &[u8], in_out: &mut [u8]) -> Result<(Nonce, Tag), Error> {
        let mut nonce = [0u8; NONCE_LEN];
        let mut tag = [0u8; TAG_LEN];
        // SAFETY: the handle is live, `aad` is readable, `in_out` writable,
        // and `nonce` and `tag` are writable.
        ffi::check(unsafe {
            rind_fips_aead_seal_random(
                self.key.handle.ptr(),
                aad.as_ptr(),
                aad.len(),
                in_out.as_mut_ptr(),
                in_out.len(),
                &mut nonce,
                &mut tag,
            )
        })?;
        Ok((Nonce(nonce), Tag(tag)))
    }
}

impl fmt::Debug for RandomizedNonceKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RandomizedNonceKey")
            .field("key", &self.key)
            .finish_non_exhaustive()
    }
}

/// A TLS 1.3 record sealing key for AES-128-GCM or AES-256-GCM.
///
/// The caller passes each record's nonce, `static_iv XOR seq` with `seq`
/// starting at 0, so the first nonce is the static IV. The module remembers
/// that IV's last 8 bytes and refuses a sequence that does not move forward
/// or that is `u64::MAX`. A gap is allowed. A refused seal zeroes its
/// output, so a caller that ignores the error sends no plaintext.
///
/// The key is held in the module, which wipes it, and the sequence mask,
/// on drop.
///
/// ```
/// use rind_fips::aead::{
///     AES_128_GCM, Nonce, TlsProtocolId, TlsRecordOpeningKey, TlsRecordSealingKey,
/// };
///
/// let key_bytes = [0x42; 16];
/// let mut sealing =
///     TlsRecordSealingKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &key_bytes).unwrap();
/// let opening =
///     TlsRecordOpeningKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &key_bytes).unwrap();
/// let nonce = |seq: u64| {
///     let mut bytes = [0u8; 12];
///     bytes[4..].copy_from_slice(&seq.to_be_bytes());
///     Nonce::assume_unique_for_key(bytes)
/// };
/// let mut message = b"hello".to_vec();
/// sealing
///     .seal_in_place_append_tag(nonce(0), b"aad", &mut message)
///     .unwrap();
/// let plain = opening.open_in_place(nonce(0), b"aad", &mut message).unwrap();
/// assert_eq!(plain, b"hello");
/// ```
pub struct TlsRecordSealingKey {
    algorithm: &'static Algorithm,
    protocol: TlsProtocolId,
    handle: Handle<TlsSealKey>,
}

impl TlsRecordSealingKey {
    /// Expands `key` for `algorithm`.
    ///
    /// Fails with [`Error::Unsupported`] for [`TlsProtocolId::TLS12`] or
    /// AES-192-GCM, and with [`Error::WrongLength`] if `key` is not
    /// [`Algorithm::key_len`] bytes.
    pub fn new(
        algorithm: &'static Algorithm,
        protocol: TlsProtocolId,
        key: &[u8],
    ) -> Result<Self, Error> {
        if protocol != TlsProtocolId::TLS13 || !is_tls_aead(algorithm) {
            return Err(Error::Unsupported);
        }
        let handle = new_handle(|out| {
            // SAFETY: `key` is readable, and `out` writable.
            unsafe { rind_fips_tls_seal_new(algorithm.id, key.as_ptr(), key.len(), out) }
        })?;
        Ok(Self {
            algorithm,
            protocol,
            handle,
        })
    }

    /// Seals `in_out` in place and appends the tag, if `nonce`'s sequence is
    /// one this key still allows.
    ///
    /// Fails with [`Error::Unsupported`], zeroing `in_out` and the tag it
    /// appends, if the sequence does not move forward or is `u64::MAX`, and
    /// with [`Error::WrongLength`], leaving `in_out` unchanged, past GCM's
    /// limits. A length failure has already consumed the sequence.
    pub fn seal_in_place_append_tag<InOut>(
        &mut self,
        nonce: Nonce,
        aad: &[u8],
        in_out: &mut InOut,
    ) -> Result<(), Error>
    where
        InOut: AsMut<[u8]> + for<'a> Extend<&'a u8>,
    {
        match self.seal(&nonce, aad, in_out.as_mut()) {
            Ok(tag) => {
                in_out.extend(tag.as_ref());
                Ok(())
            }
            Err(Error::Unsupported) => {
                in_out.extend(&[0u8; TAG_LEN]);
                in_out.as_mut().fill(0);
                Err(Error::Unsupported)
            }
            Err(err) => Err(err),
        }
    }

    /// Seals `in_out` in place and returns the tag, if `nonce`'s sequence is
    /// one this key still allows.
    ///
    /// Fails as [`Self::seal_in_place_append_tag`] does. A refused sequence
    /// zeroes `in_out`.
    pub fn seal_in_place_separate_tag(
        &mut self,
        nonce: Nonce,
        aad: &[u8],
        in_out: &mut [u8],
    ) -> Result<Tag, Error> {
        self.seal(&nonce, aad, in_out)
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    /// The TLS version this key checks nonces for.
    pub fn tls_protocol_id(&self) -> TlsProtocolId {
        self.protocol
    }

    fn seal(&mut self, nonce: &Nonce, aad: &[u8], in_out: &mut [u8]) -> Result<Tag, Error> {
        let mut tag = [0u8; TAG_LEN];
        // SAFETY: the handle is live, `nonce` and `aad` readable, and
        // `in_out` and `tag` writable.
        ffi::check(unsafe {
            rind_fips_tls_seal(
                self.handle.ptr(),
                &nonce.0,
                aad.as_ptr(),
                aad.len(),
                in_out.as_mut_ptr(),
                in_out.len(),
                &mut tag,
            )
        })?;
        Ok(Tag(tag))
    }
}

impl fmt::Debug for TlsRecordSealingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TlsRecordSealingKey")
            .field("algorithm", self.algorithm)
            .field("protocol", &self.protocol)
            .finish_non_exhaustive()
    }
}

/// A TLS record opening key for AES-128-GCM or AES-256-GCM.
///
/// Decryption takes the peer's nonce, which IG C.H allows. The key does not
/// keep a sequence counter: a replay is the record layer's to reject. Held
/// in the module, which wipes it on drop.
pub struct TlsRecordOpeningKey {
    algorithm: &'static Algorithm,
    protocol: TlsProtocolId,
    key: Key,
}

impl TlsRecordOpeningKey {
    /// Expands `key` for `algorithm`.
    ///
    /// Fails with [`Error::Unsupported`] for [`TlsProtocolId::TLS12`] or
    /// AES-192-GCM, and with [`Error::WrongLength`] if `key` is not
    /// [`Algorithm::key_len`] bytes.
    pub fn new(
        algorithm: &'static Algorithm,
        protocol: TlsProtocolId,
        key: &[u8],
    ) -> Result<Self, Error> {
        if protocol != TlsProtocolId::TLS13 || !is_tls_aead(algorithm) {
            return Err(Error::Unsupported);
        }
        Ok(Self {
            algorithm,
            protocol,
            key: Key::new(algorithm, key)?,
        })
    }

    /// Decrypts and verifies `in_out`, the ciphertext followed by its tag.
    ///
    /// Fails with [`Error::DecryptFailed`] if `in_out` is shorter than a tag
    /// or does not verify, clearing the ciphertext in the latter case, and
    /// with [`Error::WrongLength`] past the sealing limits.
    pub fn open_in_place<'a>(
        &self,
        nonce: Nonce,
        aad: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        self.key.open_in_place(nonce, aad, in_out)
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    /// The TLS version this key is for.
    pub fn tls_protocol_id(&self) -> TlsProtocolId {
        self.protocol
    }
}

impl fmt::Debug for TlsRecordOpeningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TlsRecordOpeningKey")
            .field("key", &self.key)
            .field("protocol", &self.protocol)
            .finish_non_exhaustive()
    }
}

/// AES-128-GCM and AES-256-GCM, the TLS record ciphers. AES-192-GCM is not.
fn is_tls_aead(algorithm: &'static Algorithm) -> bool {
    matches!(algorithm.key_len(), 16 | 32)
}
