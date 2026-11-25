// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use super::{NONCE_LEN, TAG_LEN, Tag};
use crate::cipher::new_handle;
use crate::ffi::{self, Bytes, Handle, Status, ids, opaque};
use crate::{Error, hkdf};

opaque! {
    QuicHpKey => rind_fips_quic_hp_free,
    QuicSealingKey => rind_fips_quic_sealing_key_free,
}

unsafe extern "C" {
    fn rind_fips_quic_sealing_key_new(
        id: u32,
        key: *const u8,
        len: usize,
        iv: *const [u8; NONCE_LEN],
        out: *mut *mut QuicSealingKey,
    ) -> Status;
    fn rind_fips_quic_seal(
        key: *mut QuicSealingKey,
        pn: u64,
        aad: *const u8,
        aad_len: usize,
        in_out: *mut u8,
        len: usize,
        tag: *mut [u8; TAG_LEN],
    ) -> Status;
    fn rind_fips_quic_hp_new(
        id: u32,
        key: *const u8,
        len: usize,
        out: *mut *mut QuicHpKey,
    ) -> Status;
    fn rind_fips_quic_hp_mask(
        key: *const QuicHpKey,
        sample: *const [u8; SAMPLE_LEN],
        mask: *mut [u8; 5],
    );
    fn rind_fips_hkdf_expand_quic_hp(
        prk: *const hkdf::HkdfPrk,
        info: *const Bytes,
        info_len: usize,
        id: u32,
    ) -> *mut QuicHpKey;
}

/// The length of a header-protection sample, in bytes, for every algorithm.
pub const SAMPLE_LEN: usize = 16;

/// A header-protection cipher, which fixes the key length a key must have.
pub struct Algorithm {
    id: u32,
    name: &'static str,
    key_len: usize,
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Algorithm")
            .field("id", &format_args!("{}", self.name))
            .finish()
    }
}

impl Algorithm {
    /// The length of a key, in bytes.
    pub fn key_len(&self) -> usize {
        self.key_len
    }
}

/// AES-128 header protection, which QUIC pairs with AES-128-GCM.
pub static AES_128: Algorithm = Algorithm {
    id: ids::aes::AES_128,
    name: "Aes128",
    key_len: 16,
};

/// AES-256 header protection, which QUIC pairs with AES-256-GCM.
pub static AES_256: Algorithm = Algorithm {
    id: ids::aes::AES_256,
    name: "Aes256",
    key_len: 32,
};

/// A header-protection key, expanded once for its algorithm; held in the
/// module, which wipes it on drop.
pub struct HeaderProtectionKey {
    algorithm: &'static Algorithm,
    handle: Handle<QuicHpKey>,
}

impl HeaderProtectionKey {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not [`Algorithm::key_len`] bytes.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        let handle = new_handle(|out| {
            // SAFETY: `key` is readable, and `out` writable.
            unsafe { rind_fips_quic_hp_new(algorithm.id, key.as_ptr(), key.len(), out) }
        })?;
        Ok(Self { algorithm, handle })
    }

    /// Computes the mask for `sample`: its first byte masks the packet's first
    /// byte, and the rest mask the packet number.
    pub fn mask(&self, sample: &[u8; SAMPLE_LEN]) -> [u8; 5] {
        let mut mask = [0; 5];
        // SAFETY: the handle is live, `sample` is `SAMPLE_LEN` readable
        // bytes, and `mask` 5 writable bytes.
        unsafe { rind_fips_quic_hp_mask(self.handle.ptr(), sample, &mut mask) };
        mask
    }
}

impl fmt::Debug for HeaderProtectionKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HeaderProtectionKey")
            .field("algorithm", &format_args!("{}", self.algorithm.name))
            .finish_non_exhaustive()
    }
}

/// A key of the algorithm's [`Algorithm::key_len`].
impl hkdf::sealed::Sealed for &'static Algorithm {}
impl hkdf::KeyType for &'static Algorithm {}

impl From<hkdf::Okm<'_, &'static Algorithm>> for HeaderProtectionKey {
    fn from(okm: hkdf::Okm<'_, &'static Algorithm>) -> Self {
        let info = okm.info();
        // SAFETY: the handle is live, and `info` lists readable strings.
        let handle = unsafe {
            rind_fips_hkdf_expand_quic_hp(
                okm.prk.handle.ptr(),
                info.as_ptr(),
                info.len(),
                okm.len.id,
            )
        };
        Self {
            algorithm: okm.len,
            handle: Handle::new(handle),
        }
    }
}

/// How many packet numbers a [`PacketSealingKey`] tracks: the highest sealed
/// and the `SEAL_WINDOW - 1` below it. A packet number `SEAL_WINDOW` or more
/// below the highest sealed is refused.
pub const SEAL_WINDOW: u64 = 1024;

/// An AES-GCM key that seals QUIC packets (RFC 9001 section 5.3), each
/// packet number once; held in the module, which wipes it on drop.
///
/// The module builds each nonce itself, as the key's packet protection IV
/// XORed with the packet number, so the caller never picks one. Unlike a
/// [`super::TlsRecordSealingKey`], it does not need packet numbers in
/// increasing order, since QUIC senders may seal packet `n + 1` before `n`:
/// the module remembers which packet numbers it has sealed among the highest
/// and the `SEAL_WINDOW - 1` below it (see [`SEAL_WINDOW`]), and refuses a
/// repeat, or one `SEAL_WINDOW` or more below the highest. Any `u64` is a
/// packet number, though QUIC's are below 2^62 (RFC 9000 section 17.1),
/// since the XOR with the IV is one-to-one on all of them. So no nonce is
/// used twice under a key, in whatever order the calls come (SP 800-38D
/// section 8.2.1). Open packets with a [`super::Key`].
///
/// ```
/// use rind_fips::aead::quic::*;
/// use rind_fips::aead::*;
///
/// let iv = [0x5a; 12];
/// let mut key = PacketSealingKey::new(&AES_128_GCM, &[7; 16], &iv).unwrap();
///
/// // Packet 6 before packet 5 is fine.
/// let mut later = b"hello".to_vec();
/// let tag6 = key
///     .seal_in_place_separate_tag(6, b"header", &mut later)
///     .unwrap();
/// let mut earlier = b"hello".to_vec();
/// key.seal_in_place_separate_tag(5, b"header", &mut earlier)
///     .unwrap();
///
/// // But a packet number twice is not.
/// let mut again = b"hello".to_vec();
/// assert_eq!(
///     key.seal_in_place_separate_tag(6, b"header", &mut again)
///         .err(),
///     Some(rind_fips::Error::MessageLimitReached)
/// );
///
/// let opening = Key::new(&AES_128_GCM, &[7; 16]).unwrap();
/// let plaintext = opening
///     .open_in_place_separate_tag(Nonce::from_sequence(&iv, 6), b"header", tag6, &mut later)
///     .unwrap();
/// assert_eq!(plaintext, b"hello");
/// ```
pub struct PacketSealingKey {
    algorithm: &'static super::Algorithm,
    handle: Handle<QuicSealingKey>,
}

impl PacketSealingKey {
    /// Expands `key` for `algorithm`, with packet protection IV `iv`,
    /// failing with [`Error::Unsupported`] unless `algorithm` is one of
    /// QUIC's, [`super::AES_128_GCM`] or [`super::AES_256_GCM`], and with
    /// [`Error::WrongLength`] if `key` is not its [`super::Algorithm::key_len`]
    /// bytes.
    pub fn new(
        algorithm: &'static super::Algorithm,
        key: &[u8],
        iv: &[u8; NONCE_LEN],
    ) -> Result<Self, Error> {
        let handle = new_handle(|out| {
            // SAFETY: `key` is readable, `iv` is its length's bytes, and
            // `out` writable.
            unsafe {
                rind_fips_quic_sealing_key_new(algorithm.id, key.as_ptr(), key.len(), iv, out)
            }
        })?;
        Ok(Self { algorithm, handle })
    }

    /// Encrypts `in_out` in place as packet `packet_number` and returns the
    /// tag.
    ///
    /// Fails with [`Error::MessageLimitReached`] if `packet_number` was
    /// sealed under the key already or is [`SEAL_WINDOW`] or more below the
    /// highest sealed, and with [`Error::WrongLength`] past the sealing
    /// limits, zeroing `in_out` in either case. The latter still spends the
    /// packet number.
    pub fn seal_in_place_separate_tag(
        &mut self,
        packet_number: u64,
        aad: &[u8],
        in_out: &mut [u8],
    ) -> Result<Tag, Error> {
        let mut tag = [0; TAG_LEN];
        // SAFETY: the handle is live and borrowed mutably, `tag` is its
        // length's bytes, `aad` readable, and `in_out` writable.
        ffi::check(unsafe {
            rind_fips_quic_seal(
                self.handle.ptr(),
                packet_number,
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

impl fmt::Debug for PacketSealingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PacketSealingKey")
            .field("algorithm", &format_args!("{}", self.algorithm.name))
            .finish_non_exhaustive()
    }
}
