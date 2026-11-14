// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::cipher::new_handle;
use crate::ffi::{self, Bytes, Handle, Status, ids, opaque};
use crate::{Error, hkdf};

/// QUIC header protection (RFC 9001 section 5.4): the mask a key derives from
/// a sample of each packet's ciphertext.
///
/// ```
/// use rind_fips::aead::quic::*;
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
/// use rind_fips::aead::gcm::*;
/// use rind_fips::cipher::AES_128;
///
/// let key = Key::new(&AES_128, &[0; 16], TagLength::Truncated96).unwrap();
///
/// // A block of zeros, sealed elsewhere: McGrew and Viega's test case 2,
/// // its tag cut to 96 bits.
/// let mut in_out = [
///     0x03, 0x88, 0xda, 0xce, 0x60, 0xb6, 0xa3, 0x92, 0xf3, 0x28, 0xc2, 0xb9, 0x71, 0xb2, 0xfe,
///     0x78, 0xab, 0x6e, 0x47, 0xd4, 0x2c, 0xec, 0x13, 0xbd, 0xf5, 0x3a, 0x67, 0xb2,
/// ];
/// let iv = Iv::assume_unique_for_key(&[0; 12]).unwrap();
/// let plaintext = key.open_in_place(iv, b"", &mut in_out).unwrap();
/// assert_eq!(plaintext, [0; 16]);
/// ```
pub mod gcm;

opaque! {
    AeadKey => rind_fips_aead_key_free,
}

unsafe extern "C" {
    fn rind_fips_aead_key_new(
        id: u32,
        key: *const u8,
        len: usize,
        out: *mut *mut AeadKey,
    ) -> Status;
    fn rind_fips_aead_open(
        key: *const AeadKey,
        nonce: *const [u8; NONCE_LEN],
        aad: *const u8,
        aad_len: usize,
        tag: *const [u8; TAG_LEN],
        in_out: *mut u8,
        len: usize,
    ) -> Status;
    fn rind_fips_hkdf_expand_aead(
        prk: *const hkdf::HkdfPrk,
        info: *const Bytes,
        info_len: usize,
        id: u32,
    ) -> *mut AeadKey;
}

const NONCE_LEN: usize = 12;
const TAG_LEN: usize = 16;

/// An AEAD algorithm, which fixes the key length a key must have.
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
    id: ids::aead::AES_128_GCM,
    name: "Aes128Gcm",
    key_len: 16,
};

/// AES-192 in GCM mode, with a 24-byte key.
pub static AES_192_GCM: Algorithm = Algorithm {
    id: ids::aead::AES_192_GCM,
    name: "Aes192Gcm",
    key_len: 24,
};

/// AES-256 in GCM mode, with a 32-byte key.
pub static AES_256_GCM: Algorithm = Algorithm {
    id: ids::aead::AES_256_GCM,
    name: "Aes256Gcm",
    key_len: 32,
};

/// An AES-GCM key that opens messages sealed under the sender's nonces;
/// held in the module, which wipes it on drop.
///
/// It does not seal: FIPS 140-3 approves AES-GCM encryption only under an
/// IV the module generates (IG C.H), which this crate does not offer yet.
pub struct Key {
    algorithm: &'static Algorithm,
    handle: Handle<AeadKey>,
}

impl Key {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not [`Algorithm::key_len`] bytes.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        let handle = new_handle(|out| {
            // SAFETY: `key` is readable, and `out` writable.
            unsafe { rind_fips_aead_key_new(algorithm.id, key.as_ptr(), key.len(), out) }
        })?;
        Ok(Self { algorithm, handle })
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
        // SAFETY: the handle is live, `nonce` and `tag` are their lengths'
        // readable bytes, `aad` readable, and `in_out` writable.
        ffi::check(unsafe {
            rind_fips_aead_open(
                self.handle.ptr(),
                &nonce.0,
                aad.as_ptr(),
                aad.len(),
                &tag.0,
                in_out.as_mut_ptr(),
                in_out.len(),
            )
        })?;
        Ok(in_out)
    }
}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Key")
            .field("algorithm", &format_args!("{}", self.algorithm.name))
            .finish_non_exhaustive()
    }
}

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

/// An authentication tag, parsed from received bytes for opening.
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

/// A key of the algorithm's [`Algorithm::key_len`].
impl hkdf::sealed::Sealed for &'static Algorithm {
    fn len(&self) -> usize {
        self.key_len()
    }
}
impl hkdf::KeyType for &'static Algorithm {}

impl From<hkdf::Okm<'_, &'static Algorithm>> for Key {
    fn from(okm: hkdf::Okm<'_, &'static Algorithm>) -> Self {
        let info = okm.info();
        // SAFETY: the handle is live, and `info` lists readable strings.
        let handle = unsafe {
            rind_fips_hkdf_expand_aead(okm.prk.handle.ptr(), info.as_ptr(), info.len(), okm.len.id)
        };
        Self {
            algorithm: okm.len,
            handle: Handle::new(handle),
        }
    }
}
