// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::Error;
use crate::cipher::{Algorithm, new_handle};
use crate::ffi::{self, Handle, Status, opaque};

opaque! {
    GcmKey => rind_fips_gcm_key_free,
}

unsafe extern "C" {
    fn rind_fips_gcm_key_new(
        id: u32,
        key: *const u8,
        len: usize,
        tag_len: usize,
        out: *mut *mut GcmKey,
    ) -> Status;
    fn rind_fips_gcm_open(
        key: *const GcmKey,
        iv: *const u8,
        iv_len: usize,
        aad: *const u8,
        aad_len: usize,
        tag: *const u8,
        tag_len: usize,
        in_out: *mut u8,
        len: usize,
    ) -> Status;
}

/// How long an AES-GCM tag is: one of NIST SP 800-38D's lengths, named in bits.
///
/// A forger's every try at a `t`-bit tag succeeds with probability 2^-t, and
/// each forgery against a short tag also helps recover the authentication key
/// (Ferguson, "Authentication weaknesses in GCM"). Keep [`TagLength::Full`]
/// unless a protocol fixes a shorter tag; SP 800-38D's Appendix C bounds how
/// much one key may open under 32- and 64-bit tags.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum TagLength {
    /// The whole 128-bit tag.
    Full,
    /// The first 120 bits of the tag.
    Truncated120,
    /// The first 112 bits of the tag.
    Truncated112,
    /// The first 104 bits of the tag.
    Truncated104,
    /// The first 96 bits of the tag.
    Truncated96,
    /// The first 64 bits of the tag.
    Truncated64,
    /// The first 32 bits of the tag.
    Truncated32,
}

impl TagLength {
    fn bytes(self) -> usize {
        match self {
            Self::Full => 16,
            Self::Truncated120 => 15,
            Self::Truncated112 => 14,
            Self::Truncated104 => 13,
            Self::Truncated96 => 12,
            Self::Truncated64 => 8,
            Self::Truncated32 => 4,
        }
    }
}

/// An AES-GCM IV of any length but zero, which the caller promises seals
/// only once under a key.
///
/// It is not `Clone`, so one value seals at most one message.
pub struct Iv<'a>(&'a [u8]);

impl<'a> Iv<'a> {
    /// Wraps `iv`, which the caller promises is never reused with the same
    /// key, failing with [`Error::WrongLength`] if it is empty or past GCM's
    /// limit of 2^61 - 1 bytes.
    pub fn assume_unique_for_key(iv: &'a [u8]) -> Result<Self, Error> {
        if iv.is_empty() || iv.len() as u64 >= 1 << 61 {
            return Err(Error::WrongLength);
        }
        Ok(Self(iv))
    }
}

impl fmt::Debug for Iv<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Iv").finish_non_exhaustive()
    }
}

/// An AES-GCM key that takes an IV of any length and checks tags of one
/// [`TagLength`], as WebCrypto's AES-GCM does; held in the module, which
/// wipes it on drop.
///
/// Prefer [`super::Key`] and [`super::RandomizedNonceKey`], whose 96-bit
/// nonces and full tags are what protocols use; GCM hashes an IV of any
/// other length into its counter, which weakens its bounds. It opens only,
/// as [`super::Key`] does. Sealing with an IV the module generates is
/// [`super::RandomizedNonceKey`].
pub struct Key {
    algorithm: &'static Algorithm,
    tag_len: TagLength,
    handle: Handle<GcmKey>,
}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Key")
            .field("algorithm", self.algorithm)
            .finish_non_exhaustive()
    }
}

impl Key {
    /// Expands `key` for `algorithm`, to check tags of `tag_len`, failing
    /// with [`Error::WrongLength`] if it is not that algorithm's key length.
    pub fn new(
        algorithm: &'static Algorithm,
        key: &[u8],
        tag_len: TagLength,
    ) -> Result<Self, Error> {
        let handle = new_handle(|out| {
            // SAFETY: `key` is readable, and `out` writable.
            unsafe {
                rind_fips_gcm_key_new(
                    algorithm.id(),
                    key.as_ptr(),
                    key.len(),
                    tag_len.bytes(),
                    out,
                )
            }
        })?;
        Ok(Self {
            algorithm,
            tag_len,
            handle,
        })
    }

    /// The length of this key's tags, in bytes.
    pub fn tag_len(&self) -> usize {
        self.tag_len.bytes()
    }

    /// Decrypts and verifies `in_out`, the ciphertext followed by its tag of
    /// [`Self::tag_len`] bytes, and returns the plaintext at its front.
    ///
    /// Fails with [`Error::DecryptFailed`] if `in_out` is shorter than a tag
    /// or does not verify, clearing the ciphertext in the latter case, and
    /// with [`Error::WrongLength`] past the sealing limits.
    pub fn open_in_place<'a>(
        &self,
        iv: Iv<'_>,
        aad: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        let at = in_out
            .len()
            .checked_sub(self.tag_len())
            .ok_or(Error::DecryptFailed)?;
        let (in_out, tag) = in_out.split_at_mut(at);
        self.open_in_place_separate_tag(iv, aad, tag, in_out)
    }

    /// Decrypts and verifies `in_out` against the separate `tag`, and returns
    /// the plaintext.
    ///
    /// Fails with [`Error::WrongLength`], leaving `in_out` unchanged, if
    /// `tag` is not [`Self::tag_len`] bytes or past the sealing limits, and
    /// with [`Error::DecryptFailed`], clearing `in_out`, if it does not
    /// verify.
    pub fn open_in_place_separate_tag<'a>(
        &self,
        iv: Iv<'_>,
        aad: &[u8],
        tag: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        // SAFETY: the handle is live, `iv`, `aad`, and `tag` readable, and
        // `in_out` writable.
        ffi::check(unsafe {
            rind_fips_gcm_open(
                self.handle.ptr(),
                iv.0.as_ptr(),
                iv.0.len(),
                aad.as_ptr(),
                aad.len(),
                tag.as_ptr(),
                tag.len(),
                in_out.as_mut_ptr(),
                in_out.len(),
            )
        })?;
        Ok(in_out)
    }
}
