// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use super::{Algorithm, NONCE_LEN, Nonce, TAG_LEN, Tag};
use crate::Error;
use crate::cipher::new_handle;
use crate::ffi::{self, Handle, Status, opaque};

opaque! {
    Tls13SealingKey => rind_fips_tls13_sealing_key_free,
}

unsafe extern "C" {
    fn rind_fips_tls13_sealing_key_new(
        id: u32,
        key: *const u8,
        len: usize,
        out: *mut *mut Tls13SealingKey,
    ) -> Status;
    fn rind_fips_tls13_seal(
        key: *mut Tls13SealingKey,
        nonce: *const [u8; NONCE_LEN],
        aad: *const u8,
        aad_len: usize,
        in_out: *mut u8,
        len: usize,
        tag: *mut [u8; TAG_LEN],
    ) -> Status;
}

/// The TLS version whose record nonces a [`TlsRecordSealingKey`] checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TlsProtocolId {
    /// TLS 1.3 (RFC 8446), whose record nonce is the IV XORed with the
    /// record's sequence number.
    TLS13,
}

/// An AES-GCM key that seals TLS records, each only under a nonce whose
/// sequence number is above the last one's; held in the module, which wipes
/// it on drop. Open them with a [`super::Key`]: there is no
/// `TlsRecordOpeningKey`, since opening a TLS 1.3 record checks nothing that
/// opening any AES-GCM message doesn't.
///
/// This is FIPS 140-3's TLS 1.3 IV construction (IG C.H scenario 5):
/// the module manages the sequence number. Its first nonce must be the
/// traffic key's `write_iv`, sequence number 0, and each later one `write_iv`
/// XORed with its record's sequence number (RFC 8446 section 5.3), which
/// may skip ahead but never repeat or wrap. Seal nothing but TLS 1.3 records
/// with it.
///
/// ```
/// use rind_fips::aead::*;
///
/// let iv = [0x5a; 12];
/// let nonce = |seq| Nonce::from_sequence(&iv, seq);
///
/// let mut key = TlsRecordSealingKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &[7; 16]).unwrap();
/// let mut record = b"hello".to_vec();
/// key.seal_in_place_append_tag(nonce(0), b"header", &mut record)
///     .unwrap();
///
/// // A sequence number already sealed under is refused.
/// let mut again = b"hello".to_vec();
/// assert_eq!(
///     key.seal_in_place_append_tag(nonce(0), b"header", &mut again),
///     Err(rind_fips::Error::MessageLimitReached)
/// );
///
/// let opening = Key::new(&AES_128_GCM, &[7; 16]).unwrap();
/// let plaintext = opening
///     .open_in_place(nonce(0), b"header", &mut record)
///     .unwrap();
/// assert_eq!(plaintext, b"hello");
/// ```
pub struct TlsRecordSealingKey {
    algorithm: &'static Algorithm,
    handle: Handle<Tls13SealingKey>,
}

impl TlsRecordSealingKey {
    /// Expands `key` for `algorithm` and `protocol`, failing with
    /// [`Error::Unsupported`] unless `algorithm` is one of TLS's,
    /// [`super::AES_128_GCM`] or [`super::AES_256_GCM`], and with
    /// [`Error::WrongLength`] if `key` is not its [`Algorithm::key_len`]
    /// bytes.
    pub fn new(
        algorithm: &'static Algorithm,
        protocol: TlsProtocolId,
        key: &[u8],
    ) -> Result<Self, Error> {
        let TlsProtocolId::TLS13 = protocol;
        let handle = new_handle(|out| {
            // SAFETY: `key` is readable, and `out` writable.
            unsafe { rind_fips_tls13_sealing_key_new(algorithm.id, key.as_ptr(), key.len(), out) }
        })?;
        Ok(Self { algorithm, handle })
    }

    /// Encrypts `in_out` in place under `nonce` and appends the tag to it.
    ///
    /// Fails as [`Self::seal_in_place_separate_tag`] does.
    pub fn seal_in_place_append_tag<InOut>(
        &mut self,
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

    /// Encrypts `in_out` in place under `nonce` and returns the tag.
    ///
    /// Fails with [`Error::MessageLimitReached`] if `nonce`'s sequence
    /// number is not above the last one sealed, or is 2^64 - 1, past which
    /// it would wrap, and with [`Error::WrongLength`] past the sealing
    /// limits, zeroing `in_out` in either case. The latter still spends the
    /// sequence number. Both are as aws-lc does.
    pub fn seal_in_place_separate_tag(
        &mut self,
        nonce: Nonce,
        aad: &[u8],
        in_out: &mut [u8],
    ) -> Result<Tag, Error> {
        let mut tag = [0; TAG_LEN];
        // SAFETY: the handle is live and borrowed mutably, `nonce` and `tag`
        // are their lengths' bytes, `aad` readable, and `in_out` writable.
        ffi::check(unsafe {
            rind_fips_tls13_seal(
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
            .field("algorithm", &format_args!("{}", self.algorithm.name))
            .finish_non_exhaustive()
    }
}
