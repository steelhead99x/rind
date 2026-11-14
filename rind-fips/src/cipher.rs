// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::Error;
use crate::ffi::{self, Handle, Opaque, Status, ids, opaque};

opaque! {
    AesKey => rind_fips_aes_free,
    AesCtrKey => rind_fips_aes_ctr_free,
    AesCbcEncrypting => rind_fips_aes_cbc_encrypting_free,
    AesCbcDecrypting => rind_fips_aes_cbc_decrypting_free,
}

unsafe extern "C" {
    fn rind_fips_aes_new(id: u32, key: *const u8, len: usize, out: *mut *mut AesKey) -> Status;
    fn rind_fips_aes_encrypt_block(key: *const AesKey, block: *mut [u8; 16]);
    fn rind_fips_aes_ctr_new(
        id: u32,
        key: *const u8,
        len: usize,
        counter_bits: u8,
        out: *mut *mut AesCtrKey,
    ) -> Status;
    fn rind_fips_aes_ctr_apply(
        key: *const AesCtrKey,
        counter_block: *const [u8; 16],
        in_out: *mut u8,
        len: usize,
    ) -> Status;
    fn rind_fips_aes_cbc_encrypting_new(
        id: u32,
        key: *const u8,
        len: usize,
        out: *mut *mut AesCbcEncrypting,
    ) -> Status;
    fn rind_fips_aes_cbc_encrypt_blocks(
        key: *const AesCbcEncrypting,
        iv: *const [u8; 16],
        in_out: *mut u8,
        len: usize,
    ) -> Status;
    fn rind_fips_aes_cbc_decrypting_new(
        id: u32,
        key: *const u8,
        len: usize,
        out: *mut *mut AesCbcDecrypting,
    ) -> Status;
    fn rind_fips_aes_cbc_decrypt(
        key: *const AesCbcDecrypting,
        iv: *const [u8; 16],
        in_out: *mut u8,
        len: usize,
        plaintext_len: *mut usize,
    ) -> Status;
    fn rind_fips_aes_cbc_decrypt_blocks(
        key: *const AesCbcDecrypting,
        iv: *const [u8; 16],
        in_out: *mut u8,
        len: usize,
    ) -> Status;
}

/// Takes ownership of the handle `make` writes to its argument, if the
/// status it returns is 0.
pub(crate) fn new_handle<T: Opaque>(
    make: impl FnOnce(*mut *mut T) -> Status,
) -> Result<Handle<T>, Error> {
    let mut out = core::ptr::null_mut();
    let status = make(&mut out);
    Handle::from_status(status, out)
}

/// An AES key size, which fixes the key length a key must have.
#[derive(Debug)]
pub struct Algorithm {
    pub(crate) key_len: usize,
}

impl Algorithm {
    /// The module's number for this key size.
    pub(crate) fn id(&self) -> u32 {
        match self.key_len {
            16 => ids::aes::AES_128,
            24 => ids::aes::AES_192,
            _ => ids::aes::AES_256,
        }
    }
}

/// AES with a 16-byte key.
pub static AES_128: Algorithm = Algorithm { key_len: 16 };

/// AES with a 24-byte key.
pub static AES_192: Algorithm = Algorithm { key_len: 24 };

/// AES with a 32-byte key.
pub static AES_256: Algorithm = Algorithm { key_len: 32 };

/// An AES key that encrypts single blocks; held in the module, which wipes
/// it on drop.
///
/// This is the bare block cipher. Use it only where a protocol specifies
/// AES on one block, such as DTLS 1.3 record number protection or SRTP key
/// derivation; QUIC header protection has [`crate::aead::quic`].
pub struct Aes {
    algorithm: &'static Algorithm,
    handle: Handle<AesKey>,
}

impl Aes {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not that algorithm's key length.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        // SAFETY: `key` is readable, and `out` writable.
        let handle = new_handle(|out| unsafe {
            rind_fips_aes_new(algorithm.id(), key.as_ptr(), key.len(), out)
        })?;
        Ok(Self { algorithm, handle })
    }

    /// Encrypts one block in place.
    pub fn encrypt_block(&self, block: &mut [u8; 16]) {
        // SAFETY: the handle is live, and `block` is 16 writable bytes.
        unsafe { rind_fips_aes_encrypt_block(self.handle.ptr(), block) }
    }
}

impl fmt::Debug for Aes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Aes")
            .field("algorithm", self.algorithm)
            .finish_non_exhaustive()
    }
}

/// An AES key for counter mode, with a counter width fixed when it is made;
/// held in the module, which wipes it on drop.
///
/// Each call takes a 16-byte counter block whose rightmost `counter_bits` bits
/// are a big-endian counter, incremented per block and wrapping within those
/// bits, as WebCrypto's AES-CTR defines it. RFC 3686 uses 32 bits; SRTP's
/// AES-CM, whose IVs leave their low 16 bits zero for at most 2^16 blocks,
/// works with any width of at least 16; pyca's and aws-lc-rs's CTR use 128.
/// Counter mode is unauthenticated, so pair it with a MAC.
pub struct AesCtr {
    algorithm: &'static Algorithm,
    handle: Handle<AesCtrKey>,
}

impl AesCtr {
    /// Expands `key` for `algorithm`, counting over the rightmost
    /// `counter_bits` bits of each counter block.
    ///
    /// Fails with [`Error::WrongLength`] if `key` is not that algorithm's key
    /// length, or if `counter_bits` is not 1 to 128.
    pub fn new(algorithm: &'static Algorithm, key: &[u8], counter_bits: u8) -> Result<Self, Error> {
        let handle = new_handle(|out| {
            // SAFETY: `key` is readable, and `out` writable.
            unsafe {
                rind_fips_aes_ctr_new(algorithm.id(), key.as_ptr(), key.len(), counter_bits, out)
            }
        })?;
        Ok(Self { algorithm, handle })
    }

    /// XORs the keystream from `counter_block` into `inout`.
    ///
    /// Encryption and decryption are the same operation. The counter block is
    /// not secret. Each call starts at a whole block, so a stream split after
    /// a length that is not a multiple of 16 cannot resume mid-block: passing
    /// that partial block's counter block again reuses keystream.
    ///
    /// Fails with [`Error::WrongLength`], leaving `inout` unchanged, if
    /// `inout` needs more than 2^`counter_bits` blocks: the counter would wrap
    /// onto a block already used, repeating keystream.
    pub fn apply_keystream(&self, counter_block: &[u8; 16], inout: &mut [u8]) -> Result<(), Error> {
        // SAFETY: the handle is live, `counter_block` is 16 readable bytes,
        // and `inout` writable.
        ffi::check(unsafe {
            rind_fips_aes_ctr_apply(
                self.handle.ptr(),
                counter_block,
                inout.as_mut_ptr(),
                inout.len(),
            )
        })
    }
}

impl fmt::Debug for AesCtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AesCtr")
            .field("algorithm", self.algorithm)
            .finish_non_exhaustive()
    }
}

/// An AES key that encrypts in CBC mode, as WebCrypto's AES-CBC, pyca's
/// `modes.CBC`, and Dart's `AesCbc` do; held in the module, which wipes it
/// on drop.
///
/// CBC is unauthenticated, so anyone who can alter a ciphertext and learn
/// whether it decrypted can decrypt it: Vaudenay's padding oracle needs only
/// that error, however it surfaces. Send a MAC over the IV and ciphertext
/// with each message, as encrypt-then-MAC and RFC 7518's `A128CBC-HS256`
/// do, or use [`crate::aead`] instead.
///
/// Each message needs a fresh [`CbcIv`], normally [`CbcIv::random`]: an IV
/// an attacker can predict, such as a counter, leaks whether a plaintext
/// block equals one they chose.
pub struct AesCbcEncryptingKey {
    algorithm: &'static Algorithm,
    handle: Handle<AesCbcEncrypting>,
}

impl AesCbcEncryptingKey {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not that algorithm's key length.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        let handle = new_handle(|out| {
            // SAFETY: `key` is readable, and `out` writable.
            unsafe {
                rind_fips_aes_cbc_encrypting_new(algorithm.id(), key.as_ptr(), key.len(), out)
            }
        })?;
        Ok(Self { algorithm, handle })
    }

    /// Pads `in_out` with PKCS#7, 1 to 16 bytes each holding the count, and
    /// encrypts it in place under `iv`.
    ///
    /// Fails with [`Error::WrongLength`], leaving it padded but unencrypted,
    /// if `in_out` is a buffer whose `extend` does not grow what `as_mut`
    /// returns to whole blocks, as aws-lc-rs's `encrypt` refuses it.
    pub fn encrypt<InOut>(&self, iv: CbcIv, in_out: &mut InOut) -> Result<(), Error>
    where
        InOut: AsMut<[u8]> + for<'a> Extend<&'a u8>,
    {
        let pad = 16 - in_out.as_mut().len() % 16;
        in_out.extend(&[pad as u8; 16][..pad]);
        self.encrypt_blocks(iv, in_out.as_mut())
    }

    /// Encrypts `in_out` in place under `iv`, without padding.
    ///
    /// Fails with [`Error::WrongLength`], leaving `in_out` unchanged, if
    /// `in_out` is not a whole number of 16-byte blocks.
    pub fn encrypt_blocks(&self, iv: CbcIv, in_out: &mut [u8]) -> Result<(), Error> {
        // SAFETY: the handle is live, `iv` is 16 readable bytes, and
        // `in_out` writable.
        ffi::check(unsafe {
            rind_fips_aes_cbc_encrypt_blocks(
                self.handle.ptr(),
                &iv.0,
                in_out.as_mut_ptr(),
                in_out.len(),
            )
        })
    }
}

impl fmt::Debug for AesCbcEncryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AesCbcEncryptingKey")
            .field("algorithm", self.algorithm)
            .finish_non_exhaustive()
    }
}

/// A CBC IV that encrypts one message: random, or one the caller promises an
/// attacker cannot predict.
///
/// It is not `Clone`, so one value encrypts at most one message. Read it with
/// [`CbcIv::as_bytes`] before encrypting to send it alongside the ciphertext.
pub struct CbcIv([u8; 16]);

impl CbcIv {
    /// Draws an IV from the module's DRBG.
    ///
    /// Fails with [`Error::RngFailed`] if the DRBG does.
    pub fn random() -> Result<Self, Error> {
        let mut iv = [0; 16];
        crate::rand::fill(&mut iv)?;
        Ok(Self(iv))
    }

    /// Wraps `iv`, which the caller promises an attacker cannot predict:
    /// never a constant, zero, or counter.
    pub fn assume_unpredictable(iv: [u8; 16]) -> Self {
        Self(iv)
    }

    /// The IV's bytes, which the receiver needs to decrypt.
    pub fn as_bytes(&self) -> &[u8; 16] {
        &self.0
    }
}

impl fmt::Debug for CbcIv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("CbcIv").finish_non_exhaustive()
    }
}

/// An AES key that decrypts in CBC mode; held in the module, which wipes it
/// on drop.
///
/// Decryption is unauthenticated: check the MAC over the IV and ciphertext
/// before decrypting, and never let a sender learn that decryption failed,
/// or the error is a padding oracle. See [`AesCbcEncryptingKey`].
pub struct AesCbcDecryptingKey {
    algorithm: &'static Algorithm,
    handle: Handle<AesCbcDecrypting>,
}

impl AesCbcDecryptingKey {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not that algorithm's key length.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        let handle = new_handle(|out| {
            // SAFETY: `key` is readable, and `out` writable.
            unsafe {
                rind_fips_aes_cbc_decrypting_new(algorithm.id(), key.as_ptr(), key.len(), out)
            }
        })?;
        Ok(Self { algorithm, handle })
    }

    /// Decrypts `in_out` in place under `iv`, checks and removes its PKCS#7
    /// padding, and returns the plaintext at its front.
    ///
    /// Fails with [`Error::DecryptFailed`], leaving `in_out` unchanged, if it
    /// is empty or not a whole number of 16-byte blocks, and clearing it if
    /// its padding is malformed. The padding check runs in constant time.
    pub fn decrypt<'a>(&self, iv: &[u8; 16], in_out: &'a mut [u8]) -> Result<&'a mut [u8], Error> {
        let mut len = 0;
        // SAFETY: the handle is live, `iv` is 16 readable bytes, `in_out`
        // writable, and `len` writable.
        ffi::check(unsafe {
            rind_fips_aes_cbc_decrypt(
                self.handle.ptr(),
                iv,
                in_out.as_mut_ptr(),
                in_out.len(),
                &mut len,
            )
        })?;
        Ok(&mut in_out[..len])
    }

    /// Decrypts `in_out` in place under `iv`, without padding.
    ///
    /// Fails with [`Error::DecryptFailed`], leaving `in_out` unchanged, if
    /// `in_out` is not a whole number of 16-byte blocks.
    pub fn decrypt_blocks(&self, iv: &[u8; 16], in_out: &mut [u8]) -> Result<(), Error> {
        // SAFETY: the handle is live, `iv` is 16 readable bytes, and
        // `in_out` writable.
        ffi::check(unsafe {
            rind_fips_aes_cbc_decrypt_blocks(
                self.handle.ptr(),
                iv,
                in_out.as_mut_ptr(),
                in_out.len(),
            )
        })
    }
}

impl fmt::Debug for AesCbcDecryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AesCbcDecryptingKey")
            .field("algorithm", self.algorithm)
            .finish_non_exhaustive()
    }
}
