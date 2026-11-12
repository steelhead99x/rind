// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES for the portable backend and armv7 without the crypto extension:
//! aws-lc's bitsliced AES, several blocks a pass, with the round keys held
//! bitsliced so each call skips that step.

use super::aes_nohw::{NohwKey, Schedule};
use crate::low;

/// An AES key that encrypts.
pub(crate) struct AesKey(Schedule);

impl AesKey {
    /// Expands `key`, which must be 16, 24, or 32 bytes.
    pub(crate) fn new(key: &[u8]) -> Self {
        Self(NohwKey::new(key).schedule())
    }

    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        self.0.encrypt_block(block)
    }

    /// XORs counter-mode keystream into `inout`, whose last block may be
    /// partial.
    ///
    /// The counter blocks are `ivec`, then `ivec` with its last four bytes,
    /// a big-endian counter, incremented with 32-bit wrapping.
    pub(crate) fn ctr32(&self, ivec: &[u8; 16], inout: &mut [u8]) {
        self.0.ctr32(ivec, inout);
    }

    /// Encrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`.
    pub(crate) fn cbc_encrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        self.0.cbc_encrypt(iv, blocks);
    }

    /// The key's length in bytes, 16, 24, or 32, which no API reads but
    /// `Debug`.
    pub(crate) fn key_len(&self) -> usize {
        self.0.key_len()
    }
}

impl Drop for AesKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::Zeroable for AesKey {}

/// An AES key that decrypts. The inverse cipher runs the encryption round
/// keys backwards.
pub(crate) struct AesDecKey(Schedule);

impl AesDecKey {
    /// Expands `key`, which must be 16, 24, or 32 bytes.
    pub(crate) fn new(key: &[u8]) -> Self {
        Self(NohwKey::new(key).schedule())
    }

    pub(crate) fn decrypt_block(&self, inout: &mut [u8; 16]) {
        self.0.decrypt_block(inout);
    }

    /// Decrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`.
    pub(crate) fn cbc_decrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        self.0.cbc_decrypt(iv, blocks);
    }
}

impl Drop for AesDecKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::Zeroable for AesDecKey {}
