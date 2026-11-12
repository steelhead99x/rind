// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::aes::{AesDecKey, AesKey};

/// Encrypts whole blocks in place in CBC mode, the first chained from `iv`.
pub(crate) fn encrypt(key: &AesKey, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
    key.cbc_encrypt(iv, blocks);
}

/// Decrypts whole blocks in place in CBC mode, the first chained from `iv`.
pub(crate) fn decrypt(key: &AesDecKey, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
    key.cbc_decrypt(iv, blocks);
}
