// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::aes::{AesDecKey, AesKey};
use crate::low::portable::aes_cbc as portable;

/// Encrypts whole blocks in place in CBC mode, the first chained from `iv`.
pub(crate) fn encrypt(key: &AesKey, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
    match key {
        AesKey::Hw(key) => key.cbc_encrypt(iv, blocks),
        AesKey::Neon(key) => key.cbc_encrypt(iv, blocks),
        AesKey::Portable(key) => portable::encrypt(key, iv, blocks),
    }
}

/// Decrypts whole blocks in place in CBC mode, the first chained from `iv`.
pub(crate) fn decrypt(key: &AesDecKey, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
    match key {
        AesDecKey::Hw(key) => key.cbc_decrypt(iv, blocks),
        AesDecKey::Neon(key) => key.cbc_decrypt(iv, blocks),
        AesDecKey::Portable(key) => portable::decrypt(key, iv, blocks),
    }
}
