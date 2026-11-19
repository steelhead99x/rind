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

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::arm::aes_neon::{NeonDecKey, NeonKey};
    use crate::low::arm::cpu::HaveNeon;
    use crate::low::portable::aes as portable_aes;

    // The NEON path's CBC, which encrypts block by block and decrypts with
    // bitsliced AES in batches of eight, against the portable code at lengths
    // around those batches, for each key size.
    #[test]
    fn neon_matches_portable() {
        let Some(token) = HaveNeon::check() else {
            return;
        };
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for key_len in [16, 24, 32] {
            let raw = bytes(key_len, 5);
            let (enc, dec) = (NeonKey::new(&raw, token), NeonDecKey::new(&raw, token));
            let (want_enc, want_dec) = (
                AesKey::Portable(portable_aes::AesKey::new(&raw)),
                AesDecKey::Portable(portable_aes::AesDecKey::new(&raw)),
            );
            let iv: [u8; 16] = bytes(16, 9).try_into().unwrap();
            for blocks in (0..=19).chain([31, 32, 33, 100]) {
                let plain = bytes(16 * blocks, blocks as u32);
                let (plain, _) = plain.as_chunks::<16>();

                let (mut got, mut want) = (plain.to_vec(), plain.to_vec());
                enc.cbc_encrypt(&iv, &mut got);
                encrypt(&want_enc, &iv, &mut want);
                assert_eq!(got, want, "{key_len}-byte key, {blocks} blocks, encrypt");

                dec.cbc_decrypt(&iv, &mut got);
                assert_eq!(got, plain, "{key_len}-byte key, {blocks} blocks, decrypt");
                decrypt(&want_dec, &iv, &mut want);
                assert_eq!(want, plain);
            }
        }
    }
}
