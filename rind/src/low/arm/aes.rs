// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES on the crypto extension where the CPU has it, and the portable
//! backend's bitsliced AES otherwise.

use super::aesv8_armx::{AesHwDecKey, AesHwKey};
use super::cpu::HaveCryptoExt;
use crate::low::{self, portable::aes as portable};

// Keep all-zero valid when drop wipes the whole enum. A process only ever
// builds one variant, so boxing the bitsliced round keys would buy nothing.
#[repr(u8)]
#[expect(clippy::large_enum_variant)]
pub(crate) enum AesKey {
    Portable(portable::AesKey),
    /// The crypto extension's, which the key picks when the CPU has it.
    Hw(AesHwKey),
}

impl AesKey {
    /// Expands `key`, which must be 16, 24, or 32 bytes.
    pub(crate) fn new(key: &[u8]) -> Self {
        match HaveCryptoExt::check() {
            Some(token) => Self::Hw(AesHwKey::new(key, token)),
            None => Self::Portable(portable::AesKey::new(key)),
        }
    }

    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        match self {
            Self::Portable(key) => key.encrypt_block(block),
            Self::Hw(key) => key.encrypt_block(block),
        }
    }

    /// The key's length in bytes, 16, 24, or 32, which no API reads but
    /// `Debug`.
    pub(crate) fn key_len(&self) -> usize {
        match self {
            Self::Portable(key) => key.key_len(),
            Self::Hw(key) => key.key_len(),
        }
    }
}

impl Drop for AesKey {
    fn drop(&mut self) {
        // The active key's drop cannot clear the enum's unused storage.
        low::zeroise_value(self);
    }
}

impl low::Zeroable for AesKey {}

/// An AES key that decrypts, on the path [`AesKey`] picks for the CPU.
#[repr(u8)]
#[expect(clippy::large_enum_variant)]
pub(crate) enum AesDecKey {
    Portable(portable::AesDecKey),
    Hw(AesHwDecKey),
}

impl AesDecKey {
    /// Expands `key`, which must be 16, 24, or 32 bytes.
    pub(crate) fn new(key: &[u8]) -> Self {
        match HaveCryptoExt::check() {
            Some(token) => Self::Hw(AesHwDecKey::new(key, token)),
            None => Self::Portable(portable::AesDecKey::new(key)),
        }
    }

    pub(crate) fn decrypt_block(&self, inout: &mut [u8; 16]) {
        match self {
            Self::Portable(key) => key.decrypt_block(inout),
            Self::Hw(key) => key.decrypt_block(inout),
        }
    }
}

impl Drop for AesDecKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::Zeroable for AesDecKey {}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::aes_ctr;

    #[test]
    fn key_len() {
        for key in [&[0u8; 16][..], &[0u8; 24], &[0u8; 32]] {
            assert_eq!(AesKey::new(key).key_len(), key.len());
            if let Some(token) = HaveCryptoExt::check() {
                assert_eq!(AesKey::Hw(AesHwKey::new(key, token)).key_len(), key.len());
            }
        }
    }

    // Every other test sees only the path the CPU picks, so the crypto
    // extension's AES is checked against the portable code here: each key
    // size, single blocks, and counter mode across the 32-bit counter's wrap.
    #[test]
    fn hw_matches_portable() {
        let Some(token) = HaveCryptoExt::check() else {
            return;
        };
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for (key_len, seed) in [16, 24, 32].into_iter().zip(1..) {
            let key = bytes(key_len, seed);
            let portable = AesKey::Portable(portable::AesKey::new(&key));
            let hw = AesKey::Hw(AesHwKey::new(&key, token));

            let block: [u8; 16] = bytes(16, seed).try_into().unwrap();
            assert_eq!(
                hw.encrypt_block(&block),
                portable.encrypt_block(&block),
                "{key_len}-byte key block"
            );

            let nonce = bytes(12, seed).try_into().unwrap();
            for counter in [0, 1, u32::MAX - 3, u32::MAX] {
                for len in [1, 15, 16, 17, 127, 128, 129, 300] {
                    let mut want = bytes(len, counter);
                    let mut got = want.clone();
                    aes_ctr::apply(&portable, &nonce, counter, &mut want);
                    aes_ctr::apply(&hw, &nonce, counter, &mut got);
                    assert_eq!(
                        got, want,
                        "{key_len}-byte key, counter {counter}, {len} bytes"
                    );
                }
            }
        }
    }

    // Each decryption path the CPU offers must invert encryption, which the
    // tests above hold to AES on every path.
    #[test]
    fn every_path_decrypts() {
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for (key_len, seed) in [16, 24, 32].into_iter().zip(1..) {
            let key = bytes(key_len, seed);
            let enc = AesKey::new(&key);
            let mut paths = vec![AesDecKey::Portable(portable::AesDecKey::new(&key))];
            if let Some(token) = HaveCryptoExt::check() {
                paths.push(AesDecKey::Hw(AesHwDecKey::new(&key, token)));
            }
            for block_seed in 0..4 {
                let block: [u8; 16] = bytes(16, block_seed).try_into().unwrap();
                let ct = enc.encrypt_block(&block);
                for (i, dec) in paths.iter().enumerate() {
                    let mut pt = ct;
                    dec.decrypt_block(&mut pt);
                    assert_eq!(
                        pt, block,
                        "{key_len}-byte key, path {i}, block {block_seed}"
                    );
                }
            }
        }
    }
}
