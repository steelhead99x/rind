// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES on the crypto extension where the CPU has it, on NEON alone where it
//! has only that, and the portable backend's bitsliced AES otherwise.

use super::aesv8_armx::{AesHwDecKey, AesHwKey};
use super::cpu::{HaveCryptoExt, HaveNeon};
use super::vpaes_armv7::{NeonDecKey, NeonKey};
use crate::low::{self, portable::aes as portable};

// Keep all-zero valid when drop wipes the whole enum.
#[repr(u8)]
pub(crate) enum AesKey {
    Portable(portable::AesKey),
    /// NEON's, which the key picks when the CPU has it but not the crypto
    /// extension.
    Neon(NeonKey),
    /// The crypto extension's, which the key picks when the CPU has it.
    Hw(AesHwKey),
}

impl AesKey {
    /// Expands `key`, which must be 16, 24, or 32 bytes.
    pub(crate) fn new(key: &[u8]) -> Self {
        if let Some(token) = HaveCryptoExt::check() {
            return Self::Hw(AesHwKey::new(key, token));
        }
        match HaveNeon::check() {
            Some(token) => Self::Neon(NeonKey::new(key, token)),
            None => Self::Portable(portable::AesKey::new(key)),
        }
    }

    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        match self {
            Self::Portable(key) => key.encrypt_block(block),
            Self::Neon(key) => key.encrypt_block(block),
            Self::Hw(key) => key.encrypt_block(block),
        }
    }

    /// The key's length in bytes, 16, 24, or 32, which no API reads but
    /// `Debug`.
    pub(crate) fn key_len(&self) -> usize {
        match self {
            Self::Portable(key) => key.key_len(),
            Self::Neon(key) => key.key_len(),
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
pub(crate) enum AesDecKey {
    Portable(portable::AesDecKey),
    Neon(NeonDecKey),
    Hw(AesHwDecKey),
}

impl AesDecKey {
    /// Expands `key`, which must be 16, 24, or 32 bytes.
    pub(crate) fn new(key: &[u8]) -> Self {
        if let Some(token) = HaveCryptoExt::check() {
            return Self::Hw(AesHwDecKey::new(key, token));
        }
        match HaveNeon::check() {
            Some(token) => Self::Neon(NeonDecKey::new(key, token)),
            None => Self::Portable(portable::AesDecKey::new(key)),
        }
    }

    pub(crate) fn decrypt_block(&self, inout: &mut [u8; 16]) {
        match self {
            Self::Portable(key) => key.decrypt_block(inout),
            Self::Neon(key) => key.decrypt_block(inout),
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
    use crate::low::{aes_cbc, aes_ctr, ct};

    fn bytes(n: usize, seed: u32) -> Vec<u8> {
        (0..n as u32)
            .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect()
    }

    /// Every encryption path the CPU offers, the portable one first.
    fn enc_paths(key: &[u8]) -> Vec<AesKey> {
        let mut paths = vec![AesKey::Portable(portable::AesKey::new(key))];
        if let Some(token) = HaveNeon::check() {
            paths.push(AesKey::Neon(NeonKey::new(key, token)));
        }
        if let Some(token) = HaveCryptoExt::check() {
            paths.push(AesKey::Hw(AesHwKey::new(key, token)));
        }
        paths
    }

    /// Every decryption path the CPU offers, the portable one first.
    fn dec_paths(key: &[u8]) -> Vec<AesDecKey> {
        let mut paths = vec![AesDecKey::Portable(portable::AesDecKey::new(key))];
        if let Some(token) = HaveNeon::check() {
            paths.push(AesDecKey::Neon(NeonDecKey::new(key, token)));
        }
        if let Some(token) = HaveCryptoExt::check() {
            paths.push(AesDecKey::Hw(AesHwDecKey::new(key, token)));
        }
        paths
    }

    #[test]
    fn key_len() {
        for key in [&[0u8; 16][..], &[0u8; 24], &[0u8; 32]] {
            assert_eq!(AesKey::new(key).key_len(), key.len());
            for path in enc_paths(key) {
                assert_eq!(path.key_len(), key.len());
            }
        }
    }

    // Every other test sees only the path the CPU picks, so the NEON and
    // crypto extension AES are checked against the portable code here: each
    // key size, single blocks, and counter mode and CBC around NEON's
    // eight-block batches and the six-block tail bsaes takes, across the
    // 32-bit counter's wrap. The key and data are secret, so under
    // `admin/ctgrind` this also checks that each path valgrind can run is
    // constant time in them.
    #[test]
    fn paths_match_portable() {
        let lens = [
            1, 15, 16, 17, 95, 96, 112, 127, 128, 129, 200, 223, 224, 300, 368,
        ];
        for (key_len, seed) in [16, 24, 32].into_iter().zip(1..) {
            let key = bytes(key_len, seed);
            ct::secret_slice(&key);
            let mut enc = enc_paths(&key);
            let portable = enc.remove(0);
            let mut dec = dec_paths(&key);
            let portable_dec = dec.remove(0);

            let block: [u8; 16] = bytes(16, seed).try_into().unwrap();
            let secret = block;
            ct::secret_slice(&secret);
            let want = portable.encrypt_block(&secret);
            ct::public_slice(&want);
            for (i, path) in enc.iter().enumerate() {
                let got = path.encrypt_block(&secret);
                ct::public_slice(&got);
                assert_eq!(got, want, "{key_len}-byte key block, path {i}");
            }
            // Each decryption path inverts it.
            for (i, path) in dec.iter().chain([&portable_dec]).enumerate() {
                let mut got = want;
                ct::secret_slice(&got);
                path.decrypt_block(&mut got);
                ct::public_slice(&got);
                assert_eq!(got, block, "{key_len}-byte key, decryption {i}");
            }

            let nonce = bytes(12, seed).try_into().unwrap();
            for counter in [0, 1, u32::MAX - 3, u32::MAX] {
                for len in lens {
                    let mut want = bytes(len, counter);
                    ct::secret_slice(&want);
                    let mut got = vec![0; len];
                    aes_ctr::apply(&portable, &nonce, counter, &mut want);
                    ct::public_slice(&want);
                    for (i, path) in enc.iter().enumerate() {
                        got.copy_from_slice(&bytes(len, counter));
                        ct::secret_slice(&got);
                        aes_ctr::apply(path, &nonce, counter, &mut got);
                        ct::public_slice(&got);
                        assert_eq!(
                            got, want,
                            "{key_len}-byte key, path {i}, counter {counter}, {len} bytes"
                        );
                    }
                }
            }

            let iv: [u8; 16] = bytes(16, seed + 7).try_into().unwrap();
            for blocks in lens.map(|len| len.div_ceil(16)) {
                let plain: Vec<[u8; 16]> = bytes(16 * blocks, seed).as_chunks().0.to_vec();
                let mut want = plain.clone();
                ct::secret_slice(&want);
                aes_cbc::encrypt(&portable, &iv, &mut want);
                ct::public_slice(&want);
                for (i, path) in enc.iter().enumerate() {
                    let mut got = plain.clone();
                    ct::secret_slice(&got);
                    aes_cbc::encrypt(path, &iv, &mut got);
                    ct::public_slice(&got);
                    assert_eq!(got, want, "{key_len}-byte key, path {i}, {blocks} blocks");
                }
                for (i, path) in dec.iter().chain([&portable_dec]).enumerate() {
                    let mut got = want.clone();
                    ct::secret_slice(&got);
                    aes_cbc::decrypt(path, &iv, &mut got);
                    ct::public_slice(&got);
                    assert_eq!(
                        got, plain,
                        "{key_len}-byte key, decryption {i}, {blocks} blocks"
                    );
                }
            }
        }
    }
}
