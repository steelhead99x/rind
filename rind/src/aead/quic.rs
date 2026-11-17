// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::Error;
use crate::cipher::{self, Aes, ChaCha20};
use crate::low::{Zeroable, ZeroableRef, zeroise_value};

/// The length of a header-protection sample, in bytes, for every algorithm.
pub const SAMPLE_LEN: usize = 16;

/// A header-protection cipher, which fixes the key length a key must have.
pub struct Algorithm {
    id: AlgorithmId,
    // The only path to the cipher's code, so a binary links only the ciphers
    // whose algorithms it names.
    new: fn(&[u8]) -> Result<Key, Error>,
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Algorithm").field("id", &self.id).finish()
    }
}

#[derive(Debug)]
enum AlgorithmId {
    Aes128,
    Aes256,
    ChaCha20,
}

impl Algorithm {
    /// The length of a key, in bytes.
    pub fn key_len(&self) -> usize {
        match self.id {
            AlgorithmId::Aes128 => 16,
            AlgorithmId::Aes256 | AlgorithmId::ChaCha20 => 32,
        }
    }
}

/// AES-128 header protection, which QUIC pairs with AES-128-GCM.
pub static AES_128: Algorithm = Algorithm {
    id: AlgorithmId::Aes128,
    new: |key| Ok(Key::Aes(Masker::new(Aes::new(&cipher::AES_128, key)?))),
};

/// AES-256 header protection, which QUIC pairs with AES-256-GCM.
pub static AES_256: Algorithm = Algorithm {
    id: AlgorithmId::Aes256,
    new: |key| Ok(Key::Aes(Masker::new(Aes::new(&cipher::AES_256, key)?))),
};

/// ChaCha20 header protection, which QUIC pairs with ChaCha20-Poly1305.
pub static CHACHA20: Algorithm = Algorithm {
    id: AlgorithmId::ChaCha20,
    new: |key| {
        let key = key.try_into().map_err(|_| Error::WrongLength)?;
        Ok(Key::ChaCha20(Masker::new(ChaCha20::new(key))))
    },
};

/// A header-protection key, expanded once for its algorithm and wiped on drop.
pub struct HeaderProtectionKey(Key);

impl HeaderProtectionKey {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not [`Algorithm::key_len`] bytes.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        Ok(Self((algorithm.new)(key)?))
    }

    /// Computes the mask for `sample`: its first byte masks the packet's first
    /// byte, and the rest mask the packet number.
    pub fn mask(&self, sample: &[u8; SAMPLE_LEN]) -> [u8; 5] {
        match &self.0 {
            Key::Aes(key) => key.mask(sample),
            Key::ChaCha20(key) => key.mask(sample),
        }
    }
}

impl fmt::Debug for HeaderProtectionKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // An id, not the static, so formatting links no other cipher's code.
        let algorithm = match &self.0 {
            Key::Aes(masker) if masker.key.key_len() == 16 => AlgorithmId::Aes128,
            Key::Aes(_) => AlgorithmId::Aes256,
            Key::ChaCha20(_) => AlgorithmId::ChaCha20,
        };
        f.debug_struct("HeaderProtectionKey")
            .field("algorithm", &algorithm)
            .finish_non_exhaustive()
    }
}

/// A key with its cipher's mask, which it reaches only through `mask`:
/// matching on [`Key`] then names no cipher's code.
struct Masker<C: Mask> {
    key: C,
    mask: ZeroableRef<MaskFn<C>>,
}

type MaskFn<C> = fn(&C, &[u8; SAMPLE_LEN]) -> [u8; 5];

impl<C: Mask> Masker<C> {
    fn new(key: C) -> Self {
        Self {
            key,
            mask: ZeroableRef::new(const { &(C::mask as MaskFn<C>) }),
        }
    }

    fn mask(&self, sample: &[u8; SAMPLE_LEN]) -> [u8; 5] {
        (self.mask.get())(&self.key, sample)
    }
}

/// A cipher that masks QUIC headers.
trait Mask: 'static {
    fn mask(&self, sample: &[u8; SAMPLE_LEN]) -> [u8; 5];
}

impl Mask for Aes {
    fn mask(&self, sample: &[u8; SAMPLE_LEN]) -> [u8; 5] {
        self.header_protection_mask(sample)
    }
}

impl Mask for ChaCha20 {
    fn mask(&self, sample: &[u8; SAMPLE_LEN]) -> [u8; 5] {
        self.header_protection_mask(sample)
    }
}

// All-zero is the `Aes` variant with an all-zero key and a `None`
// `ZeroableRef`, which `Zeroable` requires to be valid: every other field is a
// plain integer or vector.
//
// Boxing the AES key schedule would allocate for every key to save space only
// on ChaCha20 keys; the 32-bit arm schedule is small, so the lint is allowed
// rather than expected.
#[allow(clippy::large_enum_variant)]
#[repr(u8)]
enum Key {
    Aes(Masker<Aes>),
    ChaCha20(Masker<ChaCha20>),
}

impl Drop for Key {
    fn drop(&mut self) {
        // Wipes the discriminant and the space a smaller variant leaves unused,
        // not only the variant's own key.
        zeroise_value(self);
    }
}

impl Zeroable for Key {}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn key_length_must_match_algorithm() {
        let key = [0u8; 33];
        for algorithm in [&AES_128, &AES_256, &CHACHA20] {
            for len in 0..=key.len() {
                assert_eq!(
                    HeaderProtectionKey::new(algorithm, &key[..len]).is_ok(),
                    len == algorithm.key_len(),
                    "{algorithm:?} len {len}"
                );
            }
        }
    }

    #[test]
    fn rfc9001() {
        // Appendices A.2 and A.3 (AES-128) and A.5 (ChaCha20).
        for (algorithm, key, sample, mask) in [
            (
                &AES_128,
                "9f50449e04a0e810283a1e9933adedd2",
                "d1b1c98dd7689fb8ec11d242b123dc9b",
                "437b9aec36",
            ),
            (
                &AES_128,
                "c206b8d9b9f0f37644430b490eeaa314",
                "2cd0991cd25b0aac406a5816b6394100",
                "2ec0d8356a",
            ),
            (
                &CHACHA20,
                "25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4",
                "5e5cd55c41f69080575d7999c25a5bfb",
                "aefefe7d03",
            ),
        ] {
            let key = HeaderProtectionKey::new(algorithm, &hex::decode(key).unwrap()).unwrap();
            let sample = hex::decode(sample).unwrap().try_into().unwrap();
            assert_eq!(hex::encode(key.mask(&sample)), mask);
        }
    }
}
