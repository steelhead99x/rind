//! QUIC header protection (RFC 9001).

use core::fmt;

use crate::{error, hkdf};

/// A header-protection sample.
pub type Sample = [u8; SAMPLE_LEN];

const SAMPLE_LEN: usize = rind::aead::quic::SAMPLE_LEN;

/// A header-protection cipher, chosen by one of this module's constants.
pub struct Algorithm {
    id: AlgorithmId,
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AlgorithmId {
    AES_128,
    AES_256,
    CHACHA20,
}

impl Algorithm {
    /// The length of a key, in bytes.
    pub fn key_len(&self) -> usize {
        self.rind().key_len()
    }

    /// The length of a sample, in bytes.
    pub fn sample_len(&self) -> usize {
        SAMPLE_LEN
    }

    fn rind(&self) -> &'static rind::aead::quic::Algorithm {
        match self.id {
            AlgorithmId::AES_128 => &rind::aead::quic::AES_128,
            AlgorithmId::AES_256 => &rind::aead::quic::AES_256,
            AlgorithmId::CHACHA20 => &rind::aead::quic::CHACHA20,
        }
    }
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl PartialEq for Algorithm {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Algorithm {}

/// A header-protection key is [`Algorithm::key_len`] bytes.
impl hkdf::KeyType for &'static Algorithm {
    fn len(&self) -> usize {
        self.key_len()
    }
}

/// AES-128 header protection.
pub const AES_128: Algorithm = Algorithm {
    id: AlgorithmId::AES_128,
};

/// AES-256 header protection.
pub const AES_256: Algorithm = Algorithm {
    id: AlgorithmId::AES_256,
};

/// ChaCha20 header protection.
pub const CHACHA20: Algorithm = Algorithm {
    id: AlgorithmId::CHACHA20,
};

/// A header-protection key; wiped on drop.
pub struct HeaderProtectionKey {
    key: rind::aead::quic::HeaderProtectionKey,
    algorithm: &'static Algorithm,
}

impl HeaderProtectionKey {
    /// Expands `key_bytes` for `algorithm`, failing unless it is [`Algorithm::key_len`] bytes.
    pub fn new(
        algorithm: &'static Algorithm,
        key_bytes: &[u8],
    ) -> Result<Self, error::Unspecified> {
        Ok(Self {
            key: rind::aead::quic::HeaderProtectionKey::new(algorithm.rind(), key_bytes)
                .map_err(error::unspecified)?,
            algorithm,
        })
    }

    /// Returns the five-byte mask for `sample`, failing unless it is a sample's length.
    pub fn new_mask(&self, sample: &[u8]) -> Result<[u8; 5], error::Unspecified> {
        Ok(self.key.mask(sample.try_into()?))
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }
}

impl From<hkdf::Okm<'_, &'static Algorithm>> for HeaderProtectionKey {
    fn from(okm: hkdf::Okm<'_, &'static Algorithm>) -> Self {
        let algorithm = *okm.len();
        let mut key = [0u8; 32];
        let key = &mut key[..algorithm.key_len()];
        okm.fill_exact(key);
        Self::new(algorithm, key).expect("key_len bytes are a valid key")
    }
}
