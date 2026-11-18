use std::fmt;

use dimpl::crypto::{
    Aad, Buf, Cipher, Dtls12CipherSuite, Dtls13CipherSuite, HashAlgorithm, Nonce,
    SupportedDtls12CipherSuite, SupportedDtls13CipherSuite, TmpBuf,
};
use dimpl::{CryptoError, CryptoOperation};
use rind::aead;
use rind::cipher::{self, Aes, ChaCha20};

const TAG_LEN: usize = 16;

/// The AEAD behind a suite, shared by its DTLS 1.2 and 1.3 forms.
#[derive(Debug, Clone, Copy)]
enum Algorithm {
    Aes128Gcm,
    Aes256Gcm,
    ChaCha20Poly1305,
}

impl Algorithm {
    fn aead(self) -> &'static aead::Algorithm {
        match self {
            Self::Aes128Gcm => &aead::AES_128_GCM,
            Self::Aes256Gcm => &aead::AES_256_GCM,
            Self::ChaCha20Poly1305 => &aead::CHACHA20_POLY1305,
        }
    }

    fn cipher(self, key: &[u8]) -> Result<Box<dyn Cipher>, CryptoError> {
        let actual = key.len().min(u16::MAX as usize) as u16;
        let key = aead::Key::new(self.aead(), key).map_err(|_| match self {
            Self::Aes128Gcm | Self::Aes256Gcm => CryptoError::InvalidAesGcmKeySize { actual },
            Self::ChaCha20Poly1305 => CryptoError::InvalidChacha20Poly1305KeySize { actual },
        })?;
        Ok(Box::new(Aead(key)))
    }

    /// DTLS 1.3 record number protection (RFC 9147 section 4.2.3).
    fn mask(self, sn_key: &[u8], sample: &[u8; 16]) -> [u8; 16] {
        // dimpl derives `sn_key` at the suite's key length.
        let aes = |algorithm| {
            let mut mask = *sample;
            Aes::new(algorithm, sn_key)
                .expect("sn_key is the suite's AES key length")
                .encrypt_block(&mut mask);
            mask
        };
        match self {
            Self::Aes128Gcm => aes(&cipher::AES_128),
            Self::Aes256Gcm => aes(&cipher::AES_256),
            Self::ChaCha20Poly1305 => {
                let key = sn_key.try_into().expect("sn_key is a ChaCha20 key length");
                let [c0, c1, c2, c3, nonce @ ..] = sample;
                let counter = u32::from_le_bytes([*c0, *c1, *c2, *c3]);
                let mut mask = [0u8; 16];
                ChaCha20::new(key)
                    .apply_keystream(nonce, counter, &mut mask)
                    .expect("one block never wraps the counter");
                mask
            }
        }
    }
}

struct Aead(aead::Key);

impl fmt::Debug for Aead {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Aead")
    }
}

impl Cipher for Aead {
    fn encrypt(&mut self, plaintext: &mut Buf, aad: Aad, nonce: Nonce) -> Result<(), CryptoError> {
        self.0
            .seal_in_place_append_tag(aead::Nonce::assume_unique_for_key(nonce.0), &aad, plaintext)
            .map_err(|_| CryptoError::OperationFailed(CryptoOperation::Encrypt))
    }

    fn decrypt(
        &mut self,
        ciphertext: &mut TmpBuf,
        aad: Aad,
        nonce: Nonce,
    ) -> Result<(), CryptoError> {
        let len = ciphertext.len();
        let Some(plaintext_len) = len.checked_sub(TAG_LEN) else {
            return Err(CryptoError::CiphertextTooShort {
                minimum: TAG_LEN as u8,
                actual: len as u8,
            });
        };

        self.0
            .open_in_place(
                aead::Nonce::assume_unique_for_key(nonce.0),
                &aad,
                ciphertext.as_mut(),
            )
            .map_err(|_| CryptoError::OperationFailed(CryptoOperation::Decrypt))?;

        ciphertext.truncate(plaintext_len);
        Ok(())
    }
}

#[derive(Debug)]
struct Dtls12 {
    suite: Dtls12CipherSuite,
    hash: HashAlgorithm,
    algorithm: Algorithm,
}

impl SupportedDtls12CipherSuite for Dtls12 {
    fn suite(&self) -> Dtls12CipherSuite {
        self.suite
    }

    fn hash_algorithm(&self) -> HashAlgorithm {
        self.hash
    }

    fn key_lengths(&self) -> (usize, usize, usize) {
        // (MAC key, encryption key, fixed IV): RFC 5288 and RFC 7905.
        let fixed_iv_len = match self.algorithm {
            Algorithm::Aes128Gcm | Algorithm::Aes256Gcm => 4,
            Algorithm::ChaCha20Poly1305 => 12,
        };
        (0, self.algorithm.aead().key_len(), fixed_iv_len)
    }

    fn explicit_nonce_len(&self) -> usize {
        match self.algorithm {
            Algorithm::Aes128Gcm | Algorithm::Aes256Gcm => 8,
            Algorithm::ChaCha20Poly1305 => 0,
        }
    }

    fn tag_len(&self) -> usize {
        TAG_LEN
    }

    fn create_cipher(&self, key: &[u8]) -> Result<Box<dyn Cipher>, CryptoError> {
        self.algorithm.cipher(key)
    }
}

#[derive(Debug)]
struct Dtls13 {
    suite: Dtls13CipherSuite,
    hash: HashAlgorithm,
    algorithm: Algorithm,
}

impl SupportedDtls13CipherSuite for Dtls13 {
    fn suite(&self) -> Dtls13CipherSuite {
        self.suite
    }

    fn hash_algorithm(&self) -> HashAlgorithm {
        self.hash
    }

    fn key_len(&self) -> usize {
        self.algorithm.aead().key_len()
    }

    fn iv_len(&self) -> usize {
        12
    }

    fn tag_len(&self) -> usize {
        TAG_LEN
    }

    fn create_cipher(&self, key: &[u8]) -> Result<Box<dyn Cipher>, CryptoError> {
        self.algorithm.cipher(key)
    }

    fn encrypt_sn(&self, sn_key: &[u8], sample: &[u8; 16]) -> [u8; 16] {
        self.algorithm.mask(sn_key, sample)
    }
}

const DTLS12_AES_128_GCM: &dyn SupportedDtls12CipherSuite = &Dtls12 {
    suite: Dtls12CipherSuite::ECDHE_ECDSA_AES128_GCM_SHA256,
    hash: HashAlgorithm::SHA256,
    algorithm: Algorithm::Aes128Gcm,
};
const DTLS12_AES_256_GCM: &dyn SupportedDtls12CipherSuite = &Dtls12 {
    suite: Dtls12CipherSuite::ECDHE_ECDSA_AES256_GCM_SHA384,
    hash: HashAlgorithm::SHA384,
    algorithm: Algorithm::Aes256Gcm,
};
const DTLS12_CHACHA20_POLY1305: &dyn SupportedDtls12CipherSuite = &Dtls12 {
    suite: Dtls12CipherSuite::ECDHE_ECDSA_CHACHA20_POLY1305_SHA256,
    hash: HashAlgorithm::SHA256,
    algorithm: Algorithm::ChaCha20Poly1305,
};

const DTLS13_AES_128_GCM: &dyn SupportedDtls13CipherSuite = &Dtls13 {
    suite: Dtls13CipherSuite::AES_128_GCM_SHA256,
    hash: HashAlgorithm::SHA256,
    algorithm: Algorithm::Aes128Gcm,
};
const DTLS13_AES_256_GCM: &dyn SupportedDtls13CipherSuite = &Dtls13 {
    suite: Dtls13CipherSuite::AES_256_GCM_SHA384,
    hash: HashAlgorithm::SHA384,
    algorithm: Algorithm::Aes256Gcm,
};
const DTLS13_CHACHA20_POLY1305: &dyn SupportedDtls13CipherSuite = &Dtls13 {
    suite: Dtls13CipherSuite::CHACHA20_POLY1305_SHA256,
    hash: HashAlgorithm::SHA256,
    algorithm: Algorithm::ChaCha20Poly1305,
};

/// DTLS 1.2 suites, in order of preference where rind runs AES on CPU instructions.
pub(crate) static DTLS12: &[&dyn SupportedDtls12CipherSuite] = &[
    DTLS12_AES_128_GCM,
    DTLS12_AES_256_GCM,
    DTLS12_CHACHA20_POLY1305,
];

/// [`DTLS12`] with ChaCha20-Poly1305 first, which outruns AES without AES
/// instructions.
pub(crate) static DTLS12_CHACHA20_FIRST: &[&dyn SupportedDtls12CipherSuite] = &[
    DTLS12_CHACHA20_POLY1305,
    DTLS12_AES_128_GCM,
    DTLS12_AES_256_GCM,
];

/// DTLS 1.3 suites, in order of preference where rind runs AES on CPU instructions.
pub(crate) static DTLS13: &[&dyn SupportedDtls13CipherSuite] = &[
    DTLS13_AES_128_GCM,
    DTLS13_AES_256_GCM,
    DTLS13_CHACHA20_POLY1305,
];

/// [`DTLS13`] with ChaCha20-Poly1305 first, which outruns AES without AES
/// instructions.
pub(crate) static DTLS13_CHACHA20_FIRST: &[&dyn SupportedDtls13CipherSuite] = &[
    DTLS13_CHACHA20_POLY1305,
    DTLS13_AES_128_GCM,
    DTLS13_AES_256_GCM,
];
