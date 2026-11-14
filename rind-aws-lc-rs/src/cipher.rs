//! Unauthenticated AES encryption in CBC and CTR modes.
//!
//! Not offered, as rind lacks them: ECB, CFB, and OFB modes, ISO 10126
//! padding, DES, and the streaming keys. Pair these modes with a MAC, or use
//! [`crate::aead`].

use core::fmt;

use crate::error::Unspecified;
use crate::hkdf;
use crate::iv::{FixedLength, IV_LEN_128_BIT};
use crate::wipe::Wiped;

/// The length of an AES-128 key, in bytes.
pub const AES_128_KEY_LEN: usize = 16;

/// The length of an AES-192 key, in bytes.
pub const AES_192_KEY_LEN: usize = 24;

/// The length of an AES-256 key, in bytes.
pub const AES_256_KEY_LEN: usize = 32;

/// The length of an AES-CBC IV, in bytes.
pub const AES_CBC_IV_LEN: usize = 16;

/// The length of an AES-CTR IV, the first counter block, in bytes.
pub const AES_CTR_IV_LEN: usize = 16;

const AES_BLOCK_LEN: usize = 16;

/// A block cipher mode of operation.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperatingMode {
    /// Cipher block chaining.
    CBC,
    /// Counter mode, counting over the whole 128-bit block.
    CTR,
}

/// The block cipher an [`Algorithm`] names.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AlgorithmId {
    /// AES with a 128-bit key.
    Aes128,
    /// AES with a 256-bit key.
    Aes256,
    /// AES with a 192-bit key.
    Aes192,
}

/// A block cipher, chosen by one of this module's constants.
#[derive(Debug, PartialEq, Eq)]
pub struct Algorithm {
    id: AlgorithmId,
    key_len: usize,
}

impl Algorithm {
    /// The length of a block, in bytes.
    pub const fn block_len(&self) -> usize {
        AES_BLOCK_LEN
    }

    fn rind(&self) -> &'static rind::cipher::Algorithm {
        match self.id {
            AlgorithmId::Aes128 => &rind::cipher::AES_128,
            AlgorithmId::Aes192 => &rind::cipher::AES_192,
            AlgorithmId::Aes256 => &rind::cipher::AES_256,
        }
    }
}

/// AES with a 128-bit key.
pub const AES_128: Algorithm = Algorithm {
    id: AlgorithmId::Aes128,
    key_len: AES_128_KEY_LEN,
};

/// AES with a 192-bit key.
pub const AES_192: Algorithm = Algorithm {
    id: AlgorithmId::Aes192,
    key_len: AES_192_KEY_LEN,
};

/// AES with a 256-bit key.
pub const AES_256: Algorithm = Algorithm {
    id: AlgorithmId::Aes256,
    key_len: AES_256_KEY_LEN,
};

/// A cipher key is the algorithm's key length.
impl hkdf::KeyType for &'static Algorithm {
    fn len(&self) -> usize {
        self.key_len
    }
}

macro_rules! cipher_context {
    ($name:ident, $other:ident, $doc:expr) => {
        #[doc = $doc]
        #[non_exhaustive]
        pub enum $name {
            /// A 128-bit IV.
            Iv128(FixedLength<IV_LEN_128_BIT>),
            /// No IV.
            None,
        }

        /// The IV's bytes, failing for `None`.
        impl<'a> TryFrom<&'a $name> for &'a [u8] {
            type Error = Unspecified;

            fn try_from(value: &'a $name) -> Result<Self, Unspecified> {
                match value {
                    $name::Iv128(iv) => Ok(iv.as_ref()),
                    $name::None => Err(Unspecified),
                }
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    Self::Iv128(_) => f.write_str("Iv128"),
                    Self::None => f.write_str("None"),
                }
            }
        }

        impl From<$other> for $name {
            fn from(value: $other) -> Self {
                match value {
                    $other::Iv128(iv) => Self::Iv128(iv),
                    $other::None => Self::None,
                }
            }
        }
    };
}

cipher_context!(
    EncryptionContext,
    DecryptionContext,
    "What encrypting takes besides the key: the IV."
);
cipher_context!(
    DecryptionContext,
    EncryptionContext,
    "What decrypting takes besides the key: the IV encrypting used."
);

impl EncryptionContext {
    fn iv(&self) -> Result<&[u8; IV_LEN_128_BIT], Unspecified> {
        match self {
            Self::Iv128(iv) => Ok(iv.as_ref()),
            Self::None => Err(Unspecified),
        }
    }
}

impl DecryptionContext {
    fn iv(&self) -> Result<&[u8; IV_LEN_128_BIT], Unspecified> {
        match self {
            Self::Iv128(iv) => Ok(iv.as_ref()),
            Self::None => Err(Unspecified),
        }
    }
}

/// A key not yet given a mode; wiped on drop under the `wipe` feature.
pub struct UnboundCipherKey {
    algorithm: &'static Algorithm,
    key: Key,
}

// The key bytes, kept until a mode expands them.
type Key = Wiped<[u8; AES_256_KEY_LEN]>;

impl UnboundCipherKey {
    /// Takes `key_bytes` for `algorithm`, failing unless it is the algorithm's key length.
    pub fn new(algorithm: &'static Algorithm, key_bytes: &[u8]) -> Result<Self, Unspecified> {
        if key_bytes.len() != algorithm.key_len {
            return Err(Unspecified);
        }
        let mut key = Key::new([0; AES_256_KEY_LEN]);
        key[..key_bytes.len()].copy_from_slice(key_bytes);
        Ok(Self { algorithm, key })
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    fn bytes(&self) -> &[u8] {
        &self.key[..self.algorithm.key_len]
    }
}

impl fmt::Debug for UnboundCipherKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("UnboundCipherKey")
            .field("algorithm", &self.algorithm)
            .finish()
    }
}

impl From<hkdf::Okm<'_, &'static Algorithm>> for UnboundCipherKey {
    fn from(okm: hkdf::Okm<'_, &'static Algorithm>) -> Self {
        let algorithm = *okm.len();
        let mut key = Key::new([0; AES_256_KEY_LEN]);
        okm.fill_exact(&mut key[..algorithm.key_len]);
        Self { algorithm, key }
    }
}

enum Encrypting {
    Cbc(rind::cipher::AesCbcEncryptingKey),
    Ctr(rind::cipher::AesCtr),
}

impl Encrypting {
    fn new(key: &UnboundCipherKey, mode: OperatingMode) -> Result<Self, Unspecified> {
        let algorithm = key.algorithm.rind();
        Ok(match mode {
            OperatingMode::CBC => Self::Cbc(
                rind::cipher::AesCbcEncryptingKey::new(algorithm, key.bytes())
                    .map_err(crate::error::unspecified)?,
            ),
            OperatingMode::CTR => Self::Ctr(ctr(key)?),
        })
    }

    fn mode(&self) -> OperatingMode {
        match self {
            Self::Cbc(_) => OperatingMode::CBC,
            Self::Ctr(_) => OperatingMode::CTR,
        }
    }
}

fn ctr(key: &UnboundCipherKey) -> Result<rind::cipher::AesCtr, Unspecified> {
    rind::cipher::AesCtr::new(key.algorithm.rind(), key.bytes(), 128)
        .map_err(crate::error::unspecified)
}

/// A key that encrypts in CBC, without padding, or CTR mode; wiped on drop under the `wipe` feature.
pub struct EncryptingKey {
    algorithm: &'static Algorithm,
    key: Encrypting,
}

impl EncryptingKey {
    /// A CTR key.
    pub fn ctr(key: UnboundCipherKey) -> Result<Self, Unspecified> {
        Self::new(key, OperatingMode::CTR)
    }

    /// A CBC key, without padding: it encrypts only whole blocks.
    pub fn cbc(key: UnboundCipherKey) -> Result<Self, Unspecified> {
        Self::new(key, OperatingMode::CBC)
    }

    fn new(key: UnboundCipherKey, mode: OperatingMode) -> Result<Self, Unspecified> {
        Ok(Self {
            algorithm: key.algorithm,
            key: Encrypting::new(&key, mode)?,
        })
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &Algorithm {
        self.algorithm
    }

    /// The mode this key encrypts in.
    pub fn mode(&self) -> OperatingMode {
        self.key.mode()
    }

    /// Encrypts `in_out` in place under a random IV, and returns it.
    pub fn encrypt(&self, in_out: &mut [u8]) -> Result<DecryptionContext, Unspecified> {
        self.less_safe_encrypt(in_out, EncryptionContext::Iv128(FixedLength::new()?))
    }

    /// Encrypts `in_out` in place under the caller's IV, which must never
    /// repeat under this key, and returns it.
    pub fn less_safe_encrypt(
        &self,
        in_out: &mut [u8],
        context: EncryptionContext,
    ) -> Result<DecryptionContext, Unspecified> {
        let iv = context.iv()?;
        match &self.key {
            Encrypting::Cbc(key) => key
                .encrypt_blocks(rind::cipher::CbcIv::assume_unpredictable(*iv), in_out)
                .map_err(crate::error::unspecified)?,
            Encrypting::Ctr(key) => key
                .apply_keystream(iv, in_out)
                .map_err(crate::error::unspecified)?,
        }
        Ok(context.into())
    }
}

impl fmt::Debug for EncryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EncryptingKey")
            .field("algorithm", self.algorithm)
            .field("mode", &self.mode())
            .finish_non_exhaustive()
    }
}

enum Decrypting {
    Cbc(rind::cipher::AesCbcDecryptingKey),
    Ctr(rind::cipher::AesCtr),
}

impl Decrypting {
    fn new(key: &UnboundCipherKey, mode: OperatingMode) -> Result<Self, Unspecified> {
        let algorithm = key.algorithm.rind();
        Ok(match mode {
            OperatingMode::CBC => Self::Cbc(
                rind::cipher::AesCbcDecryptingKey::new(algorithm, key.bytes())
                    .map_err(crate::error::unspecified)?,
            ),
            OperatingMode::CTR => Self::Ctr(ctr(key)?),
        })
    }

    fn mode(&self) -> OperatingMode {
        match self {
            Self::Cbc(_) => OperatingMode::CBC,
            Self::Ctr(_) => OperatingMode::CTR,
        }
    }
}

/// A key that decrypts in CBC, without padding, or CTR mode; wiped on drop under the `wipe` feature.
pub struct DecryptingKey {
    algorithm: &'static Algorithm,
    key: Decrypting,
}

impl DecryptingKey {
    /// A CTR key.
    pub fn ctr(key: UnboundCipherKey) -> Result<Self, Unspecified> {
        Self::new(key, OperatingMode::CTR)
    }

    /// A CBC key, without padding: it decrypts only whole blocks.
    pub fn cbc(key: UnboundCipherKey) -> Result<Self, Unspecified> {
        Self::new(key, OperatingMode::CBC)
    }

    fn new(key: UnboundCipherKey, mode: OperatingMode) -> Result<Self, Unspecified> {
        Ok(Self {
            algorithm: key.algorithm,
            key: Decrypting::new(&key, mode)?,
        })
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &Algorithm {
        self.algorithm
    }

    /// The mode this key decrypts in.
    pub fn mode(&self) -> OperatingMode {
        self.key.mode()
    }

    /// Decrypts `in_out` in place under the IV encrypting used, and returns it.
    pub fn decrypt<'in_out>(
        &self,
        in_out: &'in_out mut [u8],
        context: DecryptionContext,
    ) -> Result<&'in_out mut [u8], Unspecified> {
        let iv = context.iv()?;
        match &self.key {
            Decrypting::Cbc(key) => key
                .decrypt_blocks(iv, in_out)
                .map_err(crate::error::unspecified)?,
            Decrypting::Ctr(key) => key
                .apply_keystream(iv, in_out)
                .map_err(crate::error::unspecified)?,
        }
        Ok(in_out)
    }
}

impl fmt::Debug for DecryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DecryptingKey")
            .field("algorithm", self.algorithm)
            .field("mode", &self.mode())
            .finish_non_exhaustive()
    }
}

/// A key that pads with PKCS#7 and encrypts in CBC mode; wiped on drop under the `wipe` feature.
pub struct PaddedBlockEncryptingKey {
    algorithm: &'static Algorithm,
    key: rind::cipher::AesCbcEncryptingKey,
}

impl PaddedBlockEncryptingKey {
    /// A CBC key that pads with PKCS#7.
    pub fn cbc_pkcs7(key: UnboundCipherKey) -> Result<Self, Unspecified> {
        Ok(Self {
            algorithm: key.algorithm,
            key: rind::cipher::AesCbcEncryptingKey::new(key.algorithm.rind(), key.bytes())
                .map_err(crate::error::unspecified)?,
        })
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &Algorithm {
        self.algorithm
    }

    /// The mode this key encrypts in, always CBC.
    pub fn mode(&self) -> OperatingMode {
        OperatingMode::CBC
    }

    /// Pads `in_out` and encrypts it in place under a random IV, and returns it.
    pub fn encrypt<InOut>(&self, in_out: &mut InOut) -> Result<DecryptionContext, Unspecified>
    where
        InOut: AsMut<[u8]> + for<'in_out> Extend<&'in_out u8>,
    {
        let iv = rind::cipher::CbcIv::random().map_err(crate::error::unspecified)?;
        let context = EncryptionContext::Iv128((*iv.as_bytes()).into());
        self.key
            .encrypt(iv, in_out)
            .map_err(crate::error::unspecified)?;
        Ok(context.into())
    }

    /// Pads `in_out` and encrypts it in place under the caller's IV, which
    /// must be unpredictable, and returns it.
    pub fn less_safe_encrypt<InOut>(
        &self,
        in_out: &mut InOut,
        context: EncryptionContext,
    ) -> Result<DecryptionContext, Unspecified>
    where
        InOut: AsMut<[u8]> + for<'in_out> Extend<&'in_out u8>,
    {
        self.key
            .encrypt(
                rind::cipher::CbcIv::assume_unpredictable(*context.iv()?),
                in_out,
            )
            .map_err(crate::error::unspecified)?;
        Ok(context.into())
    }
}

impl fmt::Debug for PaddedBlockEncryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PaddedBlockEncryptingKey")
            .field("algorithm", self.algorithm)
            .field("mode", &self.mode())
            .finish_non_exhaustive()
    }
}

/// A key that decrypts in CBC mode and removes PKCS#7 padding; wiped on drop under the `wipe` feature.
pub struct PaddedBlockDecryptingKey {
    algorithm: &'static Algorithm,
    key: rind::cipher::AesCbcDecryptingKey,
}

impl PaddedBlockDecryptingKey {
    /// A CBC key that removes PKCS#7 padding.
    pub fn cbc_pkcs7(key: UnboundCipherKey) -> Result<Self, Unspecified> {
        Ok(Self {
            algorithm: key.algorithm,
            key: rind::cipher::AesCbcDecryptingKey::new(key.algorithm.rind(), key.bytes())
                .map_err(crate::error::unspecified)?,
        })
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &Algorithm {
        self.algorithm
    }

    /// The mode this key decrypts in, always CBC.
    pub fn mode(&self) -> OperatingMode {
        OperatingMode::CBC
    }

    /// Decrypts `in_out` in place, checks and removes its padding in
    /// constant time, and returns the plaintext at its front.
    pub fn decrypt<'in_out>(
        &self,
        in_out: &'in_out mut [u8],
        context: DecryptionContext,
    ) -> Result<&'in_out mut [u8], Unspecified> {
        self.key
            .decrypt(context.iv()?, in_out)
            .map_err(crate::error::unspecified)
    }
}

impl fmt::Debug for PaddedBlockDecryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PaddedBlockDecryptingKey")
            .field("algorithm", self.algorithm)
            .field("mode", &self.mode())
            .finish_non_exhaustive()
    }
}
