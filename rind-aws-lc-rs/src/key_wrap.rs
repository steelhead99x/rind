//! Key wrap (RFC 3394) and key wrap with padding (RFC 5649) with AES.

use core::fmt;

// With `fips`, key wrap runs in rind-fips's module, whose API is rind's.
use rind::key_wrap::Mode;
#[cfg(feature = "fips")]
use rind_fips as rind;

use crate::error::{Unspecified, unspecified};
use crate::sealed::Sealed;

/// A block cipher's identity.
#[non_exhaustive]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BlockCipherId {
    /// AES with a 128-bit key.
    Aes128,
    /// AES with a 256-bit key.
    Aes256,
}

/// A block cipher a key encryption key can use.
pub trait BlockCipher: 'static + fmt::Debug + Sealed {
    /// The cipher's identity.
    fn id(&self) -> BlockCipherId;

    /// The cipher's key length in bytes.
    fn key_len(&self) -> usize;
}

/// AES as a key wrap block cipher.
pub struct AesBlockCipher {
    id: BlockCipherId,
    key_len: usize,
}

impl BlockCipherId {
    fn rind(self) -> &'static rind::cipher::Algorithm {
        match self {
            Self::Aes128 => &rind::key_wrap::AES_128,
            Self::Aes256 => &rind::key_wrap::AES_256,
        }
    }
}

impl BlockCipher for AesBlockCipher {
    fn id(&self) -> BlockCipherId {
        self.id
    }

    fn key_len(&self) -> usize {
        self.key_len
    }
}

impl Sealed for AesBlockCipher {}

impl fmt::Debug for AesBlockCipher {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.id, f)
    }
}

/// AES with a 128-bit key.
pub const AES_128: AesBlockCipher = AesBlockCipher {
    id: BlockCipherId::Aes128,
    key_len: 16,
};

/// AES with a 256-bit key.
pub const AES_256: AesBlockCipher = AesBlockCipher {
    id: BlockCipherId::Aes256,
    key_len: 32,
};

/// Key wrap (RFC 3394).
pub trait KeyWrap: Sealed {
    /// Wraps `plaintext`, a multiple of 8 bytes from 16, into the start of
    /// `output`, which must be at least 8 bytes longer, returning the wrapped
    /// key.
    fn wrap<'output>(
        self,
        plaintext: &[u8],
        output: &'output mut [u8],
    ) -> Result<&'output mut [u8], Unspecified>;

    /// Unwraps `ciphertext` into the start of `output`, which must be at
    /// least 8 bytes shorter, returning the unwrapped key.
    fn unwrap<'output>(
        self,
        ciphertext: &[u8],
        output: &'output mut [u8],
    ) -> Result<&'output mut [u8], Unspecified>;
}

/// Key wrap with padding (RFC 5649).
pub trait KeyWrapPadded: Sealed {
    /// Wraps `plaintext`, of any length from 1 byte, into the start of
    /// `output`, which must hold it padded to 8 bytes plus 8, returning the
    /// wrapped key.
    fn wrap_with_padding<'output>(
        self,
        plaintext: &[u8],
        output: &'output mut [u8],
    ) -> Result<&'output mut [u8], Unspecified>;

    /// Unwraps `ciphertext` into the start of `output`, which must be at
    /// least 8 bytes shorter, returning the unwrapped key.
    fn unwrap_with_padding<'output>(
        self,
        ciphertext: &[u8],
        output: &'output mut [u8],
    ) -> Result<&'output mut [u8], Unspecified>;
}

/// An AES key encryption key.
pub type AesKek = KeyEncryptionKey<AesBlockCipher>;

/// A key encryption key, which wraps other keys.
pub struct KeyEncryptionKey<Cipher: BlockCipher> {
    cipher: &'static Cipher,
    kek: rind::key_wrap::AesKek,
}

impl<Cipher: BlockCipher> KeyEncryptionKey<Cipher> {
    /// Makes a key encryption key from `key`, which must be `cipher`'s key
    /// length.
    pub fn new(cipher: &'static Cipher, key: &[u8]) -> Result<Self, Unspecified> {
        let kek = rind::key_wrap::AesKek::new(cipher.id().rind(), key).map_err(unspecified)?;
        Ok(Self { cipher, kek })
    }

    /// The block cipher's identity.
    pub fn block_cipher_id(&self) -> BlockCipherId {
        self.cipher.id()
    }
}

impl<Cipher: BlockCipher> Sealed for KeyEncryptionKey<Cipher> {}

impl KeyWrap for KeyEncryptionKey<AesBlockCipher> {
    fn wrap<'output>(
        self,
        plaintext: &[u8],
        output: &'output mut [u8],
    ) -> Result<&'output mut [u8], Unspecified> {
        let len = plaintext.len().checked_add(8).ok_or(Unspecified)?;
        let output = output.get_mut(..len).ok_or(Unspecified)?;
        self.kek
            .wrap_key(Mode::Kw, plaintext, output)
            .map_err(unspecified)?;
        Ok(output)
    }

    fn unwrap<'output>(
        self,
        ciphertext: &[u8],
        output: &'output mut [u8],
    ) -> Result<&'output mut [u8], Unspecified> {
        let len = ciphertext.len().checked_sub(8).ok_or(Unspecified)?;
        let output = output.get_mut(..len).ok_or(Unspecified)?;
        self.kek
            .unwrap_key(Mode::Kw, ciphertext, output)
            .map_err(unspecified)
    }
}

impl KeyWrapPadded for KeyEncryptionKey<AesBlockCipher> {
    fn wrap_with_padding<'output>(
        self,
        plaintext: &[u8],
        output: &'output mut [u8],
    ) -> Result<&'output mut [u8], Unspecified> {
        let len = plaintext
            .len()
            .checked_next_multiple_of(8)
            .and_then(|len| len.checked_add(8))
            .ok_or(Unspecified)?;
        let output = output.get_mut(..len).ok_or(Unspecified)?;
        self.kek
            .wrap_key(Mode::Kwp, plaintext, output)
            .map_err(unspecified)?;
        Ok(output)
    }

    fn unwrap_with_padding<'output>(
        self,
        ciphertext: &[u8],
        output: &'output mut [u8],
    ) -> Result<&'output mut [u8], Unspecified> {
        let len = ciphertext.len().checked_sub(8).ok_or(Unspecified)?;
        let output = output.get_mut(..len).ok_or(Unspecified)?;
        self.kek
            .unwrap_key(Mode::Kwp, ciphertext, output)
            .map_err(unspecified)
    }
}

impl<Cipher: BlockCipher> fmt::Debug for KeyEncryptionKey<Cipher> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyEncryptionKey")
            .field("cipher", self.cipher)
            .finish_non_exhaustive()
    }
}
