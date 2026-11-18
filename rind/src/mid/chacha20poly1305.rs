// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::chacha20::check_counter;
use crate::Error;
use crate::low::{self, Entry, zeroise};

/// A ChaCha20Poly1305 key.
///
/// See [RFC7539](https://datatracker.ietf.org/doc/html/rfc7539).
pub(crate) struct ChaCha20Poly1305 {
    key: [u8; 32],
}

impl ChaCha20Poly1305 {
    /// Create a new [`ChaCha20Poly1305`] from 32 bytes of key material.
    pub(crate) fn new(key: [u8; 32]) -> Self {
        low::ct::secret_slice(&key);
        Self { key }
    }

    /// Encrypt the given message.
    ///
    /// On entry, `cipher_inout` contains the plaintext of the message.
    /// `nonce` contains the nonce, which must be unique for a given key.
    /// `aad` is the additionally-authenticated data.  It may be empty.
    ///
    /// On exit, `cipher_inout` contains the ciphertext of the message,
    /// and `tag_out` contains the authentication tag.
    ///
    /// Fails with [`Error::WrongLength`], leaving `cipher_inout` unchanged,
    /// if the message is longer than the 2^38 - 64 bytes its 32-bit block
    /// counter covers.
    pub(crate) fn encrypt(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        cipher_inout: &mut [u8],
        tag_out: &mut [u8; 16],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        // block 0 keys Poly1305
        check_counter(1, cipher_inout.len())?;
        *tag_out = low::chacha20poly1305::seal(&self.key, nonce, aad, cipher_inout);
        low::ct::public_slice(cipher_inout);
        low::ct::public_slice(tag_out);
        Ok(())
    }

    /// Decrypts and verifies the given message.
    ///
    /// On entry, `cipher_inout` contains the ciphertext of the message.
    /// `nonce` contains the nonce, which must match what was supplied
    /// when encrypting this message.
    /// `aad` is the additionally-authenticated data.  It may be empty.
    /// `tag` is the purported authentication tag.
    ///
    /// On success, `cipher_inout` contains the plaintext of the message,
    /// and `Ok(())` is returned.
    /// A message past [`Self::encrypt`]'s limit fails with
    /// `Err(Error::WrongLength)`, leaving `cipher_inout` unchanged.
    /// Otherwise, `Err(Error::DecryptFailed)` is returned and `cipher_inout`
    /// is cleared.
    pub(crate) fn decrypt(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        cipher_inout: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        check_counter(1, cipher_inout.len())?;
        let valid = low::chacha20poly1305::open(&self.key, nonce, aad, cipher_inout, tag);

        if low::ct::into_public(valid) {
            low::ct::public_slice(cipher_inout);
            Ok(())
        } else {
            // avoid unauthenticated plaintext leak
            cipher_inout.fill(0x00);
            Err(Error::DecryptFailed)
        }
    }
}

impl Drop for ChaCha20Poly1305 {
    fn drop(&mut self) {
        zeroise(&mut self.key);
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    #[test]
    fn test_vector() {
        // from RFC7539
        let k = ChaCha20Poly1305::new([
            0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d,
            0x8e, 0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b,
            0x9c, 0x9d, 0x9e, 0x9f,
        ]);
        let mut buffer = *b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
        let aad = [
            0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
        ];
        let nonce = [
            0x07, 0x00, 0x00, 0x00, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
        ];
        let mut tag = [0u8; 16];

        k.encrypt(&nonce, &aad, &mut buffer[..], &mut tag).unwrap();

        assert_eq!(
            buffer,
            [
                0xd3, 0x1a, 0x8d, 0x34, 0x64, 0x8e, 0x60, 0xdb, 0x7b, 0x86, 0xaf, 0xbc, 0x53, 0xef,
                0x7e, 0xc2, 0xa4, 0xad, 0xed, 0x51, 0x29, 0x6e, 0x08, 0xfe, 0xa9, 0xe2, 0xb5, 0xa7,
                0x36, 0xee, 0x62, 0xd6, 0x3d, 0xbe, 0xa4, 0x5e, 0x8c, 0xa9, 0x67, 0x12, 0x82, 0xfa,
                0xfb, 0x69, 0xda, 0x92, 0x72, 0x8b, 0x1a, 0x71, 0xde, 0x0a, 0x9e, 0x06, 0x0b, 0x29,
                0x05, 0xd6, 0xa5, 0xb6, 0x7e, 0xcd, 0x3b, 0x36, 0x92, 0xdd, 0xbd, 0x7f, 0x2d, 0x77,
                0x8b, 0x8c, 0x98, 0x03, 0xae, 0xe3, 0x28, 0x09, 0x1b, 0x58, 0xfa, 0xb3, 0x24, 0xe4,
                0xfa, 0xd6, 0x75, 0x94, 0x55, 0x85, 0x80, 0x8b, 0x48, 0x31, 0xd7, 0xbc, 0x3f, 0xf4,
                0xde, 0xf0, 0x8e, 0x4b, 0x7a, 0x9d, 0xe5, 0x76, 0xd2, 0x65, 0x86, 0xce, 0xc6, 0x4b,
                0x61, 0x16
            ]
        );
        assert_eq!(
            tag,
            [
                0x1a, 0xe1, 0x0b, 0x59, 0x4f, 0x09, 0xe2, 0x6a, 0x7e, 0x90, 0x2e, 0xcb, 0xd0, 0x60,
                0x06, 0x91
            ]
        );
    }
}
