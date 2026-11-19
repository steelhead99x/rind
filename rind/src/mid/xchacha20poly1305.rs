// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::chacha20::check_counter;
use crate::Error;
use crate::low::{self, Entry, zeroise};

/// A XChaCha20Poly1305 key.
///
/// See [RFC7539](https://datatracker.ietf.org/doc/html/rfc7539).
pub(crate) struct XChaCha20Poly1305 {
    key: [u8; 32],
}

impl XChaCha20Poly1305 {
    /// Create a new [`XChaCha20Poly1305`] from 32 bytes of key material.
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
        nonce: &[u8; 24],
        aad: &[u8],
        cipher_inout: &mut [u8],
        tag_out: &mut [u8; 16],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        // block 0 keys Poly1305
        check_counter(1, cipher_inout.len())?;
        let (key, nonce) = self.subkey(nonce);
        *tag_out = low::chacha20poly1305::seal(&key, &nonce, aad, cipher_inout);
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
        nonce: &[u8; 24],
        aad: &[u8],
        cipher_inout: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        check_counter(1, cipher_inout.len())?;
        let (key, nonce) = self.subkey(nonce);
        let valid = low::chacha20poly1305::open(&key, &nonce, aad, cipher_inout, tag);

        if low::ct::into_public(valid) {
            low::ct::public_slice(cipher_inout);
            Ok(())
        } else {
            // avoid unauthenticated plaintext leak
            cipher_inout.fill(0x00);
            Err(Error::DecryptFailed)
        }
    }

    /// The ChaCha20-Poly1305 key and nonce that `nonce` picks under this key.
    fn subkey(&self, nonce: &[u8; 24]) -> ([u8; 32], [u8; 12]) {
        let (head, tail) = nonce.split_at(16);
        let mut chacha_nonce = [0u8; 12];
        chacha_nonce[4..].copy_from_slice(tail);
        (
            low::hchacha20(&self.key, head.try_into().unwrap()),
            chacha_nonce,
        )
    }
}

impl Drop for XChaCha20Poly1305 {
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
        // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-xchacha-03#appendix-A.1
        let k = XChaCha20Poly1305::new([
            0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d,
            0x8e, 0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b,
            0x9c, 0x9d, 0x9e, 0x9f,
        ]);
        let mut buffer = *b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
        let aad = [
            0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
        ];
        let nonce = *b"@ABCDEFGHIJKLMNOPQRSTUVW";
        let mut tag = [0u8; 16];

        k.encrypt(&nonce, &aad, &mut buffer[..], &mut tag).unwrap();

        assert_eq!(
            buffer,
            [
                0xbd, 0x6d, 0x17, 0x9d, 0x3e, 0x83, 0xd4, 0x3b, 0x95, 0x76, 0x57, 0x94, 0x93, 0xc0,
                0xe9, 0x39, 0x57, 0x2a, 0x17, 0x00, 0x25, 0x2b, 0xfa, 0xcc, 0xbe, 0xd2, 0x90, 0x2c,
                0x21, 0x39, 0x6c, 0xbb, 0x73, 0x1c, 0x7f, 0x1b, 0x0b, 0x4a, 0xa6, 0x44, 0x0b, 0xf3,
                0xa8, 0x2f, 0x4e, 0xda, 0x7e, 0x39, 0xae, 0x64, 0xc6, 0x70, 0x8c, 0x54, 0xc2, 0x16,
                0xcb, 0x96, 0xb7, 0x2e, 0x12, 0x13, 0xb4, 0x52, 0x2f, 0x8c, 0x9b, 0xa4, 0x0d, 0xb5,
                0xd9, 0x45, 0xb1, 0x1b, 0x69, 0xb9, 0x82, 0xc1, 0xbb, 0x9e, 0x3f, 0x3f, 0xac, 0x2b,
                0xc3, 0x69, 0x48, 0x8f, 0x76, 0xb2, 0x38, 0x35, 0x65, 0xd3, 0xff, 0xf9, 0x21, 0xf9,
                0x66, 0x4c, 0x97, 0x63, 0x7d, 0xa9, 0x76, 0x88, 0x12, 0xf6, 0x15, 0xc6, 0x8b, 0x13,
                0xb5, 0x2e
            ]
        );
        assert_eq!(
            tag,
            [
                0xc0, 0x87, 0x59, 0x24, 0xc1, 0xc7, 0x98, 0x79, 0x47, 0xde, 0xaf, 0xd8, 0x78, 0x0a,
                0xcf, 0x49
            ]
        );
    }
}
