// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::aes::{check_gcm_iv, check_gcm_lengths, expand_key};
use crate::Error;
use crate::low::ghash::GhashTable;
use crate::low::{self, AesKey, Entry, aes_gcm, ct_equal};

/// An AES-GCM key.
///
/// Making one of these is relatively expensive due to key
/// expansion and precomputation.
pub(crate) struct AesGcm {
    key: AesKey,
    gh: GhashTable,
}

impl AesGcm {
    /// The AES key's length in bytes, 16, 24, or 32.
    pub(crate) fn key_len(&self) -> usize {
        self.key.key_len()
    }

    /// Wipes and frees what the key keeps on the heap: a whole-value wipe
    /// that skips this key's drop must call this first.
    #[cfg(rind_backend = "x86_64")]
    pub(crate) fn release(&mut self) {
        self.gh.release();
    }

    /// Expands a 16-, 24-, or 32-byte key, which the caller has checked,
    /// into an AES-128-GCM, AES-192-GCM, or AES-256-GCM key.
    pub(crate) fn new(key: &[u8]) -> Self {
        let _entry = Entry::new_secret();
        let key = expand_key(key);
        let gh = GhashTable::new(u128::from_be_bytes(key.encrypt_block(&[0; 16])));

        Self { key, gh }
    }

    /// Encrypts the given message.
    ///
    /// On entry, `cipher_inout` contains the plaintext of the message.
    /// `nonce` contains the nonce, which must be unique for a given key.
    /// `aad` is the additionally-authenticated data.  It may be empty.
    ///
    /// On exit, `cipher_inout` contains the ciphertext of the message,
    /// and `tag_out` contains the authentication tag.
    ///
    /// Fails with [`Error::WrongLength`], leaving `cipher_inout` unchanged,
    /// if the message is longer than GCM's 2^36 - 32 bytes, or `aad` is
    /// 2^61 bytes or longer.
    pub(crate) fn encrypt(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        cipher_inout: &mut [u8],
        tag_out: &mut [u8; 16],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        check_gcm_lengths(aad.len(), cipher_inout.len())?;
        *tag_out = aes_gcm::seal(&self.key, &self.gh, nonce, aad, cipher_inout);

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
    /// A message past [`Self::encrypt`]'s limits fails with
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
        check_gcm_lengths(aad.len(), cipher_inout.len())?;
        let valid = aes_gcm::open(&self.key, &self.gh, nonce, aad, cipher_inout, tag);

        if low::ct::into_public(valid) {
            low::ct::public_slice(cipher_inout);
            Ok(())
        } else {
            // avoid unauthenticated plaintext leak
            cipher_inout.fill(0x00);
            Err(Error::DecryptFailed)
        }
    }

    /// Encrypts as [`Self::encrypt`] does, under an IV of any length, and
    /// writes the first `tag_out.len()` bytes of the tag, at most 16. A
    /// 96-bit IV and full tag are quicker through [`Self::encrypt`].
    ///
    /// Also fails with [`Error::WrongLength`] if `iv` is empty or 2^61
    /// bytes or longer.
    pub(crate) fn encrypt_any(
        &self,
        iv: &[u8],
        aad: &[u8],
        cipher_inout: &mut [u8],
        tag_out: &mut [u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        check_gcm_iv(iv)?;
        check_gcm_lengths(aad.len(), cipher_inout.len())?;
        let y0 = aes_gcm::initial_counter(&self.gh, iv);
        let tag = aes_gcm::tagged_from::<true>(&self.key, &self.gh, y0, aad, cipher_inout);
        tag_out.copy_from_slice(&tag[..tag_out.len()]);

        low::ct::public_slice(cipher_inout);
        low::ct::public_slice(tag_out);
        Ok(())
    }

    /// Decrypts and verifies as [`Self::decrypt`] does, under an IV of any
    /// length, against `tag`, the first `tag.len()` bytes of the tag, at most
    /// 16.
    ///
    /// Also fails with [`Error::WrongLength`], leaving `cipher_inout`
    /// unchanged, if `iv` is empty or 2^61 bytes or longer.
    pub(crate) fn decrypt_any(
        &self,
        iv: &[u8],
        aad: &[u8],
        cipher_inout: &mut [u8],
        tag: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        check_gcm_iv(iv)?;
        check_gcm_lengths(aad.len(), cipher_inout.len())?;
        let y0 = aes_gcm::initial_counter(&self.gh, iv);
        let want = aes_gcm::tagged_from::<false>(&self.key, &self.gh, y0, aad, cipher_inout);
        let valid = ct_equal(&want[..tag.len()], tag);

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

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn smoketest() {
        let t = AesGcm::new(&[0; 16]);
        let mut tag = [0u8; 16];
        t.encrypt(&[0u8; 12], &[], &mut [], &mut tag).unwrap();
        assert_eq!(
            &tag,
            b"\x58\xe2\xfc\xce\xfa\x7e\x30\x61\x36\x7f\x1d\x57\xa4\xe7\x45\x5a"
        );
    }

    #[test]
    fn long_encrypt_test() {
        let t = AesGcm::new(&[b'k'; 16]);
        let mut tag = [0u8; 16];
        // not divisible by 128, 64, 16 to cover by-8, by-4, and trailing cases
        let mut cipher = [b'p'; 4164];
        t.encrypt(b"noncenonceno", b"aad", &mut cipher, &mut tag)
            .unwrap();

        let expected = include_bytes!("../testdata/aes-gcm-ciphertext.bin");
        let (expected_cipher, expected_tag) = expected.split_at(expected.len() - 16);
        assert_eq!(expected_cipher, cipher);
        assert_eq!(expected_tag, tag);
    }

    #[test]
    fn long_decrypt_test() {
        let t = AesGcm::new(&[b'k'; 16]);
        let expected = include_bytes!("../testdata/aes-gcm-ciphertext.bin");
        let (cipher, tag) = expected.split_at(expected.len() - 16);
        let mut plain = cipher.to_vec();

        t.decrypt(b"noncenonceno", b"aad", &mut plain, tag.try_into().unwrap())
            .unwrap();

        assert_eq!(plain, &[b'p'; 4164]);
    }
}
