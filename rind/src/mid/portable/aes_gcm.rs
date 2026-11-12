// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::aes::{check_gcm_iv, check_gcm_lengths};
use crate::Error;
use crate::low::{self, Entry, NohwTable, PortableAesKey, ct_equal};
#[cfg(rind_backend = "arm")]
use crate::low::{AesHwKey, GhashTable, HaveCryptoExt};

/// An AES-GCM key.
pub(crate) enum AesGcm {
    Portable(Portable),
    /// armv7's crypto extension's, which the key picks when the CPU has it.
    #[cfg(rind_backend = "arm")]
    Hw(Hw),
}

impl AesGcm {
    /// Expands a 16-, 24-, or 32-byte key, which the caller has checked,
    /// into an AES-128-GCM, AES-192-GCM, or AES-256-GCM key.
    pub(crate) fn new(key: &[u8]) -> Self {
        let _entry = Entry::new_secret();
        // Mark a copy: the caller's buffer may be shared, or a promoted constant.
        let mut copy = [0u8; 32];
        let copy_key = &mut copy[..key.len()];
        copy_key.copy_from_slice(key);
        low::ct::secret_slice(copy_key);
        #[cfg(rind_backend = "arm")]
        if let Some(token) = HaveCryptoExt::check() {
            return Self::Hw(Hw::new(copy_key, token));
        }
        Self::Portable(Portable::new(copy_key))
    }

    /// The AES key's length in bytes, 16, 24, or 32.
    pub(crate) fn key_len(&self) -> usize {
        match self {
            Self::Portable(key) => key.key.key_len(),
            #[cfg(rind_backend = "arm")]
            Self::Hw(key) => key.key.key_len(),
        }
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
        match self {
            Self::Portable(key) => *tag_out = key.tagged::<true>(nonce, aad, cipher_inout),
            #[cfg(rind_backend = "arm")]
            Self::Hw(key) => *tag_out = key.tagged::<true>(nonce, aad, cipher_inout),
        }
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
        let want = match self {
            Self::Portable(key) => key.tagged::<false>(nonce, aad, cipher_inout),
            #[cfg(rind_backend = "arm")]
            Self::Hw(key) => key.tagged::<false>(nonce, aad, cipher_inout),
        };
        let result = ct_equal(&want, tag);

        if low::ct::into_public(result) {
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
        let tag = match self {
            Self::Portable(key) => key.tagged::<true>(iv, aad, cipher_inout),
            #[cfg(rind_backend = "arm")]
            Self::Hw(key) => key.tagged::<true>(iv, aad, cipher_inout),
        };
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
        let want = match self {
            Self::Portable(key) => key.tagged::<false>(iv, aad, cipher_inout),
            #[cfg(rind_backend = "arm")]
            Self::Hw(key) => key.tagged::<false>(iv, aad, cipher_inout),
        };
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

/// aws-lc's bitsliced AES and integer GHASH, for CPUs without the crypto
/// extension. Both wipe themselves on drop.
pub(crate) struct Portable {
    key: PortableAesKey,
    table: NohwTable,
}

impl Portable {
    fn new(key: &[u8]) -> Self {
        let key = PortableAesKey::new(key);
        let h = key.encrypt_block(&[0; 16]);
        let table = NohwTable::new(&h);
        Self { key, table }
    }
}

/// Bytes of counter mode between GHASH passes, so GHASH reads them back from
/// cache: aws-lc's `GHASH_CHUNK`.
const CHUNK: usize = 3 * 1024;

/// aws-lc's AES and GHASH for the crypto extension, composed as aws-lc's
/// `CRYPTO_gcm128_encrypt_ctr32` does on 32-bit ARM.
#[cfg(rind_backend = "arm")]
pub(crate) struct Hw {
    key: AesHwKey,
    table: GhashTable,
}

#[cfg(rind_backend = "arm")]
impl Hw {
    fn new(key: &[u8], token: HaveCryptoExt) -> Self {
        let key = AesHwKey::new(key, token);
        let h = key.encrypt_block(&[0; 16]);
        let table = GhashTable::new(&h, token);
        Self { key, table }
    }
}

/// The AES and GHASH a GCM composed of separate passes runs.
trait Parts {
    /// GHASH's key powers.
    type Table: Ghash;

    fn table(&self) -> &Self::Table;

    #[must_use]
    fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16];

    /// XORs the keystream from counter block `ivec` into `inout`, its last
    /// four bytes incremented with 32-bit wrapping, returning the next
    /// counter block.
    fn ctr(&self, ivec: &[u8; 16], inout: &mut [u8]) -> [u8; 16];

    /// Encrypts (if `ENC`) or decrypts `inout` in place under `iv`, of any
    /// length, and returns its tag.
    fn tagged<const ENC: bool>(&self, iv: &[u8], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
        let table = self.table();
        let mut y0 = [0u8; 16];
        match iv.try_into() {
            Ok(nonce) => {
                let nonce: &[u8; 12] = nonce;
                y0[..12].copy_from_slice(nonce);
                y0[15] = 1;
            }
            Err(_) => {
                ghash(table, &mut y0, iv);
                table.ghash(&mut y0, &[lengths(0, iv.len())]);
            }
        }

        let mut xi = [0u8; 16];
        ghash(table, &mut xi, aad);
        let mut counter = add32(&y0, 1);
        for chunk in inout.chunks_mut(CHUNK) {
            if !ENC {
                ghash(table, &mut xi, chunk);
            }
            counter = self.ctr(&counter, chunk);
            if ENC {
                ghash(table, &mut xi, chunk);
            }
        }

        // Finishes GHASH with the bit lengths, then masks it with the first
        // counter block's keystream.
        table.ghash(&mut xi, &[lengths(aad.len(), inout.len())]);
        for (x, e) in xi.iter_mut().zip(self.encrypt_block(&y0)) {
            *x ^= e;
        }
        xi
    }
}

/// GHASH over whole blocks.
trait Ghash {
    fn ghash(&self, xi: &mut [u8; 16], input: &[[u8; 16]]);
}

#[cfg(rind_backend = "arm")]
impl Ghash for GhashTable {
    fn ghash(&self, xi: &mut [u8; 16], input: &[[u8; 16]]) {
        self.ghash(xi, input);
    }
}

impl Ghash for NohwTable {
    fn ghash(&self, xi: &mut [u8; 16], input: &[[u8; 16]]) {
        self.ghash(xi, input);
    }
}

#[cfg(rind_backend = "arm")]
impl Parts for Hw {
    type Table = GhashTable;

    fn table(&self) -> &GhashTable {
        &self.table
    }

    fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        self.key.encrypt_block(block)
    }

    fn ctr(&self, ivec: &[u8; 16], inout: &mut [u8]) -> [u8; 16] {
        let (blocks, tail) = inout.as_chunks_mut::<16>();
        self.key.ctr32(ivec, blocks);
        let ivec = add32(ivec, blocks.len() as u32);
        if tail.is_empty() {
            return ivec;
        }

        for (b, k) in tail.iter_mut().zip(self.key.encrypt_block(&ivec)) {
            *b ^= k;
        }
        add32(&ivec, 1)
    }
}

impl Parts for Portable {
    type Table = NohwTable;

    fn table(&self) -> &NohwTable {
        &self.table
    }

    fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        self.key.encrypt_block(block)
    }

    fn ctr(&self, ivec: &[u8; 16], inout: &mut [u8]) -> [u8; 16] {
        // The final partial block shares the last batch.
        self.key.ctr32(ivec, inout);
        add32(ivec, inout.len().div_ceil(16) as u32)
    }
}

/// Folds `data` into `xi`, padding its last block with zeroes.
fn ghash(table: &impl Ghash, xi: &mut [u8; 16], data: &[u8]) {
    let (blocks, tail) = data.as_chunks::<16>();
    table.ghash(xi, blocks);
    if !tail.is_empty() {
        let mut last = [0u8; 16];
        last[..tail.len()].copy_from_slice(tail);
        table.ghash(xi, &[last]);
    }
}

/// GCM's last GHASH block: the bit lengths of the AAD and the message.
fn lengths(aad: usize, msg: usize) -> [u8; 16] {
    (((aad as u128 * 8) << 64) | (msg as u128 * 8)).to_be_bytes()
}

/// `block` with `n` added to its big-endian counter in its last four bytes,
/// modulo 2^32, as GCM increments it.
fn add32(block: &[u8; 16], n: u32) -> [u8; 16] {
    let b = u128::from_be_bytes(*block);
    let ctr = (b as u32).wrapping_add(n);
    (b & !0xffff_ffff | u128::from(ctr)).to_be_bytes()
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
    fn long_round_trip() {
        let t = AesGcm::new(&[b'k'; 16]);
        let expected = include_bytes!("../../testdata/aes-gcm-ciphertext.bin");
        let (expected_cipher, expected_tag) = expected.split_at(expected.len() - 16);

        let mut tag = [0u8; 16];
        let mut cipher = [b'p'; 4164];
        t.encrypt(b"noncenonceno", b"aad", &mut cipher, &mut tag)
            .unwrap();
        assert_eq!(expected_cipher, cipher);
        assert_eq!(expected_tag, tag);

        t.decrypt(b"noncenonceno", b"aad", &mut cipher, &tag)
            .unwrap();
        assert_eq!(cipher, [b'p'; 4164]);
    }

    // The crypto extension's composition and the portable one, against GCM
    // by the book: each key size,
    // IVs of 1, 12, and 17 bytes, message lengths around the block and chunk
    // boundaries, and counter blocks whose 32-bit counter wraps within the
    // message, as an IV other than 96 bits may hash to.
    #[test]
    fn compositions_match_model() {
        use crate::low::gcm_model;

        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for key_len in [16, 24, 32] {
            let raw = bytes(key_len, 1);
            let portable = Portable::new(&raw);
            #[cfg(rind_backend = "arm")]
            let hw = HaveCryptoExt::check().map(|token| Hw::new(&raw, token));
            let encrypt = |b: &[u8; 16]| portable.encrypt_block(b);
            let aad = bytes(17, 2);
            for msg_len in [0, 1, 16, 17, 100, 3071, 3073] {
                let plain = bytes(msg_len, 3);
                let what = format!("{key_len} {msg_len}");
                let mut runs = vec![];
                for iv_len in [1, 12, 17] {
                    let iv = bytes(iv_len, msg_len as u32);
                    let mut y0 = [0u8; 16];
                    if iv_len == 12 {
                        y0[..12].copy_from_slice(&iv);
                        y0[15] = 1;
                    } else {
                        ghash(portable.table(), &mut y0, &iv);
                        portable.table().ghash(&mut y0, &[lengths(0, iv_len)]);
                    }
                    runs.push((iv, y0));
                }

                for (iv, y0) in runs {
                    let want = gcm_model(encrypt, &y0, &aad, &plain);
                    check(&portable, &iv, &aad, &plain, &want, &what);
                    #[cfg(rind_backend = "arm")]
                    if let Some(hw) = &hw {
                        check(hw, &iv, &aad, &plain, &want, &what);
                    }
                }
            }
        }

        // The counter's wrap, which `tagged` reaches only through an IV's
        // hash, so the parts' own CTR is checked from a counter block about
        // to wrap: within one call, and across two split at a block, as
        // `tagged`'s chunks are.
        let portable = Portable::new(&[7; 16]);
        let mut y0 = [3u8; 16];
        y0[12..].copy_from_slice(&0xffff_fffeu32.to_be_bytes());
        let plain = bytes(100, 4);
        let (want, _) = gcm_model(|b| portable.encrypt_block(b), &y0, &[], &plain);
        let mut got = plain.clone();
        let mut next = add32(&y0, 1);
        next = portable.ctr(&next, &mut got[..48]);
        portable.ctr(&next, &mut got[48..]);
        assert_eq!(got, want);
        #[cfg(rind_backend = "arm")]
        if let Some(token) = HaveCryptoExt::check() {
            let hw = Hw::new(&[7; 16], token);
            let mut got = plain.clone();
            let next = hw.ctr(&add32(&y0, 1), &mut got[..48]);
            hw.ctr(&next, &mut got[48..]);
            assert_eq!(got, want);
        }

        fn check(
            parts: &impl Parts,
            iv: &[u8],
            aad: &[u8],
            plain: &[u8],
            (want, want_tag): &(Vec<u8>, [u8; 16]),
            what: &str,
        ) {
            let mut got = plain.to_vec();
            let tag = parts.tagged::<true>(iv, aad, &mut got);
            assert_eq!((&got, &tag), (want, want_tag), "{what}");
            let tag = parts.tagged::<false>(iv, aad, &mut got);
            assert_eq!((&got[..], &tag), (plain, want_tag), "{what}");
        }
    }

    // The crypto extension's key setup, GHASH, and AES-CTR, both ways, for
    // each key size, with a secret key, nonce or IV, AAD, and message, for
    // `admin/ct-qemu`. The message spans a GHASH chunk, then 5 blocks, which
    // take the CTR routine's 3-block loop and 2-block tail, and a partial
    // block; the AAD is an even run of blocks and a partial one.
    #[cfg(rind_backend = "arm")]
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu-arm"]
    fn ct_qemu_aes_gcm() {
        use crate::low::ct_qemu;

        let seed = ct_qemu::seed().to_le_bytes();
        let bytes = |n| seed.iter().cycle().take(n).copied().collect::<Vec<u8>>();
        for key_len in [16, 24, 32] {
            let key = bytes(key_len);
            let gcm = ct_qemu::traced(|| AesGcm::new(&key));
            assert!(matches!(gcm, AesGcm::Hw(_)), "the crypto extension");

            let nonce = bytes(12).try_into().unwrap();
            let aad = bytes(300);
            let mut msg = bytes(CHUNK + 5 * 16 + 8);
            let mut tag = [0u8; 16];
            ct_qemu::traced(|| gcm.encrypt(&nonce, &aad, &mut msg, &mut tag)).unwrap();
            ct_qemu::traced(|| gcm.decrypt(&nonce, &aad, &mut msg, &tag)).unwrap();

            // An IV other than 96 bits, which hashes to a secret counter
            // block, and a truncated tag.
            let iv = bytes(17);
            let mut tag = [0u8; 12];
            ct_qemu::traced(|| gcm.encrypt_any(&iv, &aad, &mut msg, &mut tag)).unwrap();
            ct_qemu::traced(|| gcm.decrypt_any(&iv, &aad, &mut msg, &tag)).unwrap();
        }
    }
}
