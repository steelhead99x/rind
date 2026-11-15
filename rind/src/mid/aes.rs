// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::Error;
use crate::cipher::Algorithm;
use crate::low::{self, AesKey, Entry};

/// An AES key that encrypts single blocks.
///
/// This is the bare block cipher. Use it only where a protocol specifies
/// AES on one block, such as DTLS 1.3 record number protection or SRTP key
/// derivation; QUIC header protection has [`crate::aead::quic`].
pub struct Aes(AesKey);

impl Aes {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not that algorithm's key length.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        if key.len() != algorithm.key_len {
            return Err(Error::WrongLength);
        }
        Ok(Self(expand_key(key)))
    }

    /// The key's length in bytes, 16, 24, or 32.
    pub(crate) fn key_len(&self) -> usize {
        self.0.key_len()
    }

    /// Encrypts one block in place.
    pub fn encrypt_block(&self, block: &mut [u8; 16]) {
        let _entry = Entry::new_secret();
        low::ct::secret_slice(block);
        *block = self.0.encrypt_block(block);
        low::ct::public_slice(block);
    }

    /// The QUIC header-protection mask for `sample` (RFC 9001 section 5.4.3),
    /// read from `sample` without the copy [`Self::encrypt_block`] needs.
    pub(crate) fn header_protection_mask(&self, sample: &[u8; 16]) -> [u8; 5] {
        let _entry = Entry::new_secret();
        let block = self.0.encrypt_block(sample);
        let mask = [block[0], block[1], block[2], block[3], block[4]];
        low::ct::public_slice(&mask);
        mask
    }
}

/// An AES key for counter mode, with a counter width fixed when it is made.
///
/// Each call takes a 16-byte counter block whose rightmost `counter_bits` bits
/// are a big-endian counter, incremented per block and wrapping within those
/// bits, as WebCrypto's AES-CTR defines it. RFC 3686 uses 32 bits; SRTP's
/// AES-CM, whose IVs leave their low 16 bits zero for at most 2^16 blocks,
/// works with any width of at least 16; pyca's and aws-lc-rs's CTR use 128.
/// Counter mode is unauthenticated, so pair it with a MAC.
pub struct AesCtr {
    key: AesKey,
    /// The counter block's counting bits.
    counter_mask: u128,
}

impl AesCtr {
    /// Expands `key` for `algorithm`, counting over the rightmost
    /// `counter_bits` bits of each counter block.
    ///
    /// Fails with [`Error::WrongLength`] if `key` is not that algorithm's key
    /// length, or if `counter_bits` is not 1 to 128.
    pub fn new(algorithm: &'static Algorithm, key: &[u8], counter_bits: u8) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        if key.len() != algorithm.key_len || !(1..=128).contains(&counter_bits) {
            return Err(Error::WrongLength);
        }
        Ok(Self {
            key: expand_key(key),
            counter_mask: u128::MAX >> (128 - counter_bits),
        })
    }

    /// XORs the keystream from `counter_block` into `inout`.
    ///
    /// Encryption and decryption are the same operation. The counter block is
    /// not secret. Each call starts at a whole block, so a stream split after
    /// a length that is not a multiple of 16 cannot resume mid-block: passing
    /// that partial block's counter block again reuses keystream.
    ///
    /// Fails with [`Error::WrongLength`], leaving `inout` unchanged, if
    /// `inout` needs more than 2^`counter_bits` blocks: the counter would wrap
    /// onto a block already used, repeating keystream.
    pub fn apply_keystream(&self, counter_block: &[u8; 16], inout: &mut [u8]) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        let blocks = inout.len().div_ceil(16) as u128;
        if blocks.saturating_sub(1) > self.counter_mask {
            return Err(Error::WrongLength);
        }
        low::ct::secret_slice(inout);

        // The backends increment the low 32 bits, wrapping within them, so
        // split the message where those wrap or the counter does first.
        let counter_mask = self.counter_mask;
        let word_mask = counter_mask & u128::from(u32::MAX);
        let mut block = u128::from_be_bytes(*counter_block);
        let mut rest = &mut *inout;
        while !rest.is_empty() {
            let segment_blocks = (word_mask - (block & word_mask) + 1) as u64;
            let len = match usize::try_from(segment_blocks * 16) {
                Ok(len) if len < rest.len() => len,
                _ => rest.len(),
            };
            let (segment, next) = rest.split_at_mut(len);
            let bytes = block.to_be_bytes();
            let (nonce, counter) = bytes.split_first_chunk::<12>().unwrap();
            let counter = u32::from_be_bytes(counter.try_into().unwrap());
            low::aes_ctr::apply(&self.key, nonce, counter, segment);

            let counter = block.wrapping_add(segment_blocks.into());
            block = (block & !counter_mask) | (counter & counter_mask);
            rest = next;
        }
        low::ct::public_slice(inout);
        Ok(())
    }
}

impl fmt::Debug for Aes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Aes")
            .field("algorithm", crate::cipher::aes(self.key_len()))
            .finish_non_exhaustive()
    }
}

impl fmt::Debug for AesCtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AesCtr")
            .field("algorithm", crate::cipher::aes(self.key.key_len()))
            .finish_non_exhaustive()
    }
}

// The counter mask is not secret, but is wiped with the key, padding
// included, so that the whole value reads zero.
impl Drop for AesCtr {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::Zeroable for AesCtr {}

/// Fails with [`Error::WrongLength`] if `len` bytes need more blocks than
/// remain from block `counter` before the 32-bit counter wraps.
fn check_counter(counter: u32, len: usize) -> Result<(), Error> {
    if u64::from(counter) + len.div_ceil(16) as u64 > 1 << 32 {
        return Err(Error::WrongLength);
    }
    Ok(())
}

/// Fails with [`Error::WrongLength`] if an AES-GCM message is past its limits.
///
/// Its counter blocks start at 2, after the tag's, and the AAD's bit length
/// must fit in 64 bits.
pub(super) fn check_gcm_lengths(aad: usize, msg: usize) -> Result<(), Error> {
    if aad as u64 >= 1 << 61 {
        return Err(Error::WrongLength);
    }
    check_counter(2, msg)
}

/// Fails with [`Error::WrongLength`] unless `iv` is an AES-GCM IV: not
/// empty, and with a bit length that fits in 64 bits.
pub(crate) fn check_gcm_iv(iv: &[u8]) -> Result<(), Error> {
    if iv.is_empty() || iv.len() as u64 >= 1 << 61 {
        return Err(Error::WrongLength);
    }
    Ok(())
}

/// Expands `key`, which the caller has checked is 16, 24, or 32 bytes.
pub(super) fn expand_key(key: &[u8]) -> AesKey {
    // Mark a copy: the caller's buffer may be shared, or a promoted constant.
    let mut copy = [0u8; 32];
    let copy_key = &mut copy[..key.len()];
    copy_key.copy_from_slice(key);
    low::ct::secret_slice(copy_key);
    AesKey::new(copy_key)
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::cipher::{AES_128, AES_192, AES_256};
    use crate::low::AesDecKey;
    use crate::test::*;

    fn algorithm(key: &[u8]) -> &'static Algorithm {
        crate::cipher::aes(key.len())
    }

    #[test]
    fn acvp_ecb() {
        for group in acvp("ACVP-AES-ECB-1.0") {
            assert_eq!(group.str("direction"), "encrypt");
            for test in group.tests() {
                let mut key = test.hex("key");
                match group.str("testType") {
                    "AFT" => {
                        let aes = Aes::new(algorithm(&key), &key).unwrap();
                        let mut text = test.hex("pt");
                        let (blocks, rest) = text.as_chunks_mut::<16>();
                        assert!(rest.is_empty());
                        for block in blocks {
                            aes.encrypt_block(block);
                        }
                        assert_eq!(text, test.hex("ct"));
                    }
                    "MCT" => {
                        let mut block: [u8; 16] = test.hex("pt").try_into().unwrap();
                        for result in test["resultsArray"].as_array().unwrap() {
                            assert_eq!(key, result.hex("key"));
                            assert_eq!(block, &result.hex("pt")[..]);
                            let aes = Aes::new(algorithm(&key), &key).unwrap();
                            let mut previous = block;
                            for _ in 0..1000 {
                                previous = block;
                                aes.encrypt_block(&mut block);
                            }
                            assert_eq!(block, &result.hex("ct")[..]);
                            aes_mct_next_key(&mut key, &previous, &block);
                        }
                    }
                    other => panic!("unexpected test type {other}"),
                }
            }
        }
    }

    #[test]
    fn acvp_ctr() {
        for group in acvp("ACVP-AES-CTR-1.0") {
            assert_eq!(group.str("internalTestType"), "RFC3686");
            let (input, output) = match group.str("direction") {
                "encrypt" => ("pt", "ct"),
                "decrypt" => ("ct", "pt"),
                other => panic!("unexpected direction {other}"),
            };
            for test in group.tests() {
                let key = test.hex("key");
                let ctr = AesCtr::new(algorithm(&key), &key, 32).unwrap();
                let mut text = test.hex(input);
                ctr.apply_keystream(&test.hex("iv").try_into().unwrap(), &mut text)
                    .unwrap();
                // A message of `len` bits fills its last byte from the top.
                let spare_bits = text.len() * 8 - test.int("payloadLen");
                if let Some(last) = text.last_mut() {
                    *last &= 0xff << spare_bits;
                }
                assert_eq!(text, test.hex(output));
            }
        }
    }

    #[test]
    fn key_length_must_match_algorithm() {
        let key = [0u8; 33];
        for algorithm in [&AES_128, &AES_192, &AES_256] {
            for len in 0..=key.len() {
                let supported = len == algorithm.key_len;
                assert_eq!(
                    Aes::new(algorithm, &key[..len]).is_ok(),
                    supported,
                    "len {len}"
                );
                assert_eq!(
                    AesCtr::new(algorithm, &key[..len], 32).is_ok(),
                    supported,
                    "len {len}"
                );
            }
        }
    }

    #[test]
    fn counter_bits_must_be_1_to_128() {
        for bits in 0..=u8::MAX {
            assert_eq!(
                AesCtr::new(&AES_128, &[0; 16], bits).is_ok(),
                (1..=128).contains(&bits),
                "{bits} bits"
            );
        }
    }

    #[test]
    fn cavp() {
        #[derive(Default)]
        struct State {
            mct: bool,
            decrypt: bool,
            key: Vec<u8>,
            pt: Vec<u8>,
            ct: Vec<u8>,
        }

        impl State {
            fn check(&self) {
                let rounds = if self.mct { 1000 } else { 1 };
                if self.decrypt {
                    let aes = AesDecKey::new(&self.key);
                    let mut block: [u8; 16] = self.ct[..].try_into().unwrap();
                    for _ in 0..rounds {
                        aes.decrypt_block(&mut block);
                    }
                    assert_eq!(block, &self.pt[..]);
                } else {
                    let aes = Aes::new(algorithm(&self.key), &self.key).unwrap();
                    let mut block: [u8; 16] = self.pt[..].try_into().unwrap();
                    for _ in 0..rounds {
                        aes.encrypt_block(&mut block);
                    }
                    assert_eq!(block, &self.ct[..]);
                }
            }
        }

        impl CavpSink for State {
            fn on_meta(&mut self, meta: &str) {
                self.decrypt = meta == "DECRYPT";
            }

            fn on_value(&mut self, name: &str, value: Value<'_>) {
                match name {
                    "COUNT" => {}
                    "KEY" => self.key = value.bytes(),
                    // decryption entries list the ciphertext first
                    "PLAINTEXT" => {
                        self.pt = value.bytes();
                        if self.decrypt {
                            self.check();
                        }
                    }
                    "CIPHERTEXT" => {
                        self.ct = value.bytes();
                        if !self.decrypt {
                            self.check();
                        }
                    }
                    _ => todo!("unhandled value {name} = {value:?}"),
                }
            }
        }

        for bits in [128, 192, 256] {
            for kind in ["GFSbox", "KeySbox", "VarKey", "VarTxt", "MCT"] {
                let mut state = State {
                    mct: kind == "MCT",
                    ..Default::default()
                };
                process_cavp(
                    format!("../thirdparty/vectors/cavp/aes/ECB{kind}{bits}.rsp"),
                    &mut state,
                );
            }
        }
    }

    #[test]
    fn rfc3686() {
        // test vectors #3, #6, and #9: three blocks, the last one partial
        for (key, nonce, ct) in [
            (
                "7691be035e5020a8ac6e618529f9a0dc",
                "00e0017b27777f3f4a1786f0",
                "c1cf48a89f2ffdd9cf4652e9efdb72d74540a42bde6d7836d59a5ceaaef3105325b2072f",
            ),
            (
                "02bf391ee8ecb159b959617b0965279bf59b60a786d3e0fe",
                "0007bdfd5cbd60278dcc0912",
                "96893fc55e5c722f540b7dd1ddf7e758d288bc95c69165884536c811662f2188abee0935",
            ),
            (
                "ff7a617ce69148e4f1726e2f43581de2aa62d9f805532edff1eed687fb54153d",
                "001cc5b751a51d70a1c11148",
                "eb6c52821d0bbbf7ce7594462aca4faab407df866569fd07f48cc0b583d6071f1ec0e6b8",
            ),
        ] {
            let key = hex::decode(key).unwrap();
            let ctr = AesCtr::new(algorithm(&key), &key, 32).unwrap();
            let block = hex::decode(format!("{nonce}00000001")).unwrap();
            let mut buf: Vec<u8> = (0u8..36).collect();
            ctr.apply_keystream(&block.try_into().unwrap(), &mut buf)
                .unwrap();
            assert_eq!(hex::encode(&buf), ct);
        }
    }

    #[test]
    fn sp800_38a() {
        // F.5.1, F.5.3, and F.5.5, CTR-AES128.Encrypt, CTR-AES192.Encrypt, and
        // CTR-AES256.Encrypt
        let pt = "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e51\
                  30c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710";
        for (key, ct) in [
            (
                "2b7e151628aed2a6abf7158809cf4f3c",
                "874d6191b620e3261bef6864990db6ce9806f66b7970fdff8617187bb9fffdff\
                 5ae4df3edbd5d35e5b4f09020db03eab1e031dda2fbe03d1792170a0f3009cee",
            ),
            (
                "8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b",
                "1abc932417521ca24f2b0459fe7e6e0b090339ec0aa6faefd5ccc2c6f4ce8e94\
                 1e36b26bd1ebc670d1bd1d665620abf74f78a7f6d29809585a97daec58c6b050",
            ),
            (
                "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4",
                "601ec313775789a5b7a7f504bbf3d228f443e3ca4d62b59aca84e990cacaf5c5\
                 2b0930daa23de94ce87017ba2d84988ddfc9c58db67aada613c2dd08457941a6",
            ),
        ] {
            let key = hex::decode(key).unwrap();
            let ctr = AesCtr::new(algorithm(&key), &key, 128).unwrap();
            let block = hex::decode("f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff").unwrap();
            let mut buf = hex::decode(pt).unwrap();
            ctr.apply_keystream(&block.try_into().unwrap(), &mut buf)
                .unwrap();
            assert_eq!(hex::encode(&buf), ct);
        }
    }

    #[test]
    fn srtp_aes_cm() {
        // RFC 3711 appendix B.2 and RFC 6188 section 7.1: one 65282-block
        // keystream segment, checked at both ends, under the 2^16-block cap
        // the IV's 16 zero bits leave.
        for (key, first, last) in [
            (
                "2b7e151628aed2a6abf7158809cf4f3c",
                "e03ead0935c95e80e166b16dd92b4eb4d23513162b02d0f72a43a2fe4a5f97ab41e95b3bb0a2e8dd477901e4fca894c0",
                "ec8cdf7398607cb0f2d21675ea9ea1e4362b7c3c6773516318a077d7fc5073ae6a2cc3787889374fbeb4c81b17ba6c44",
            ),
            (
                "57f82fe3613fd170a85ec93c40b1f0922ec4cb0dc025b58272147cc438944a98",
                "92bdd28a93c3f52511c677d08b5515a49da71b2378a854f67050756ded165bac63c4868b7096d88421b563b8c94c9a31",
                "cea518c90fd91ced9cbb18c078a547113dbc4814f4da5f00a08772b63c6a046d6eb246913062a16891433e97dd01a57f",
            ),
        ] {
            let key = hex::decode(key).unwrap();
            let ctr = AesCtr::new(algorithm(&key), &key, 16).unwrap();
            let iv = hex::decode("f0f1f2f3f4f5f6f7f8f9fafbfcfd0000").unwrap();
            let mut keystream = vec![0u8; 65282 * 16];
            ctr.apply_keystream(&iv.try_into().unwrap(), &mut keystream)
                .unwrap();
            assert_eq!(hex::encode(&keystream[..48]), first);
            assert_eq!(hex::encode(&keystream[keystream.len() - 48..]), last);
        }
    }

    // Every counter width against a model encrypting one counter block at a
    // time, from counters that wrap the counter or carry out of the backends'
    // 32-bit word, with the bits above the counter set so a carry into them
    // shows.
    #[test]
    fn counter_bits_match_model() {
        let key = [0x42u8; 16];
        let aes = Aes::new(&AES_128, &key).unwrap();
        let fixed = u128::from_be_bytes([0xa5; 16]);
        for bits in [1u8, 2, 7, 8, 16, 31, 32, 33, 63, 64, 96, 127, 128] {
            let ctr = AesCtr::new(&AES_128, &key, bits).unwrap();
            let mask = u128::MAX >> (128 - bits);
            let max_blocks = 1u128.checked_shl(bits.into()).unwrap_or(u128::MAX);
            let starts = [
                0,
                1,
                mask.wrapping_sub(3) & mask,
                mask,
                ((1 << 32) - 3) & mask,
            ];
            for start in starts {
                let lens: [usize; 12] = [0, 1, 15, 16, 17, 32, 33, 64, 127, 128, 129, 300];
                for len in lens
                    .into_iter()
                    .filter(|len| len.div_ceil(16) as u128 <= max_blocks)
                {
                    let what = format!("{bits} bits from {start:#x}, {len} bytes");
                    let block = (fixed & !mask) | start;
                    let msg: Vec<u8> = (0..len).map(|i| i as u8).collect();
                    let mut want = msg.clone();
                    for (i, chunk) in (0u128..).zip(want.chunks_mut(16)) {
                        let mut keystream =
                            ((block & !mask) | (block.wrapping_add(i) & mask)).to_be_bytes();
                        aes.encrypt_block(&mut keystream);
                        for (b, k) in chunk.iter_mut().zip(keystream) {
                            *b ^= k;
                        }
                    }
                    let mut got = msg;
                    ctr.apply_keystream(&block.to_be_bytes(), &mut got).unwrap();
                    assert_eq!(got, want, "{what}");
                }
            }
        }
    }

    #[test]
    fn aes_ctr_refuses_counter_reuse() {
        // 2^bits blocks wrap onto the first one only when one more is needed
        let block = [0xff; 16];
        for bits in [1u8, 4, 8] {
            let ctr = AesCtr::new(&AES_128, &[0x42; 16], bits).unwrap();
            let max = 16 << bits;
            for len in [0, max - 15, max] {
                ctr.apply_keystream(&block, &mut vec![0; len]).unwrap();
            }
            let mut buf = vec![0xaa; max + 1];
            assert_eq!(
                ctr.apply_keystream(&block, &mut buf),
                Err(Error::WrongLength),
                "{bits} bits"
            );
            assert!(buf.iter().all(|b| *b == 0xaa), "refused call wrote output");
        }
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn gcm_length_limits() {
        // 2^32 - 2 blocks
        let max_msg = (1 << 36) - 32;
        assert_eq!(check_gcm_lengths(0, max_msg), Ok(()));
        assert_eq!(check_gcm_lengths(0, max_msg + 1), Err(Error::WrongLength));

        let max_aad = (1 << 61) - 1;
        assert_eq!(check_gcm_lengths(max_aad, 0), Ok(()));
        assert_eq!(check_gcm_lengths(max_aad + 1, 0), Err(Error::WrongLength));
    }

    // armv7's AES block and AES-CTR on the crypto extension, which valgrind
    // hides, for each key size, with a secret key, block, and message, for
    // `admin/ct-qemu`. The message's 5 blocks take the CTR routine's 3-block
    // loop and 2-block tail, then its partial block a 1-block call.
    #[cfg(rind_backend = "arm")]
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu-arm"]
    fn ct_qemu_aes() {
        use crate::low::ct_qemu;

        let seed = ct_qemu::seed().to_le_bytes();
        let bytes = |n| seed.iter().cycle().take(n).copied().collect::<Vec<u8>>();
        for algorithm in [&AES_128, &AES_192, &AES_256] {
            let key = bytes(algorithm.key_len);
            let aes = ct_qemu::traced(|| Aes::new(algorithm, &key).unwrap());
            let ctr = ct_qemu::traced(|| AesCtr::new(algorithm, &key, 32).unwrap());
            assert!(matches!(aes.0, AesKey::Hw(_)), "the crypto extension");

            let mut block = bytes(16).try_into().unwrap();
            ct_qemu::traced(|| aes.encrypt_block(&mut block));
            let mut counter_block: [u8; 16] = bytes(16).try_into().unwrap();
            counter_block[12..].copy_from_slice(&7u32.to_be_bytes());
            let mut msg = bytes(5 * 16 + 8);
            ct_qemu::traced(|| ctr.apply_keystream(&counter_block, &mut msg)).unwrap();
        }
    }
}
