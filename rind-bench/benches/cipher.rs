#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, SIZES, Size, dit};

#[cfg(not(target_arch = "xtensa"))]
const IV: [u8; 16] = [0; 16];

#[cfg(not(target_arch = "xtensa"))]
fn rind_aes(key_len: usize) -> &'static rind::cipher::Algorithm {
    match key_len {
        16 => &rind::cipher::AES_128,
        24 => &rind::cipher::AES_192,
        _ => &rind::cipher::AES_256,
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn aws_aes(key_len: usize) -> &'static aws_lc_rs::cipher::Algorithm {
    use aws_lc_rs::cipher::{AES_128, AES_192, AES_256};
    match key_len {
        16 => &AES_128,
        24 => &AES_192,
        _ => &AES_256,
    }
}

/// A key and the buffer it encrypts in place each call: the same buffer, so
/// a call times the cipher alone, without an allocation or a copy of the
/// input.
#[cfg(not(target_arch = "xtensa"))]
struct Cipher<K> {
    key: K,
    buf: Vec<u8>,
}

macro_rules! ctr {
    ($len:literal) => {
        const KEY: [u8; $len] = [0; $len];

        fn aws_ctr(size: Size) -> Cipher<aws_lc_rs::cipher::EncryptingKey> {
            use aws_lc_rs::cipher::{EncryptingKey, UnboundCipherKey};
            let key = UnboundCipherKey::new(aws_aes($len), &KEY).unwrap();
            Cipher {
                key: EncryptingKey::ctr(key).unwrap(),
                buf: size.zeros(),
            }
        }

        #[bench(args = SIZES, setup = aws_ctr)]
        fn aws_lc_rs(
            c: &mut Cipher<aws_lc_rs::cipher::EncryptingKey>,
        ) -> aws_lc_rs::cipher::DecryptionContext {
            use aws_lc_rs::cipher::EncryptionContext;
            c.key
                .less_safe_encrypt(&mut c.buf, EncryptionContext::Iv128(IV.into()))
                .unwrap()
        }

        fn rind_ctr(size: Size) -> Dit<Cipher<rind::cipher::AesCtr>> {
            Dit::hold(Cipher {
                key: rind::cipher::AesCtr::new(rind_aes($len), &KEY, 128).unwrap(),
                buf: size.zeros(),
            })
        }

        #[bench(args = SIZES, setup = rind_ctr)]
        fn rind(c: &mut Dit<Cipher<rind::cipher::AesCtr>>) {
            let c = &mut **c;
            c.key.apply_keystream(&IV, &mut c.buf).unwrap();
        }

        /// The buffer, after checking verified-garbage's keystream matches
        /// rind's.
        fn vg_ctr(size: Size) -> Vec<u8> {
            use verified_garbage::cipher::aes::AesCtr;
            let mut expect = size.zeros();
            rind::cipher::AesCtr::new(rind_aes($len), &KEY, 128)
                .unwrap()
                .apply_keystream(&IV, &mut expect)
                .unwrap();
            let mut ct = size.zeros();
            AesCtr::new(&KEY, &IV)
                .unwrap()
                .apply_keystream_final(&mut ct);
            assert_eq!(ct, expect);
            size.zeros()
        }

        /// verified-garbage takes the IV only with the key, so each message
        /// expands the key again.
        #[bench(args = SIZES, setup = vg_ctr)]
        fn verified_garbage(buf: &mut [u8]) {
            use verified_garbage::cipher::aes::AesCtr;
            AesCtr::new(&KEY, &IV).unwrap().apply_keystream_final(buf)
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
mod aes128_ctr {
    use swole::bench;

    use super::*;
    ctr!(16);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes192_ctr {
    use swole::bench;

    use super::*;
    ctr!(24);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes256_ctr {
    use swole::bench;

    use super::*;
    ctr!(32);
}

/// A key, the input each call copies into a buffer of kept capacity, since
/// both directions work in place and decryption consumes its ciphertext, and
/// that buffer: the copy is the same for every library.
#[cfg(not(target_arch = "xtensa"))]
struct Cbc<K> {
    key: K,
    input: Vec<u8>,
    buf: Vec<u8>,
}

#[cfg(not(target_arch = "xtensa"))]
impl<K> Cbc<K> {
    /// `key` and the plaintext of `size`, or its ciphertext under rind when
    /// decrypting.
    fn new(key: K, key_bytes: &[u8], encrypt: bool, size: Size) -> Self {
        use rind::cipher::{AesCbcEncryptingKey, CbcIv};
        let mut ct = size.zeros();
        AesCbcEncryptingKey::new(rind_aes(key_bytes.len()), key_bytes)
            .unwrap()
            .encrypt(CbcIv::assume_unpredictable(IV), &mut ct)
            .unwrap();
        Self {
            key,
            input: if encrypt { size.zeros() } else { ct },
            buf: Vec::with_capacity(size.len + 16),
        }
    }
}

/// verified-garbage's CBC: it has no padding, so its row pads and unpads
/// here, and takes the IV only with the key, so each message expands the key
/// again.
#[cfg(not(target_arch = "xtensa"))]
fn vg_cbc(key: &[u8], encrypt: bool, input: &[u8], buf: &mut Vec<u8>) {
    use verified_garbage::cipher::aes::{AesCbcDecryptor, AesCbcEncryptor};
    buf.clear();
    buf.extend_from_slice(input);
    if encrypt {
        let size = input.len();
        let pad = 16 - size % 16;
        buf.resize(size + pad, pad as u8);
        AesCbcEncryptor::new(key, &IV)
            .unwrap()
            .encrypt(buf)
            .unwrap();
    } else {
        AesCbcDecryptor::new(key, &IV)
            .unwrap()
            .decrypt(buf)
            .unwrap();
        // Every padding byte, without branching on them, as rind checks it.
        let last = &buf[buf.len() - 16..];
        let pad = last[15];
        let mut bad = u8::from(pad == 0) | u8::from(pad > 16);
        for (i, &byte) in last.iter().enumerate() {
            bad |= u8::from(15 - i < usize::from(pad)) & u8::from(byte != pad);
        }
        assert_eq!(bad, 0);
        buf.truncate(buf.len() - usize::from(pad));
    }
}

/// AES-CBC with PKCS#7 padding, as WebCrypto runs it.
macro_rules! cbc {
    ($len:literal, $encrypt:literal) => {
        const KEY: [u8; $len] = [0; $len];

        type Aws = (
            aws_lc_rs::cipher::PaddedBlockEncryptingKey,
            aws_lc_rs::cipher::PaddedBlockDecryptingKey,
        );

        fn aws_cbc(size: Size) -> Cbc<Aws> {
            use aws_lc_rs::cipher::{
                PaddedBlockDecryptingKey, PaddedBlockEncryptingKey, UnboundCipherKey,
            };
            let key = || UnboundCipherKey::new(aws_aes($len), &KEY).unwrap();
            let enc = PaddedBlockEncryptingKey::cbc_pkcs7(key()).unwrap();
            let dec = PaddedBlockDecryptingKey::cbc_pkcs7(key()).unwrap();
            Cbc::new((enc, dec), &KEY, $encrypt, size)
        }

        #[bench(args = SIZES, setup = aws_cbc)]
        fn aws_lc_rs(c: &mut Cbc<Aws>) {
            use aws_lc_rs::cipher::{DecryptionContext, EncryptionContext};
            let (enc, dec) = &c.key;
            c.buf.clear();
            c.buf.extend_from_slice(&c.input);
            if $encrypt {
                enc.less_safe_encrypt(&mut c.buf, EncryptionContext::Iv128(IV.into()))
                    .unwrap();
            } else {
                dec.decrypt(&mut c.buf, DecryptionContext::Iv128(IV.into()))
                    .unwrap();
            }
        }

        type Rind = (
            rind::cipher::AesCbcEncryptingKey,
            rind::cipher::AesCbcDecryptingKey,
        );

        fn rind_cbc(size: Size) -> Dit<Cbc<Rind>> {
            use rind::cipher::{AesCbcDecryptingKey, AesCbcEncryptingKey};
            let enc = AesCbcEncryptingKey::new(rind_aes($len), &KEY).unwrap();
            let dec = AesCbcDecryptingKey::new(rind_aes($len), &KEY).unwrap();
            Dit::hold(Cbc::new((enc, dec), &KEY, $encrypt, size))
        }

        #[bench(args = SIZES, setup = rind_cbc)]
        fn rind(c: &mut Dit<Cbc<Rind>>) {
            use rind::cipher::CbcIv;
            let c = &mut **c;
            let (enc, dec) = &c.key;
            c.buf.clear();
            c.buf.extend_from_slice(&c.input);
            if $encrypt {
                enc.encrypt(CbcIv::assume_unpredictable(IV), &mut c.buf)
                    .unwrap();
            } else {
                dec.decrypt(&IV, &mut c.buf).unwrap();
            }
        }

        /// The input, after checking verified-garbage's output matches rind's.
        fn vg_setup(size: Size) -> Cbc<()> {
            use rind::cipher::{AesCbcDecryptingKey, AesCbcEncryptingKey, CbcIv};
            let mut c = Cbc::new((), &KEY, $encrypt, size);
            let mut expect = c.input.clone();
            if $encrypt {
                AesCbcEncryptingKey::new(rind_aes($len), &KEY)
                    .unwrap()
                    .encrypt(CbcIv::assume_unpredictable(IV), &mut expect)
                    .unwrap();
            } else {
                let len = AesCbcDecryptingKey::new(rind_aes($len), &KEY)
                    .unwrap()
                    .decrypt(&IV, &mut expect)
                    .unwrap()
                    .len();
                expect.truncate(len);
            }
            vg_cbc(&KEY, $encrypt, &c.input, &mut c.buf);
            assert_eq!(c.buf, expect);
            c
        }

        #[bench(args = SIZES, setup = vg_setup)]
        fn verified_garbage(c: &mut Cbc<()>) {
            vg_cbc(&KEY, $encrypt, &c.input, &mut c.buf);
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
mod aes128_cbc_encrypt {
    use swole::bench;

    use super::*;
    cbc!(16, true);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes128_cbc_decrypt {
    use swole::bench;

    use super::*;
    cbc!(16, false);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes192_cbc_encrypt {
    use swole::bench;

    use super::*;
    cbc!(24, true);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes192_cbc_decrypt {
    use swole::bench;

    use super::*;
    cbc!(24, false);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes256_cbc_encrypt {
    use swole::bench;

    use super::*;
    cbc!(32, true);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes256_cbc_decrypt {
    use swole::bench;

    use super::*;
    cbc!(32, false);
}

/// Expanding a CBC decryption key, as each message under a fresh key pays.
/// Each call drops its key, so the wiping is timed too. The modules take the
/// libraries' names, so every path names its crate from the root.
macro_rules! cbc_key {
    ($len:literal) => {
        const KEY: [u8; $len] = [0; $len];

        pub mod aws_lc_rs {
            use swole::bench;

            use super::*;

            #[bench]
            fn decrypt() {
                use ::aws_lc_rs::cipher::{PaddedBlockDecryptingKey, UnboundCipherKey};
                let key = UnboundCipherKey::new(aws_aes($len), black_box(&KEY[..])).unwrap();
                black_box(PaddedBlockDecryptingKey::cbc_pkcs7(key).unwrap());
            }
        }

        pub mod rind {
            use swole::bench;

            use super::*;

            #[bench(setup = dit)]
            fn decrypt(_: &Dit<()>) {
                black_box(
                    ::rind::cipher::AesCbcDecryptingKey::new(rind_aes($len), black_box(&KEY[..]))
                        .unwrap(),
                );
            }
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
mod aes128_cbc_key {
    use super::*;
    cbc_key!(16);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes192_cbc_key {
    use super::*;
    cbc_key!(24);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes256_cbc_key {
    use super::*;
    cbc_key!(32);
}

/// The bare ChaCha20 stream cipher, a fresh nonce per message. aws-lc-rs and
/// ring expose no ChaCha20 without Poly1305.
#[cfg(not(target_arch = "xtensa"))]
mod chacha20 {
    use swole::bench;

    use super::*;

    const KEY: [u8; 32] = [7; 32];
    const NONCE: [u8; 12] = [9; 12];

    fn rind_chacha(size: Size) -> Dit<Cipher<rind::cipher::ChaCha20>> {
        Dit::hold(Cipher {
            key: rind::cipher::ChaCha20::new(&KEY),
            buf: size.zeros(),
        })
    }

    #[bench(args = SIZES, setup = rind_chacha)]
    fn rind(c: &mut Dit<Cipher<rind::cipher::ChaCha20>>) {
        let c = &mut **c;
        c.key.apply_keystream(&NONCE, 0, &mut c.buf).unwrap();
    }

    type Vg = (verified_garbage::cipher::chacha20::ChaCha20, [u8; 16]);

    /// verified-garbage's cipher and its counter and nonce, after checking
    /// its keystream matches rind's.
    fn vg_chacha(size: Size) -> Cipher<Vg> {
        use verified_garbage::cipher::chacha20::ChaCha20;
        let mut counter_nonce = [0u8; 16];
        counter_nonce[4..].copy_from_slice(&NONCE);
        let mut expect = size.zeros();
        rind::cipher::ChaCha20::new(&KEY)
            .apply_keystream(&NONCE, 0, &mut expect)
            .unwrap();
        let mut cipher = ChaCha20::new(&KEY, &counter_nonce);
        let mut ct = size.zeros();
        cipher.apply_keystream(&mut ct);
        assert_eq!(ct, expect);
        Cipher {
            key: (cipher, counter_nonce),
            buf: size.zeros(),
        }
    }

    /// Restarting the keystream for the nonce is verified-garbage's
    /// per-message cost, as rind's call starts from the key and nonce.
    #[bench(args = SIZES, setup = vg_chacha)]
    fn verified_garbage(c: &mut Cipher<Vg>) {
        let (cipher, counter_nonce) = &mut c.key;
        cipher.reset_nonce(counter_nonce);
        cipher.apply_keystream(&mut c.buf);
    }
}

/// The QUIC header protection mask: one cipher call on a 16-byte sample.
#[cfg(not(target_arch = "xtensa"))]
mod quic_header_protection {
    use super::*;

    const SAMPLE: [u8; 16] = [0x5a; 16];

    /// verified-garbage's mask. As rustls does, the AES key is expanded
    /// once; ChaCha20 takes the sample as its counter and nonce, so each
    /// mask starts a cipher.
    struct VgMask {
        aes: Option<verified_garbage::cipher::aes::AesEcb>,
        chacha: [u8; 32],
    }

    impl VgMask {
        /// The mask for `key`, an AES one or else ChaCha20's, after checking it
        /// matches rind's.
        fn new(algorithm: &'static rind::aead::quic::Algorithm, key: &[u8], aes: bool) -> Self {
            use verified_garbage::cipher::aes::AesEcb;
            let mut chacha = [0u8; 32];
            chacha[..key.len()].copy_from_slice(key);
            let vg = Self {
                aes: aes.then(|| AesEcb::new(key).unwrap()),
                chacha,
            };
            let expect = rind::aead::quic::HeaderProtectionKey::new(algorithm, key)
                .unwrap()
                .mask(&SAMPLE);
            assert_eq!(vg.mask(), expect);
            vg
        }

        fn mask(&self) -> [u8; 5] {
            use verified_garbage::cipher::chacha20::ChaCha20;
            let mut mask = [0u8; 5];
            match &self.aes {
                Some(aes) => {
                    let mut block = SAMPLE;
                    aes.encrypt(&mut block).unwrap();
                    mask.copy_from_slice(&block[..5]);
                }
                None => ChaCha20::new(&self.chacha, &SAMPLE).apply_keystream(&mut mask),
            }
            mask
        }
    }

    macro_rules! hp {
        ($len:literal, $alg:ident, $aes:literal) => {
            const KEY: [u8; $len] = [0; $len];

            fn ring_key() -> ring::aead::quic::HeaderProtectionKey {
                ring::aead::quic::HeaderProtectionKey::new(&ring::aead::quic::$alg, &KEY).unwrap()
            }

            #[bench(setup = ring_key)]
            fn ring(key: &ring::aead::quic::HeaderProtectionKey) -> [u8; 5] {
                key.new_mask(&SAMPLE).unwrap()
            }

            fn aws_key() -> aws_lc_rs::aead::quic::HeaderProtectionKey {
                aws_lc_rs::aead::quic::HeaderProtectionKey::new(&aws_lc_rs::aead::quic::$alg, &KEY)
                    .unwrap()
            }

            #[bench(setup = aws_key)]
            fn aws_lc_rs(key: &aws_lc_rs::aead::quic::HeaderProtectionKey) -> [u8; 5] {
                key.new_mask(&SAMPLE).unwrap()
            }

            fn rind_key() -> Dit<rind::aead::quic::HeaderProtectionKey> {
                Dit::hold(
                    rind::aead::quic::HeaderProtectionKey::new(&rind::aead::quic::$alg, &KEY)
                        .unwrap(),
                )
            }

            #[bench(setup = rind_key)]
            fn rind(key: &Dit<rind::aead::quic::HeaderProtectionKey>) -> [u8; 5] {
                key.mask(&SAMPLE)
            }

            fn vg_key() -> VgMask {
                VgMask::new(&rind::aead::quic::$alg, &KEY, $aes)
            }

            #[bench(setup = vg_key)]
            fn verified_garbage(vg: &VgMask) -> [u8; 5] {
                vg.mask()
            }

            #[cfg(target_arch = "aarch64")]
            #[bench(setup = vg_key)]
            fn verified_garbage_dit_held(
                vg: &VgMask,
                iterations: swole::Iterations,
            ) -> std::time::Duration {
                common::vg_dit_held(iterations, || verified_garbage(vg))
            }
        };
    }

    mod aes128 {
        use swole::bench;

        use super::*;
        hp!(16, AES_128, true);
    }

    mod aes256 {
        use swole::bench;

        use super::*;
        hp!(32, AES_256, true);
    }

    mod chacha20 {
        use swole::bench;

        use super::*;
        hp!(32, CHACHA20, false);
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
