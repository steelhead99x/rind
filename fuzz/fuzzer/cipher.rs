#![no_main]

//! The bare ciphers against aws-lc's and RustCrypto's: the AES block, AES-CTR
//! with any counter width, ChaCha20 from any block, and QUIC header
//! protection.
//!
//! aws-lc-rs's CTR counts over the whole block, so a narrower counter's
//! keystream is aws-lc-rs's AES on each counter block the width allows, and
//! RustCrypto's AES on the same blocks, beside RustCrypto's CTR for the
//! widths it has. aws-lc-rs has no bare ChaCha20, so that calls aws-lc
//! directly, and RustCrypto's ChaCha20 core, since its stream refuses to
//! reach the last block.

use ::aes::cipher::{BlockCipherEncrypt, KeyInit, KeyIvInit, StreamCipher, StreamCipherCore};
use aws_lc_rs::aead::quic;
use aws_lc_rs::cipher::{EncryptingKey, EncryptionContext, UnboundCipherKey};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::cipher::{Aes, AesCtr, ChaCha20};

mod rustcrypto;

use rustcrypto::rustcrypto_aes;

#[derive(Arbitrary, Debug)]
enum Input {
    AesBlock {
        key: AesKey,
        block: [u8; 16],
    },
    AesCtr {
        key: AesKey,
        counter_bits: u8,
        counter_block: [u8; 16],
        message: Vec<u8>,
    },
    ChaCha20 {
        key: [u8; 32],
        nonce: [u8; 12],
        counter: u32,
        message: Vec<u8>,
    },
    QuicHeaderProtection {
        algorithm: Quic,
        key: [u8; 32],
        sample: [u8; 16],
    },
}

#[derive(Arbitrary, Debug)]
enum AesKey {
    Aes128([u8; 16]),
    Aes192([u8; 24]),
    Aes256([u8; 32]),
}

impl AesKey {
    fn bytes(&self) -> &[u8] {
        match self {
            Self::Aes128(key) => key,
            Self::Aes192(key) => key,
            Self::Aes256(key) => key,
        }
    }

    fn ours(&self) -> (&'static rind::cipher::Algorithm, &[u8]) {
        match self {
            Self::Aes128(key) => (&rind::cipher::AES_128, key),
            Self::Aes192(key) => (&rind::cipher::AES_192, key),
            Self::Aes256(key) => (&rind::cipher::AES_256, key),
        }
    }

    /// aws-lc-rs's AES in ECB mode, the bare block cipher.
    fn theirs(&self) -> EncryptingKey {
        use aws_lc_rs::cipher::{AES_128, AES_192, AES_256};
        let key = match self {
            Self::Aes128(key) => UnboundCipherKey::new(&AES_128, key),
            Self::Aes192(key) => UnboundCipherKey::new(&AES_192, key),
            Self::Aes256(key) => UnboundCipherKey::new(&AES_256, key),
        };
        EncryptingKey::ecb(key.unwrap()).unwrap()
    }
}

#[derive(Arbitrary, Debug)]
enum Quic {
    Aes128,
    Aes256,
    ChaCha20,
}

fuzz_target!(|input: Input| match input {
    Input::AesBlock { key, block } => {
        let (algorithm, bytes) = key.ours();
        let mut ours = block;
        Aes::new(algorithm, bytes).unwrap().encrypt_block(&mut ours);
        let mut theirs = block;
        key.theirs()
            .less_safe_encrypt(&mut theirs, EncryptionContext::None)
            .unwrap();
        assert_eq!(ours, theirs);
        assert_eq!(&ours[..], rustcrypto_blocks(&key, &block));
    }
    Input::AesCtr {
        key,
        counter_bits,
        counter_block,
        message,
    } => aes_ctr(&key, counter_bits, &counter_block, message),
    Input::ChaCha20 {
        key,
        nonce,
        counter,
        message,
    } => {
        let mut ours = message.clone();
        let result = ChaCha20::new(&key).apply_keystream(&nonce, counter, &mut ours);
        // aws-lc wraps the counter, which would repeat keystream.
        let blocks = message.len().div_ceil(64) as u64;
        if u64::from(counter) + blocks > 1 << 32 {
            assert_eq!(result, Err(rind::Error::WrongLength));
            assert_eq!(ours, message);
            return;
        }
        result.unwrap();
        let mut theirs = vec![0; message.len()];
        // SAFETY: `theirs` and `message` are `message.len()` bytes, and the
        // key and nonce are 32 and 12.
        unsafe {
            aws_lc_sys::CRYPTO_chacha_20(
                theirs.as_mut_ptr(),
                message.as_ptr(),
                message.len(),
                key.as_ptr(),
                nonce.as_ptr(),
                counter,
            );
        }
        assert_eq!(ours, theirs);
        let keystream = rustcrypto_chacha20(&key, &nonce, counter, message.len());
        let independent: Vec<u8> = message.iter().zip(&keystream).map(|(m, k)| m ^ k).collect();
        assert_eq!(ours, independent);
    }
    Input::QuicHeaderProtection {
        algorithm,
        key,
        sample,
    } => {
        use rind::aead::quic as ours;
        let (chacha, algorithm, theirs) = match algorithm {
            Quic::Aes128 => (false, &ours::AES_128, &quic::AES_128),
            Quic::Aes256 => (false, &ours::AES_256, &quic::AES_256),
            Quic::ChaCha20 => (true, &ours::CHACHA20, &quic::CHACHA20),
        };
        let key = &key[..algorithm.key_len()];
        let mask = ours::HeaderProtectionKey::new(algorithm, key)
            .unwrap()
            .mask(&sample);
        let wanted = quic::HeaderProtectionKey::new(theirs, key)
            .unwrap()
            .new_mask(&sample)
            .unwrap();
        assert_eq!(mask, wanted);

        // RFC 9001 section 5.4: AES encrypts the sample, and ChaCha20 takes
        // its first four bytes as the block counter and the rest as the
        // nonce.
        let independent = match chacha {
            true => {
                let counter = u32::from_le_bytes(sample[..4].try_into().unwrap());
                let nonce = sample[4..].try_into().unwrap();
                rustcrypto_chacha20(key.try_into().unwrap(), nonce, counter, 5)
            }
            false => rustcrypto_aes!(key, Aes => {
                let mut block = sample.into();
                Aes::new_from_slice(key).unwrap().encrypt_block(&mut block);
                block[..5].to_vec()
            }),
        };
        assert_eq!(&mask[..], &independent[..]);
    }
});

/// RustCrypto's AES encryption of each block of `blocks`, whole blocks.
fn rustcrypto_blocks(key: &AesKey, blocks: &[u8]) -> Vec<u8> {
    let key = key.bytes();
    rustcrypto_aes!(key, Aes => {
        let aes = Aes::new_from_slice(key).unwrap();
        blocks
            .chunks(16)
            .flat_map(|block| {
                let mut block = <[u8; 16]>::try_from(block).unwrap().into();
                aes.encrypt_block(&mut block);
                <[u8; 16]>::from(block)
            })
            .collect()
    })
}

/// `len` bytes of RustCrypto's ChaCha20 keystream from block `counter`,
/// through its core, which reaches the last block, as its stream does not.
fn rustcrypto_chacha20(key: &[u8; 32], nonce: &[u8; 12], counter: u32, len: usize) -> Vec<u8> {
    use chacha20::{ChaChaCore, R20, variants::Ietf};
    let mut core = ChaChaCore::<R20, Ietf>::new(key.into(), nonce.into());
    core.set_block_pos(counter);
    let mut keystream = Vec::with_capacity(len.next_multiple_of(64));
    for _ in 0..len.div_ceil(64) {
        let mut block = Default::default();
        core.write_keystream_block(&mut block);
        keystream.extend_from_slice(&block);
    }
    keystream.truncate(len);
    keystream
}

/// AES-CTR counting over the rightmost `counter_bits` bits of the counter
/// block, which rind refuses outside 1 to 128 bits, and for a message that
/// would wrap the counter onto a block already used.
fn aes_ctr(key: &AesKey, counter_bits: u8, counter_block: &[u8; 16], message: Vec<u8>) {
    let (algorithm, bytes) = key.ours();
    let ours = AesCtr::new(algorithm, bytes, counter_bits);
    if !(1..=128).contains(&counter_bits) {
        assert!(ours.is_err());
        return;
    }
    let mask = u128::MAX >> (128 - counter_bits);
    let blocks = message.len().div_ceil(16);
    let mut ours_out = message.clone();
    let result = ours.unwrap().apply_keystream(counter_block, &mut ours_out);
    if blocks.saturating_sub(1) as u128 > mask {
        assert_eq!(result, Err(rind::Error::WrongLength));
        assert_eq!(ours_out, message);
        return;
    }
    result.unwrap();

    // Each block's keystream is the counter block, its counting bits
    // advanced by the block's index and wrapping within them, encrypted.
    let start = u128::from_be_bytes(*counter_block);
    let mut keystream: Vec<u8> = (0..blocks as u128)
        .flat_map(|i| ((start & !mask) | (start.wrapping_add(i) & mask)).to_be_bytes())
        .collect();
    let independent: Vec<u8> = message
        .iter()
        .zip(rustcrypto_blocks(key, &keystream))
        .map(|(m, k)| m ^ k)
        .collect();
    if !keystream.is_empty() {
        key.theirs()
            .less_safe_encrypt(&mut keystream, EncryptionContext::None)
            .unwrap();
    }
    let theirs: Vec<u8> = message.iter().zip(&keystream).map(|(m, k)| m ^ k).collect();
    assert_eq!(ours_out, theirs);
    assert_eq!(ours_out, independent);

    // RustCrypto's own CTR, for the widths it counts over.
    let mut independent = message.clone();
    rustcrypto_aes!(bytes, Aes => match counter_bits {
        32 => ctr::Ctr32BE::<Aes>::new_from_slices(bytes, counter_block)
            .unwrap()
            .apply_keystream(&mut independent),
        64 => ctr::Ctr64BE::<Aes>::new_from_slices(bytes, counter_block)
            .unwrap()
            .apply_keystream(&mut independent),
        128 => ctr::Ctr128BE::<Aes>::new_from_slices(bytes, counter_block)
            .unwrap()
            .apply_keystream(&mut independent),
        _ => return,
    });
    assert_eq!(ours_out, independent);
}
