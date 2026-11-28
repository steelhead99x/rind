//! Differential tests of the hashes, HMAC, constant-time comparison,
//! ciphers, key wrap, HKDF, PBKDF2, and AEADs against aws-lc and independent
//! oracles, which Miri cannot run.
#![cfg(not(any(miri, target_family = "wasm")))]

use aws_lc_rs::{digest, hmac};
use proptest::collection::vec;
use proptest::prelude::*;

/// aws-lc's hash of a message: through aws-lc-rs, or aws-lc-sys's EVP
/// interface for MD5, which aws-lc-rs does not export.
enum Theirs {
    AwsLcRs(&'static digest::Algorithm),
    Md5,
}

impl Theirs {
    fn digest(&self, message: &[u8]) -> Vec<u8> {
        match self {
            Self::AwsLcRs(algorithm) => digest::digest(algorithm, message).as_ref().to_vec(),
            Self::Md5 => {
                let mut out = [0u8; 16];
                // SAFETY: `message` is readable for its length, and `out` is
                // writable for MD5's 16-byte digest.
                let ok = unsafe {
                    aws_lc_sys::EVP_Digest(
                        message.as_ptr().cast(),
                        message.len(),
                        out.as_mut_ptr(),
                        core::ptr::null_mut(),
                        aws_lc_sys::EVP_md5(),
                        core::ptr::null_mut(),
                    )
                };
                assert_eq!(ok, 1);
                out.to_vec()
            }
        }
    }
}

/// RustCrypto's hash of a message.
type Independent = fn(&[u8]) -> Vec<u8>;

fn rustcrypto<D: sha2::Digest>(message: &[u8]) -> Vec<u8> {
    D::digest(message).to_vec()
}

/// Each hash rind offers, with aws-lc's, RustCrypto's, and its block size.
fn hashes() -> [(&'static rind::digest::Algorithm, Theirs, Independent, usize); 9] {
    use Theirs::*;
    [
        (&rind::digest::legacy::MD5, Md5, rustcrypto::<md5::Md5>, 64),
        (
            &rind::digest::legacy::SHA1,
            AwsLcRs(&digest::SHA1_FOR_LEGACY_USE_ONLY),
            rustcrypto::<sha1::Sha1>,
            64,
        ),
        (
            &rind::digest::SHA256,
            AwsLcRs(&digest::SHA256),
            rustcrypto::<sha2::Sha256>,
            64,
        ),
        (
            &rind::digest::SHA384,
            AwsLcRs(&digest::SHA384),
            rustcrypto::<sha2::Sha384>,
            128,
        ),
        (
            &rind::digest::SHA512,
            AwsLcRs(&digest::SHA512),
            rustcrypto::<sha2::Sha512>,
            128,
        ),
        (
            &rind::digest::SHA512_256,
            AwsLcRs(&digest::SHA512_256),
            rustcrypto::<sha2::Sha512_256>,
            128,
        ),
        (
            &rind::digest::SHA3_256,
            AwsLcRs(&digest::SHA3_256),
            rustcrypto::<sha3::Sha3_256>,
            136,
        ),
        (
            &rind::digest::SHA3_384,
            AwsLcRs(&digest::SHA3_384),
            rustcrypto::<sha3::Sha3_384>,
            104,
        ),
        (
            &rind::digest::SHA3_512,
            AwsLcRs(&digest::SHA3_512),
            rustcrypto::<sha3::Sha3_512>,
            72,
        ),
    ]
}

// Every length to three of SHA-2's larger blocks, so each tail lands on both
// sides of the length field for both block sizes, and SHA-3's padding lands
// in one byte, two, or a block of its own. One-shot, and in updates that end
// on each block boundary, which leave SHA-2 a whole block buffered.
#[test]
fn hashes_every_length() {
    let message: Vec<u8> = (0..3 * 128 + 1).map(|i| (i * 7 + 3) as u8).collect();
    for (ours, theirs, independent, block) in hashes() {
        for len in 0..=message.len() {
            let message = &message[..len];
            let wanted = theirs.digest(message);
            assert_eq!(independent(message), wanted, "{ours:?} RustCrypto {len}");
            let got = rind::digest::digest(ours, message);
            assert_eq!(got.as_ref(), wanted, "{ours:?} one-shot {len}");

            let mut ctx = rind::digest::Context::new(ours);
            for part in message.chunks(block) {
                ctx.update(part);
            }
            assert_eq!(ctx.finish().as_ref(), wanted, "{ours:?} blockwise {len}");
        }
    }
}

/// RustCrypto's HMAC of a message under a key.
type Hmac = fn(&[u8], &[u8]) -> Vec<u8>;

fn rustcrypto_hmac<D: ::hmac::EagerHash>(key: &[u8], message: &[u8]) -> Vec<u8> {
    use ::hmac::{KeyInit, Mac};
    let mut mac = ::hmac::Hmac::<D>::new_from_slice(key).unwrap();
    mac.update(message);
    mac.finalize().into_bytes().to_vec()
}

proptest! {
    #[test]
    fn hashes_match(
        message in vec(any::<u8>(), 0..1024),
        splits in vec(any::<prop::sample::Index>(), 0..4),
    ) {
        // Updates split anywhere exercise the partial-block buffering: one
        // that fills a block exactly, or spans several, after a partial one.
        let mut splits: Vec<_> = splits.iter().map(|s| s.index(message.len() + 1)).collect();
        splits.sort();
        for (ours, theirs, independent, _) in hashes() {
            let mut ctx = rind::digest::Context::new(ours);
            let mut start = 0;
            for &end in splits.iter().chain([&message.len()]) {
                ctx.update(&message[start..end]);
                start = end;
            }
            let got = ctx.finish();
            prop_assert_eq!(got.as_ref(), theirs.digest(&message));
            prop_assert_eq!(got.as_ref(), independent(&message));
        }
    }

    #[test]
    fn hmac_matches(
        // Up to 300 bytes spans keys below, at, and above both block sizes (64 and 128).
        key in vec(any::<u8>(), 0..300),
        message in vec(any::<u8>(), 0..1024),
        split in any::<prop::sample::Index>(),
    ) {
        let split = split.index(message.len() + 1);
        for (ours, theirs, independent) in [
            (&rind::hmac::legacy::HMAC_SHA1, hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY, rustcrypto_hmac::<sha1::Sha1> as Hmac),
            (&rind::hmac::HMAC_SHA256, hmac::HMAC_SHA256, rustcrypto_hmac::<sha2::Sha256>),
            (&rind::hmac::HMAC_SHA384, hmac::HMAC_SHA384, rustcrypto_hmac::<sha2::Sha384>),
            (&rind::hmac::HMAC_SHA512, hmac::HMAC_SHA512, rustcrypto_hmac::<sha2::Sha512>),
        ] {
            let ours = rind::hmac::Key::new(ours, &key);
            let mut ctx = rind::hmac::Context::with_key(&ours);
            ctx.update(&message[..split]);
            ctx.update(&message[split..]);
            let wanted = hmac::sign(&hmac::Key::new(theirs, &key), &message);
            let got = ctx.sign();
            prop_assert_eq!(got.as_ref(), wanted.as_ref());
            prop_assert_eq!(got.as_ref(), independent(&key, &message));
            prop_assert_eq!(rind::hmac::verify(&ours, &message, wanted.as_ref()), Ok(()));
        }
    }

    #[test]
    fn slice_comparison_matches_aws_lc_rs(
        a in vec(any::<u8>(), 0..64),
        other in vec(any::<u8>(), 0..64),
        flip in any::<prop::sample::Index>(),
    ) {
        let mut flipped = a.clone();
        if !flipped.is_empty() {
            flipped[flip.index(a.len())] ^= 1;
        }
        for b in [&a, &flipped, &other] {
            let ours = rind::constant_time::verify(&a, b);
            let theirs = aws_lc_rs::constant_time::verify_slices_are_equal(&a, b);
            prop_assert_eq!(ours.is_ok(), theirs.is_ok());
            let wanted = if a.len() != b.len() {
                Err(rind::Error::WrongLength)
            } else if a != *b {
                Err(rind::Error::NotEqual)
            } else {
                Ok(())
            };
            prop_assert_eq!(ours, wanted);
        }
    }
}

/// Runs `$body` with `$aes` naming RustCrypto's AES type for the size of
/// `$key`: 16, 24, or 32 bytes.
macro_rules! rustcrypto_aes {
    ($key:expr, $aes:ident => $body:expr) => {
        match $key.len() {
            16 => {
                type $aes = aes::Aes128;
                $body
            }
            24 => {
                type $aes = aes::Aes192;
                $body
            }
            _ => {
                type $aes = aes::Aes256;
                $body
            }
        }
    };
}

mod cipher {
    use aes::cipher::block_padding::{NoPadding, Pkcs7};
    use aes::cipher::{
        BlockCipherEncrypt, BlockModeDecrypt, BlockModeEncrypt, KeyInit, KeyIvInit, StreamCipher,
        StreamCipherCore, StreamCipherSeek,
    };
    use aws_lc_rs::aead::{Aad, CHACHA20_POLY1305, LessSafeKey, Nonce, UnboundKey, quic};
    use aws_lc_rs::cipher::{
        AES_128, AES_192, AES_256, DecryptingKey, DecryptionContext, EncryptingKey,
        EncryptionContext, PaddedBlockDecryptingKey, PaddedBlockEncryptingKey, UnboundCipherKey,
    };
    use proptest::prelude::*;
    use rind::Error;
    use rind::cipher::{
        self, Aes, AesCbcDecryptingKey, AesCbcEncryptingKey, AesCtr, CbcIv, ChaCha20,
    };

    fn aes_key() -> impl Strategy<Value = Vec<u8>> {
        prop::sample::select(&[16, 24, 32][..])
            .prop_flat_map(|len| prop::collection::vec(any::<u8>(), len))
    }

    fn rind_aes_algorithm(key: &[u8]) -> &'static cipher::Algorithm {
        match key.len() {
            16 => &cipher::AES_128,
            24 => &cipher::AES_192,
            _ => &cipher::AES_256,
        }
    }

    fn aws_aes_key(key: &[u8]) -> UnboundCipherKey {
        let alg = match key.len() {
            16 => &AES_128,
            24 => &AES_192,
            _ => &AES_256,
        };
        UnboundCipherKey::new(alg, key).unwrap()
    }

    // Counter blocks near a 32-bit or the 128-bit wrap exercise the carries.
    fn counter_block() -> impl Strategy<Value = [u8; 16]> {
        prop_oneof![
            any::<[u8; 16]>(),
            (any::<u128>(), (u32::MAX - 80)..=u32::MAX)
                .prop_map(
                    |(high, low)| (high & !u128::from(u32::MAX) | u128::from(low)).to_be_bytes()
                ),
            ((u128::MAX - 80)..=u128::MAX).prop_map(u128::to_be_bytes),
        ]
    }

    proptest! {
        #[test]
        fn aes_block(key in aes_key(), block in any::<[u8; 16]>()) {
            let mut ours = block;
            Aes::new(rind_aes_algorithm(&key), &key).unwrap().encrypt_block(&mut ours);

            let mut theirs = block;
            EncryptingKey::ecb(aws_aes_key(&key))
                .unwrap()
                .less_safe_encrypt(&mut theirs, EncryptionContext::None)
                .unwrap();
            prop_assert_eq!(ours, theirs);

            let mut independent = block.into();
            rustcrypto_aes!(key, Aes => Aes::new_from_slice(&key).unwrap().encrypt_block(&mut independent));
            prop_assert_eq!(ours, <[u8; 16]>::from(independent));
        }

        #[test]
        fn aes_ctr(
            key in aes_key(),
            counter_block in counter_block(),
            msg in prop::collection::vec(any::<u8>(), 0..1100),
        ) {
            // aws-lc-rs's counter is the whole block
            let mut ours = msg.clone();
            AesCtr::new(rind_aes_algorithm(&key), &key, 128)
                .unwrap()
                .apply_keystream(&counter_block, &mut ours)
                .unwrap();

            let mut theirs = msg.clone();
            if !theirs.is_empty() {
                EncryptingKey::ctr(aws_aes_key(&key))
                    .unwrap()
                    .less_safe_encrypt(&mut theirs, EncryptionContext::Iv128(counter_block.into()))
                    .unwrap();
            }
            prop_assert_eq!(&ours, &theirs);

            let mut independent = msg.clone();
            rustcrypto_aes!(key, Aes => ctr::Ctr128BE::<Aes>::new_from_slices(&key, &counter_block)
                .unwrap()
                .apply_keystream(&mut independent));
            prop_assert_eq!(&ours, &independent);
        }

        // Both ways, then a ciphertext of whole blocks with its last two
        // bytes forced, so that both well-formed and malformed padding come
        // up often: rind decrypts or refuses each as aws-lc-rs does.
        #[test]
        fn aes_cbc_pkcs7(
            key in aes_key(),
            iv in any::<[u8; 16]>(),
            msg in prop::collection::vec(any::<u8>(), 0..1100),
            forged in (1..70usize).prop_flat_map(|n| prop::collection::vec(any::<u8>(), 16 * n)),
            tail in (0u8..=17, 0u8..=2),
        ) {
            let algorithm = rind_aes_algorithm(&key);
            let enc = AesCbcEncryptingKey::new(algorithm, &key).unwrap();
            let dec = AesCbcDecryptingKey::new(algorithm, &key).unwrap();
            let theirs_dec = PaddedBlockDecryptingKey::cbc_pkcs7(aws_aes_key(&key)).unwrap();

            let mut ours = msg.clone();
            enc.encrypt(CbcIv::assume_unpredictable(iv), &mut ours)
                .unwrap();
            let mut theirs = msg.clone();
            PaddedBlockEncryptingKey::cbc_pkcs7(aws_aes_key(&key))
                .unwrap()
                .less_safe_encrypt(&mut theirs, EncryptionContext::Iv128(iv.into()))
                .unwrap();
            prop_assert_eq!(&ours, &theirs);
            let independent = rustcrypto_aes!(key, Aes => cbc::Encryptor::<Aes>::new_from_slices(&key, &iv)
                .unwrap()
                .encrypt_padded_vec::<Pkcs7>(&msg));
            prop_assert_eq!(&ours, &independent);
            prop_assert_eq!(dec.decrypt(&iv, &mut ours).unwrap(), &msg[..]);

            // Choose the plaintext's last bytes, then encrypt it unpadded.
            let mut forged = forged;
            let len = forged.len();
            forged[len - 1] = tail.0;
            forged[len - 2] = if tail.1 == 0 { tail.0 } else { forged[len - 2] };
            let mut ct = forged.clone();
            enc.encrypt_blocks(CbcIv::assume_unpredictable(iv), &mut ct).unwrap();
            let mut ours = ct.clone();
            let ours = dec.decrypt(&iv, &mut ours).map(|pt| pt.to_vec());
            let mut theirs = ct.clone();
            let theirs = theirs_dec
                .decrypt(&mut theirs, DecryptionContext::Iv128(iv.into()))
                .map(|pt| pt.to_vec());
            let independent = rustcrypto_aes!(key, Aes => cbc::Decryptor::<Aes>::new_from_slices(&key, &iv)
                .unwrap()
                .decrypt_padded_vec::<Pkcs7>(&ct));
            match (ours, theirs, independent) {
                (Ok(ours), Ok(theirs), Ok(independent)) => {
                    prop_assert_eq!(&ours, &theirs);
                    prop_assert_eq!(&ours, &independent);
                }
                (Err(Error::DecryptFailed), Err(_), Err(_)) => {}
                (ours, theirs, independent) => prop_assert!(
                    false,
                    "rind {:?}, aws-lc-rs {:?}, RustCrypto {:?}",
                    ours,
                    theirs,
                    independent
                ),
            }
        }

        #[test]
        fn aes_cbc_unpadded(
            key in aes_key(),
            iv in any::<[u8; 16]>(),
            msg in (0..70usize).prop_flat_map(|n| prop::collection::vec(any::<u8>(), 16 * n)),
        ) {
            let algorithm = rind_aes_algorithm(&key);
            let mut ours = msg.clone();
            AesCbcEncryptingKey::new(algorithm, &key)
                .unwrap()
                .encrypt_blocks(CbcIv::assume_unpredictable(iv), &mut ours)
                .unwrap();

            let mut theirs = msg.clone();
            if !theirs.is_empty() {
                EncryptingKey::cbc(aws_aes_key(&key))
                    .unwrap()
                    .less_safe_encrypt(&mut theirs, EncryptionContext::Iv128(iv.into()))
                    .unwrap();
            }
            prop_assert_eq!(&ours, &theirs);
            let independent = rustcrypto_aes!(key, Aes => cbc::Encryptor::<Aes>::new_from_slices(&key, &iv)
                .unwrap()
                .encrypt_padded_vec::<NoPadding>(&msg));
            prop_assert_eq!(&ours, &independent);
            let decrypted = rustcrypto_aes!(key, Aes => cbc::Decryptor::<Aes>::new_from_slices(&key, &iv)
                .unwrap()
                .decrypt_padded_vec::<NoPadding>(&ours));
            prop_assert_eq!(decrypted.unwrap(), &msg[..]);

            AesCbcDecryptingKey::new(algorithm, &key)
                .unwrap()
                .decrypt_blocks(&iv, &mut ours)
                .unwrap();
            prop_assert_eq!(&ours, &msg);
            if !theirs.is_empty() {
                DecryptingKey::cbc(aws_aes_key(&key))
                    .unwrap()
                    .decrypt(&mut theirs, DecryptionContext::Iv128(iv.into()))
                    .unwrap();
            }
            prop_assert_eq!(&theirs, &msg);
        }

        #[test]
        fn quic_header_protection_mask(
            index in 0..3usize,
            key in any::<[u8; 32]>(),
            // Often ChaCha20's last block counter, or the one before it.
            sample in (any::<[u8; 16]>(), 0..3u8).prop_map(|(mut sample, last)| {
                if last > 0 {
                    sample[..4].copy_from_slice(&(u32::MAX - u32::from(last - 1)).to_le_bytes());
                }
                sample
            }),
        ) {
            use rind::aead::quic as ours;
            let (algorithm, theirs) = [
                (&ours::AES_128, &quic::AES_128),
                (&ours::AES_256, &quic::AES_256),
                (&ours::CHACHA20, &quic::CHACHA20),
            ][index];
            let key = &key[..algorithm.key_len()];

            let mask = ours::HeaderProtectionKey::new(algorithm, key).unwrap().mask(&sample);
            let wanted = quic::HeaderProtectionKey::new(theirs, key)
                .unwrap()
                .new_mask(&sample)
                .unwrap();
            prop_assert_eq!(mask, wanted);

            // RFC 9001 section 5.4: AES encrypts the sample, and ChaCha20
            // takes its first four bytes as the block counter and the rest
            // as the nonce. The counter may be the last, which RustCrypto's
            // `ChaCha20` refuses to seek to, so this runs its core.
            let independent: [u8; 16] = if index == 2 {
                let mut core = chacha20::ChaChaCore::<chacha20::R20, chacha20::variants::Ietf>::new_from_slices(key, &sample[4..]).unwrap();
                core.set_block_pos(u32::from_le_bytes(sample[..4].try_into().unwrap()));
                let mut block = Default::default();
                core.write_keystream_block(&mut block);
                block[..16].try_into().unwrap()
            } else {
                let mut block = sample.into();
                rustcrypto_aes!(key, Aes => Aes::new_from_slice(key).unwrap().encrypt_block(&mut block));
                block.into()
            };
            prop_assert_eq!(&mask[..], &independent[..5]);
        }

        // ChaCha20-Poly1305's ciphertext is the plaintext XORed with the
        // keystream from block 1, which checks long, ragged outputs.
        #[test]
        fn chacha20_keystream(
            key in any::<[u8; 32]>(),
            nonce in any::<[u8; 12]>(),
            msg in prop::collection::vec(any::<u8>(), 0..1100),
        ) {
            let mut ours = msg.clone();
            ChaCha20::new(&key).apply_keystream(&nonce, 1, &mut ours).unwrap();

            let mut theirs = msg.clone();
            let _tag = LessSafeKey::new(UnboundKey::new(&CHACHA20_POLY1305, &key).unwrap())
                .seal_in_place_separate_tag(
                    Nonce::assume_unique_for_key(nonce),
                    Aad::empty(),
                    &mut theirs,
                )
                .unwrap();
            prop_assert_eq!(&ours, &theirs);

            let mut independent = msg.clone();
            let mut cipher = chacha20::ChaCha20::new_from_slices(&key, &nonce).unwrap();
            cipher.seek(64);
            cipher.apply_keystream(&mut independent);
            prop_assert_eq!(&ours, &independent);
        }
    }

    // Every length through the backends' boundaries, at once and split into
    // two calls at each block boundary.
    #[test]
    fn chacha20_every_length() {
        let key = core::array::from_fn(|i| i as u8);
        let nonce = core::array::from_fn(|i| (i * 7) as u8);
        let mut theirs = vec![0u8; 600];
        let _tag = LessSafeKey::new(UnboundKey::new(&CHACHA20_POLY1305, &key).unwrap())
            .seal_in_place_separate_tag(
                Nonce::assume_unique_for_key(nonce),
                Aad::empty(),
                &mut theirs,
            )
            .unwrap();
        let mut independent = vec![0u8; 600];
        let mut cipher = chacha20::ChaCha20::new_from_slices(&key, &nonce).unwrap();
        cipher.seek(64);
        cipher.apply_keystream(&mut independent);
        assert_eq!(theirs, independent);

        let ours = ChaCha20::new(&key);
        for len in 0..=600 {
            let mut at_once = vec![0u8; len];
            ours.apply_keystream(&nonce, 1, &mut at_once).unwrap();
            assert_eq!(at_once, theirs[..len], "{len} bytes");
            for split in (64..len).step_by(64) {
                let mut split_out = vec![0u8; len];
                let (first, second) = split_out.split_at_mut(split);
                ours.apply_keystream(&nonce, 1, first).unwrap();
                ours.apply_keystream(&nonce, 1 + split as u32 / 64, second)
                    .unwrap();
                assert_eq!(split_out, theirs[..len], "{len} bytes, split at {split}");
            }
        }
    }
}

mod key_wrap {
    use aes_kw::KeyInit;
    use proptest::prelude::*;
    use rind::Error;
    use rind::key_wrap::{self as ours, Mode};

    fn kek() -> impl Strategy<Value = Vec<u8>> {
        prop::sample::select(&[16, 24, 32][..])
            .prop_flat_map(|len| prop::collection::vec(any::<u8>(), len))
    }

    /// aws-lc's RFC 3394 and RFC 5649 key wrap, through aws-lc-sys, since
    /// aws-lc-rs offers no AES-192 KEK.
    struct Theirs(aws_lc_sys::AES_KEY, aws_lc_sys::AES_KEY);

    fn theirs(kek: &[u8]) -> Theirs {
        let bits = 8 * kek.len() as u32;
        // SAFETY: `kek` is `bits / 8` readable bytes, and each key a
        // writable `AES_KEY`.
        unsafe {
            let mut keys: Theirs = core::mem::zeroed();
            assert_eq!(
                aws_lc_sys::AES_set_encrypt_key(kek.as_ptr(), bits, &mut keys.0),
                0
            );
            assert_eq!(
                aws_lc_sys::AES_set_decrypt_key(kek.as_ptr(), bits, &mut keys.1),
                0
            );
            keys
        }
    }

    impl Theirs {
        fn wrap(&self, key: &[u8], out: &mut [u8]) -> Result<(), ()> {
            assert_eq!(out.len(), key.len() + 8);
            // SAFETY: `out` is 8 bytes longer than `key`, as the routine
            // writes, and a null IV is RFC 3394's default.
            let n = unsafe {
                aws_lc_sys::AES_wrap_key(
                    &self.0,
                    core::ptr::null(),
                    out.as_mut_ptr(),
                    key.as_ptr(),
                    key.len(),
                )
            };
            if n == out.len() as i32 {
                Ok(())
            } else {
                Err(())
            }
        }

        fn unwrap(&self, wrapped: &[u8], out: &mut [u8]) -> Result<(), ()> {
            assert_eq!(out.len() + 8, wrapped.len());
            // SAFETY: `out` is 8 bytes shorter than `wrapped`, as the routine
            // writes, and a null IV is RFC 3394's default.
            let n = unsafe {
                aws_lc_sys::AES_unwrap_key(
                    &self.1,
                    core::ptr::null(),
                    out.as_mut_ptr(),
                    wrapped.as_ptr(),
                    wrapped.len(),
                )
            };
            if n == out.len() as i32 {
                Ok(())
            } else {
                Err(())
            }
        }

        /// RFC 5649's padded wrap of `key` into `out`, returning the part
        /// written.
        fn wrap_with_padding<'a>(&self, key: &[u8], out: &'a mut [u8]) -> Result<&'a mut [u8], ()> {
            let mut n = 0;
            // SAFETY: `out` is `out.len()` writable bytes, the most the
            // routine writes.
            let ok = unsafe {
                aws_lc_sys::AES_wrap_key_padded(
                    &self.0,
                    out.as_mut_ptr(),
                    &mut n,
                    out.len(),
                    key.as_ptr(),
                    key.len(),
                )
            };
            if ok == 1 { Ok(&mut out[..n]) } else { Err(()) }
        }

        /// RFC 5649's padded unwrap of `wrapped` into `out`, returning the
        /// key.
        fn unwrap_with_padding<'a>(
            &self,
            wrapped: &[u8],
            out: &'a mut [u8],
        ) -> Result<&'a mut [u8], ()> {
            let mut n = 0;
            // SAFETY: as in `wrap_with_padding`.
            let ok = unsafe {
                aws_lc_sys::AES_unwrap_key_padded(
                    &self.1,
                    out.as_mut_ptr(),
                    &mut n,
                    out.len(),
                    wrapped.as_ptr(),
                    wrapped.len(),
                )
            };
            if ok == 1 { Ok(&mut out[..n]) } else { Err(()) }
        }
    }

    proptest! {
        #[test]
        fn wrap_and_unwrap(
            kek in kek(),
            key in (2..=12usize).prop_flat_map(|n| prop::collection::vec(any::<u8>(), 8 * n)),
            flip in any::<prop::sample::Index>(),
        ) {
            let algorithm = match kek.len() {
                16 => &ours::AES_128,
                24 => &ours::AES_192,
                _ => &ours::AES_256,
            };
            let ours = ours::AesKek::new(algorithm, &kek).unwrap();

            let mut wrapped = vec![0u8; key.len() + 8];
            ours.wrap_key(Mode::Kw, &key, &mut wrapped).unwrap();
            let mut wanted = vec![0u8; key.len() + 8];
            theirs(&kek).wrap(&key, &mut wanted).unwrap();
            prop_assert_eq!(&wrapped, &wanted);
            let mut independent = vec![0u8; key.len() + 8];
            rustcrypto_aes!(kek, Aes => aes_kw::AesKw::<Aes>::new_from_slice(&kek)
                .unwrap()
                .wrap_key(&key, &mut independent)
                .unwrap());
            prop_assert_eq!(&wrapped, &independent);

            let mut unwrapped = vec![0u8; key.len()];
            ours.unwrap_key(Mode::Kw, &wrapped, &mut unwrapped).unwrap();
            prop_assert_eq!(&unwrapped, &key);

            // both refuse any single bit flipped
            let bit = flip.index(wrapped.len() * 8);
            wrapped[bit / 8] ^= 1 << (bit % 8);
            prop_assert_eq!(ours.unwrap_key(Mode::Kw, &wrapped, &mut unwrapped).map(|_| ()), Err(Error::DecryptFailed));
            prop_assert!(theirs(&kek).unwrap(&wrapped, &mut vec![0u8; key.len()]).is_err());
            prop_assert!(rustcrypto_aes!(kek, Aes => aes_kw::AesKw::<Aes>::new_from_slice(&kek)
                .unwrap()
                .unwrap_key(&wrapped, &mut vec![0u8; key.len()])
                .is_err()));
        }

        #[test]
        fn wrap_and_unwrap_padded(
            kek in kek(),
            key in prop::collection::vec(any::<u8>(), 1..100),
            flip in any::<prop::sample::Index>(),
        ) {
            let algorithm = match kek.len() {
                16 => &ours::AES_128,
                24 => &ours::AES_192,
                _ => &ours::AES_256,
            };
            let ours = ours::AesKek::new(algorithm, &kek).unwrap();

            let mut wrapped = vec![0u8; key.len().next_multiple_of(8) + 8];
            ours.wrap_key(Mode::Kwp, &key, &mut wrapped).unwrap();
            let mut wanted = vec![0u8; key.len() + 15];
            let wanted = theirs(&kek).wrap_with_padding(&key, &mut wanted).unwrap();
            prop_assert_eq!(&wrapped[..], &wanted[..]);
            let mut independent = vec![0u8; wrapped.len()];
            rustcrypto_aes!(kek, Aes => aes_kw::AesKwp::<Aes>::new_from_slice(&kek)
                .unwrap()
                .wrap_key(&key, &mut independent)
                .unwrap());
            prop_assert_eq!(&wrapped, &independent);

            let mut unwrapped = vec![0u8; wrapped.len() - 8];
            prop_assert_eq!(&ours.unwrap_key(Mode::Kwp, &wrapped, &mut unwrapped).unwrap()[..], &key[..]);

            // both refuse any single bit flipped
            let bit = flip.index(wrapped.len() * 8);
            wrapped[bit / 8] ^= 1 << (bit % 8);
            prop_assert_eq!(ours.unwrap_key(Mode::Kwp, &wrapped, &mut unwrapped).map(|_| ()), Err(Error::DecryptFailed));
            prop_assert!(theirs(&kek).unwrap_with_padding(&wrapped, &mut vec![0u8; wrapped.len()]).is_err());
            prop_assert!(rustcrypto_aes!(kek, Aes => aes_kw::AesKwp::<Aes>::new_from_slice(&kek)
                .unwrap()
                .unwrap_key(&wrapped, &mut vec![0u8; wrapped.len()])
                .is_err()));
        }
    }
}

mod hkdf {
    use aws_lc_rs::{aead as their_aead, hkdf as theirs, hmac as their_hmac};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::{Error, aead, hkdf, hmac};

    struct Len(usize);

    impl theirs::KeyType for Len {
        fn len(&self) -> usize {
            self.0
        }
    }

    /// RustCrypto's HKDF: `len` bytes expanded from the PRK extracted from
    /// `ikm` under `salt`, or without `ikm` from `salt` taken as the PRK,
    /// which RustCrypto refuses, as `None`, when shorter than the hash.
    type Independent =
        fn(&[u8], Option<&[u8]>, &[&[u8]], usize) -> Option<Result<Vec<u8>, ::hkdf::InvalidLength>>;

    fn rustcrypto<D: ::hmac::EagerHash>(
        salt: &[u8],
        ikm: Option<&[u8]>,
        info: &[&[u8]],
        len: usize,
    ) -> Option<Result<Vec<u8>, ::hkdf::InvalidLength>>
    where
        ::hmac::Hmac<D>: ::hkdf::HmacImpl,
    {
        let hkdf = match ikm {
            Some(ikm) => ::hkdf::Hkdf::<D>::new(Some(salt), ikm),
            None => ::hkdf::Hkdf::<D>::from_prk(salt).ok()?,
        };
        let mut okm = vec![0u8; len];
        Some(hkdf.expand_multi_info(info, &mut okm).map(|()| okm))
    }

    fn algorithms() -> [(
        &'static hkdf::Algorithm,
        theirs::Algorithm,
        Independent,
        usize,
    ); 4] {
        [
            (
                &hkdf::legacy::HKDF_SHA1,
                theirs::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
                rustcrypto::<sha1::Sha1>,
                20,
            ),
            (
                &hkdf::HKDF_SHA256,
                theirs::HKDF_SHA256,
                rustcrypto::<sha2::Sha256>,
                32,
            ),
            (
                &hkdf::HKDF_SHA384,
                theirs::HKDF_SHA384,
                rustcrypto::<sha2::Sha384>,
                48,
            ),
            (
                &hkdf::HKDF_SHA512,
                theirs::HKDF_SHA512,
                rustcrypto::<sha2::Sha512>,
                64,
            ),
        ]
    }

    // Salts either side of both block sizes (64 and 128), info split into
    // parts, and lengths up to a few blocks or either side of each hash's
    // 255-block limit.
    proptest! {
        #[test]
        fn matches(
            algorithm in 0..4usize,
            salt in vec(any::<u8>(), 0..200),
            ikm in vec(any::<u8>(), 0..200),
            info in vec(vec(any::<u8>(), 0..100), 0..4),
            len in 0..200usize,
            at_limit in any::<bool>(),
        ) {
            let (ours, their_alg, independent, hash_len) = algorithms()[algorithm];
            let len = match at_limit {
                true => 255 * hash_len + len - 100,
                false => len,
            };
            let info: Vec<&[u8]> = info.iter().map(Vec::as_slice).collect();

            // An extracted PRK, then the salt taken as a PRK as it is, up to
            // the 64 bytes aws-lc-rs's `new_less_safe` holds before it panics.
            // RustCrypto expands the PRK its extract returns, and the salt
            // as a PRK when it is at least the hash's length.
            let prk = &salt[..salt.len().min(64)];
            let pairs = [
                (
                    hkdf::Salt::new(ours, &salt).extract(&ikm).unwrap(),
                    theirs::Salt::new(their_alg, &salt).extract(&ikm),
                    independent(&salt, Some(&ikm), &info, len),
                ),
                (
                    hkdf::Prk::new(ours, prk),
                    theirs::Prk::new_less_safe(their_alg, prk),
                    independent(prk, None, &info, len),
                ),
            ];
            for (ours, theirs, independent) in pairs {
                let mut ours_out = vec![0u8; len];
                let result = ours.fill(&info, &mut ours_out);
                match theirs.expand(&info, Len(len)) {
                    Ok(okm) => {
                        result.unwrap();
                        let mut theirs_out = vec![0u8; len];
                        okm.fill(&mut theirs_out).unwrap();
                        prop_assert_eq!(&ours_out, &theirs_out);
                        if let Some(independent) = independent {
                            prop_assert_eq!(&ours_out, &independent.unwrap());
                        }
                    }
                    Err(_) => {
                        prop_assert_eq!(result, Err(Error::WrongLength));
                        prop_assert!(ours_out.iter().all(|b| *b == 0));
                        if let Some(independent) = independent {
                            prop_assert!(independent.is_err());
                        }
                    }
                }
            }
        }

        // Keys built straight from an `Okm` match aws-lc-rs's conversions,
        // including keys longer than the PRK's hash output.
        #[test]
        fn keys(
            algorithm in 0..4usize,
            ikm in vec(any::<u8>(), 0..100),
            info in vec(vec(any::<u8>(), 0..50), 0..3),
            msg in vec(any::<u8>(), 0..100),
        ) {
            let (ours_prk_alg, theirs_prk_alg, _, _) = algorithms()[algorithm];
            let info: Vec<&[u8]> = info.iter().map(Vec::as_slice).collect();
            let ours = hkdf::Salt::new(ours_prk_alg, b"salt").extract(&ikm).unwrap();
            let theirs = theirs::Salt::new(theirs_prk_alg, b"salt").extract(&ikm);

            for (ours_alg, theirs_alg) in [
                (&aead::AES_128_GCM, &their_aead::AES_128_GCM),
                (&aead::AES_256_GCM, &their_aead::AES_256_GCM),
                (&aead::CHACHA20_POLY1305, &their_aead::CHACHA20_POLY1305),
            ] {
                let ours_key = aead::Key::from(ours.expand(&info, ours_alg).unwrap());
                let mut ours_sealed = msg.clone();
                ours_key
                    .seal_in_place_append_tag(
                        aead::Nonce::assume_unique_for_key([0; 12]),
                        &[],
                        &mut ours_sealed,
                    )
                    .unwrap();

                let theirs_key = their_aead::LessSafeKey::new(their_aead::UnboundKey::from(
                    theirs.expand(&info, theirs_alg).unwrap(),
                ));
                let mut theirs_sealed = msg.clone();
                theirs_key
                    .seal_in_place_append_tag(
                        their_aead::Nonce::assume_unique_for_key([0; 12]),
                        their_aead::Aad::empty(),
                        &mut theirs_sealed,
                    )
                    .unwrap();
                prop_assert_eq!(ours_sealed, theirs_sealed);
            }

            for (ours_alg, theirs_alg) in [
                (&hmac::legacy::HMAC_SHA1, their_hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY),
                (&hmac::HMAC_SHA256, their_hmac::HMAC_SHA256),
                (&hmac::HMAC_SHA384, their_hmac::HMAC_SHA384),
                (&hmac::HMAC_SHA512, their_hmac::HMAC_SHA512),
            ] {
                let ours_key = hmac::Key::from(ours.expand(&info, ours_alg).unwrap());
                let theirs_key = their_hmac::Key::from(theirs.expand(&info, theirs_alg).unwrap());
                let ours_tag = hmac::sign(&ours_key, &msg);
                let theirs_tag = their_hmac::sign(&theirs_key, &msg);
                prop_assert_eq!(ours_tag.as_ref(), theirs_tag.as_ref());
            }

            let ours = hkdf::Prk::from(ours.expand(&info, ours_prk_alg).unwrap());
            let theirs = theirs::Prk::from(theirs.expand(&info, theirs_prk_alg).unwrap());
            let mut ours_out = [0u8; 100];
            ours.fill(&info, &mut ours_out).unwrap();
            let mut theirs_out = [0u8; 100];
            theirs.expand(&info, Len(theirs_out.len())).unwrap().fill(&mut theirs_out).unwrap();
            prop_assert_eq!(ours_out, theirs_out);
        }
    }
}

mod pbkdf2 {
    use core::num::NonZeroU32;

    use ::pbkdf2::pbkdf2_hmac;
    use aws_lc_rs::pbkdf2 as theirs;
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::{Error, pbkdf2};
    use sha1::Sha1;
    use sha2::{Sha256, Sha384, Sha512};

    /// RustCrypto's PBKDF2: password, salt, iterations, and output.
    type Independent = fn(&[u8], &[u8], u32, &mut [u8]);

    // Passwords either side of both block sizes (64 and 128), and keys of
    // several blocks with a partial last one.
    proptest! {
        #[test]
        fn matches(
            password in vec(any::<u8>(), 0..300),
            salt in vec(any::<u8>(), 0..200),
            iterations in 1..20u32,
            len in 1..200usize,
        ) {
            let iterations = NonZeroU32::new(iterations).unwrap();
            for (ours, theirs, independent, hash_len) in [
                (&pbkdf2::legacy::PBKDF2_HMAC_SHA1, theirs::PBKDF2_HMAC_SHA1, pbkdf2_hmac::<Sha1> as Independent, 20),
                (&pbkdf2::PBKDF2_HMAC_SHA256, theirs::PBKDF2_HMAC_SHA256, pbkdf2_hmac::<Sha256>, 32),
                (&pbkdf2::PBKDF2_HMAC_SHA384, theirs::PBKDF2_HMAC_SHA384, pbkdf2_hmac::<Sha384>, 48),
                (&pbkdf2::PBKDF2_HMAC_SHA512, theirs::PBKDF2_HMAC_SHA512, pbkdf2_hmac::<Sha512>, 64),
            ] {
                let mut wanted = vec![0u8; len];
                theirs::derive(theirs, iterations, &salt, &password, &mut wanted);
                let mut independent_out = vec![0u8; len];
                independent(&password, &salt, iterations.get(), &mut independent_out);
                prop_assert_eq!(&independent_out, &wanted);

                let secret = pbkdf2::Secret::new(ours, &password);
                let mut got = vec![0u8; len];
                secret.derive(iterations, &salt, &mut got).unwrap();
                prop_assert_eq!(&got, &wanted);
                // Unlike aws-lc-rs, rind refuses to verify a key shorter than the HMAC output.
                let verified = match len < hash_len {
                    true => Err(Error::WrongLength),
                    false => Ok(()),
                };
                prop_assert_eq!(secret.verify(iterations, &salt, &wanted), verified);
            }
        }
    }
}

mod aead {
    use aes::cipher::{BlockCipherEncrypt, KeyIvInit, StreamCipher};
    use aes_gcm::aead::consts::U12;
    use aes_gcm::aead::{AeadInOut, KeyInit};
    use aws_lc_rs::aead as theirs;
    use chacha20poly1305::{ChaCha20Poly1305, XChaCha20Poly1305};
    use ghash::GHash;
    use ghash::universal_hash::UniversalHash;
    use proptest::collection::vec;
    use proptest::prelude::*;
    use proptest::sample::Index;
    use rind::Error;
    use rind::aead::{
        AES_128_GCM, AES_192_GCM, AES_256_GCM, Algorithm, CHACHA20_POLY1305, Key, Nonce,
        RandomizedNonceKey, gcm,
    };
    use rind::cipher::{AES_128, AES_192, AES_256};

    const TAG_LENGTHS: [gcm::TagLength; 7] = [
        gcm::TagLength::Full,
        gcm::TagLength::Truncated120,
        gcm::TagLength::Truncated112,
        gcm::TagLength::Truncated104,
        gcm::TagLength::Truncated96,
        gcm::TagLength::Truncated64,
        gcm::TagLength::Truncated32,
    ];

    /// RustCrypto's seal of a message: its ciphertext, then its tag.
    type Independent = fn(&[u8], &[u8], &[u8], &[u8]) -> Vec<u8>;

    fn seal<A: AeadInOut + KeyInit>(key: &[u8], nonce: &[u8], aad: &[u8], msg: &[u8]) -> Vec<u8> {
        let mut sealed = msg.to_vec();
        let tag = A::new_from_slice(key)
            .unwrap()
            .encrypt_inout_detached(nonce.try_into().unwrap(), aad, sealed.as_mut_slice().into())
            .unwrap();
        sealed.extend_from_slice(&tag);
        sealed
    }

    fn rustcrypto_aes_gcm(key: &[u8], nonce: &[u8], aad: &[u8], msg: &[u8]) -> Vec<u8> {
        rustcrypto_aes!(key, Aes => seal::<aes_gcm::AesGcm<Aes, U12>>(key, nonce, aad, msg))
    }

    /// AES-GCM under an IV and tag of any length, built from RustCrypto's
    /// AES, GHASH, and CTR as NIST SP 800-38D section 7.1 builds it, since
    /// RustCrypto's AES-GCM fixes both lengths in its type and takes no tag
    /// shorter than 12 bytes.
    fn rustcrypto_aes_gcm_any_iv(
        key: &[u8],
        iv: &[u8],
        tag_len: usize,
        aad: &[u8],
        msg: &[u8],
    ) -> Vec<u8> {
        fn ghash(h: &aes::Block, parts: [&[u8]; 2]) -> [u8; 16] {
            let mut ghash = GHash::new(h);
            for part in parts {
                ghash.update_padded(part);
            }
            let mut lengths = [0u8; 16];
            lengths[..8].copy_from_slice(&(8 * parts[0].len() as u64).to_be_bytes());
            lengths[8..].copy_from_slice(&(8 * parts[1].len() as u64).to_be_bytes());
            ghash.update(&[lengths.into()]);
            ghash.finalize().into()
        }

        rustcrypto_aes!(key, Aes => {
            let aes = Aes::new_from_slice(key).unwrap();
            let mut h = aes::Block::default();
            aes.encrypt_block(&mut h);
            let j0 = match iv.len() {
                12 => {
                    let mut j0 = [0u8; 16];
                    j0[..12].copy_from_slice(iv);
                    j0[15] = 1;
                    j0
                }
                _ => ghash(&h, [&[], iv]),
            };
            let mut counter = j0;
            let low = u32::from_be_bytes(j0[12..].try_into().unwrap()).wrapping_add(1);
            counter[12..].copy_from_slice(&low.to_be_bytes());
            let mut sealed = msg.to_vec();
            ctr::Ctr32BE::<Aes>::new_from_slices(key, &counter)
                .unwrap()
                .apply_keystream(&mut sealed);
            let mut tag = j0.into();
            aes.encrypt_block(&mut tag);
            let s = ghash(&h, [aad, &sealed]);
            sealed.extend(tag.iter().zip(s).map(|(t, s)| t ^ s).take(tag_len));
            sealed
        })
    }

    /// Seals on all three sides and compares, then opens aws-lc-rs's output,
    /// first with one bit of its ciphertext or tag flipped if `flip` is set.
    #[allow(clippy::too_many_arguments)]
    fn check(
        ours: &'static Algorithm,
        theirs: &'static theirs::Algorithm,
        independent: Independent,
        key: &[u8],
        nonce: [u8; 12],
        aad: &[u8],
        msg: &[u8],
        flip: Option<Index>,
    ) -> Result<(), TestCaseError> {
        let ours = Key::new(ours, key).unwrap();
        let mut ours_sealed = msg.to_vec();
        ours.seal_in_place_append_tag(Nonce::assume_unique_for_key(nonce), aad, &mut ours_sealed)
            .unwrap();

        let mut theirs_sealed = msg.to_vec();
        theirs::LessSafeKey::new(theirs::UnboundKey::new(theirs, key).unwrap())
            .seal_in_place_append_tag(
                theirs::Nonce::assume_unique_for_key(nonce),
                theirs::Aad::from(aad),
                &mut theirs_sealed,
            )
            .unwrap();
        prop_assert_eq!(&ours_sealed, &theirs_sealed);
        prop_assert_eq!(&ours_sealed, &independent(key, &nonce, aad, msg));

        if let Some(flip) = flip {
            let index = flip.index(theirs_sealed.len());
            theirs_sealed[index] ^= 1;
        }
        let result = ours
            .open_in_place(Nonce::assume_unique_for_key(nonce), aad, &mut theirs_sealed)
            .map(|plain| plain.to_vec());
        if flip.is_some() {
            prop_assert_eq!(result, Err(Error::DecryptFailed));
        } else {
            prop_assert_eq!(result, Ok(msg.to_vec()));
        }
        Ok(())
    }

    // Every message and AAD length to 32 blocks, each with every partial
    // tail, so each path through the aarch64 kernels runs, the eight-way
    // loop's repeat included, and so does every tail after x86_64's 128- and
    // 256-byte chunks. Then every message length across x86_64's switch to
    // BoringSSL's 512-bit kernel at 2048 bytes, through every tail after its
    // first chunk past it. They work in place, which a block stored before it
    // is loaded would break.
    #[test]
    fn aes_gcm_every_length() {
        let msg: Vec<u8> = (0..2048 + 256 + 15).map(|i| (i * 7 + 3) as u8).collect();
        let rc: Independent = rustcrypto_aes_gcm;
        for (ours, theirs, key) in [
            (&AES_128_GCM, &theirs::AES_128_GCM, &[1u8; 16][..]),
            (&AES_192_GCM, &theirs::AES_192_GCM, &[4u8; 24][..]),
            (&AES_256_GCM, &theirs::AES_256_GCM, &[2u8; 32][..]),
        ] {
            for len in 0..=32 * 16 + 15 {
                check(ours, theirs, rc, key, [3; 12], b"aad", &msg[..len], None).unwrap();
                check(ours, theirs, rc, key, [3; 12], &msg[..len], b"msg", None).unwrap();
            }
            for len in 2048 - 16..=msg.len() {
                check(ours, theirs, rc, key, [3; 12], b"aad", &msg[..len], None).unwrap();
            }
        }
    }

    // Messages and AAD span several blocks with ragged tails.
    proptest! {
        #[test]
        fn aes_gcm(
            key in prop_oneof![vec(any::<u8>(), 16), vec(any::<u8>(), 24), vec(any::<u8>(), 32)],
            nonce in any::<[u8; 12]>(),
            aad in vec(any::<u8>(), 0..100),
            msg in vec(any::<u8>(), 0..1100),
            flip in any::<Option<Index>>(),
        ) {
            let (ours, theirs) = match key.len() {
                16 => (&AES_128_GCM, &theirs::AES_128_GCM),
                24 => (&AES_192_GCM, &theirs::AES_192_GCM),
                _ => (&AES_256_GCM, &theirs::AES_256_GCM),
            };
            check(ours, theirs, rustcrypto_aes_gcm, &key, nonce, &aad, &msg, flip)?;
        }

        // Long messages too, which x86_64 CPUs with AVX-512 IFMA take in
        // separate passes, across their 16 KB chunks.
        #[test]
        fn chacha20_poly1305(
            key in any::<[u8; 32]>(),
            nonce in any::<[u8; 12]>(),
            aad in vec(any::<u8>(), 0..100),
            msg in prop_oneof![vec(any::<u8>(), 0..1100), vec(any::<u8>(), 1100..40000)],
            flip in any::<Option<Index>>(),
        ) {
            check(
                &CHACHA20_POLY1305,
                &theirs::CHACHA20_POLY1305,
                seal::<ChaCha20Poly1305>,
                &key,
                nonce,
                &aad,
                &msg,
                flip,
            )?;
        }

        // aws-lc-rs takes only 96-bit nonces and full tags, so this seals
        // with aws-lc's AES-GCM under an IV of any length and each tag
        // length, then opens that, as `check` does.
        #[test]
        fn aes_gcm_any_iv(
            key in prop_oneof![vec(any::<u8>(), 16), vec(any::<u8>(), 24), vec(any::<u8>(), 32)],
            iv in prop_oneof![vec(any::<u8>(), 12), vec(any::<u8>(), 1..80)],
            tag_len in proptest::sample::select(&TAG_LENGTHS[..]),
            aad in vec(any::<u8>(), 0..100),
            msg in vec(any::<u8>(), 0..1100),
            flip in any::<Option<Index>>(),
        ) {
            let aes = match key.len() {
                16 => &AES_128,
                24 => &AES_192,
                _ => &AES_256,
            };
            let ours = gcm::Key::new(aes, &key, tag_len).unwrap();
            let mut ours_sealed = msg.clone();
            ours.seal_in_place_append_tag(gcm::Iv::assume_unique_for_key(&iv).unwrap(), &aad, &mut ours_sealed).unwrap();

            let mut theirs_sealed = msg.clone();
            theirs_sealed.extend([0; 16]);
            let (out, tag) = theirs_sealed.split_at_mut(msg.len());
            let tag = &mut tag[..ours.tag_len()];
            let mut written = 0;
            // SAFETY: each pointer and length describes a live buffer, and
            // the context is freed once, after its last use.
            let sealed = unsafe {
                let aead = match key.len() {
                    16 => aws_lc_sys::EVP_aead_aes_128_gcm(),
                    24 => aws_lc_sys::EVP_aead_aes_192_gcm(),
                    _ => aws_lc_sys::EVP_aead_aes_256_gcm(),
                };
                let ctx = aws_lc_sys::EVP_AEAD_CTX_new(aead, key.as_ptr(), key.len(), tag.len());
                assert!(!ctx.is_null());
                let sealed = aws_lc_sys::EVP_AEAD_CTX_seal_scatter(
                    ctx,
                    out.as_mut_ptr(),
                    tag.as_mut_ptr(),
                    &mut written,
                    tag.len(),
                    iv.as_ptr(),
                    iv.len(),
                    msg.as_ptr(),
                    msg.len(),
                    core::ptr::null(),
                    0,
                    aad.as_ptr(),
                    aad.len(),
                );
                aws_lc_sys::EVP_AEAD_CTX_free(ctx);
                sealed
            };
            prop_assert_eq!((sealed, written), (1, ours.tag_len()));
            theirs_sealed.truncate(msg.len() + ours.tag_len());
            prop_assert_eq!(&ours_sealed, &theirs_sealed);
            prop_assert_eq!(&ours_sealed, &rustcrypto_aes_gcm_any_iv(&key, &iv, ours.tag_len(), &aad, &msg));

            if let Some(flip) = flip {
                let index = flip.index(theirs_sealed.len());
                theirs_sealed[index] ^= 1;
            }
            let result = ours
                .open_in_place(gcm::Iv::assume_unique_for_key(&iv).unwrap(), &aad, &mut theirs_sealed)
                .map(|plain| plain.to_vec());
            if flip.is_some() {
                prop_assert_eq!(result, Err(Error::DecryptFailed));
            } else {
                prop_assert_eq!(result, Ok(msg));
            }
        }

        // aws-lc-rs has no XChaCha20-Poly1305, so this seals with aws-lc's
        // under the nonce rind picked, and opens that, as `check` does.
        #[test]
        fn xchacha20_poly1305(
            key in prop_oneof![Just([0; 32]), Just([0xff; 32]), any::<[u8; 32]>()],
            aad in vec(any::<u8>(), 0..100),
            msg in vec(any::<u8>(), 0..1100),
            flip in any::<Option<Index>>(),
        ) {
            let ours = RandomizedNonceKey::new(&key);
            let mut ours_sealed = msg.clone();
            let nonce = ours.seal_in_place_append_tag(&aad, &mut ours_sealed).unwrap();

            let mut theirs_sealed = msg.clone();
            theirs_sealed.extend([0; 16]);
            let (out, tag) = theirs_sealed.split_at_mut(msg.len());
            let mut tag_len = 0;
            // SAFETY: each pointer and length describes a live buffer, and
            // the context is freed once, after its last use.
            let sealed = unsafe {
                let ctx = aws_lc_sys::EVP_AEAD_CTX_new(
                    aws_lc_sys::EVP_aead_xchacha20_poly1305(),
                    key.as_ptr(),
                    key.len(),
                    tag.len(),
                );
                assert!(!ctx.is_null());
                let sealed = aws_lc_sys::EVP_AEAD_CTX_seal_scatter(
                    ctx,
                    out.as_mut_ptr(),
                    tag.as_mut_ptr(),
                    &mut tag_len,
                    tag.len(),
                    nonce.as_ref().as_ptr(),
                    nonce.as_ref().len(),
                    msg.as_ptr(),
                    msg.len(),
                    core::ptr::null(),
                    0,
                    aad.as_ptr(),
                    aad.len(),
                );
                aws_lc_sys::EVP_AEAD_CTX_free(ctx);
                sealed
            };
            prop_assert_eq!((sealed, tag_len), (1, 16));
            prop_assert_eq!(&ours_sealed, &theirs_sealed);
            prop_assert_eq!(&ours_sealed, &seal::<XChaCha20Poly1305>(&key, nonce.as_ref(), &aad, &msg));

            if let Some(flip) = flip {
                let index = flip.index(theirs_sealed.len());
                theirs_sealed[index] ^= 1;
            }
            let result = ours
                .open_in_place(nonce, &aad, &mut theirs_sealed)
                .map(|plain| plain.to_vec());
            if flip.is_some() {
                prop_assert_eq!(result, Err(Error::DecryptFailed));
            } else {
                prop_assert_eq!(result, Ok(msg));
            }
        }
    }
}
