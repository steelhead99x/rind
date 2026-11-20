//! Differential tests against aws-lc, which Miri cannot run.
#![cfg(not(any(miri, target_family = "wasm")))]

use aws_lc_rs::{digest, hmac, signature::Ed25519KeyPair};
use proptest::collection::vec;
use proptest::prelude::*;

#[test]
fn ed25519_key_generation() {
    for _ in 0..100 {
        let key = rind::ed25519::KeyPair::generate().unwrap();
        let key_enc = key.to_pkcs8();
        let key_enc = key_enc.as_ref();

        let aws = Ed25519KeyPair::from_pkcs8(key_enc)
            .expect("aws-lc-rs rejected an ed25519 key we generated");
        assert_eq!(
            aws.to_pkcs8().unwrap().as_ref(),
            key_enc,
            "aws-lc-rs varied our ed25519 key encoding"
        );
    }
}

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

/// Each hash rind offers, with aws-lc's and its block size.
fn hashes() -> [(&'static rind::digest::Algorithm, Theirs, usize); 9] {
    use Theirs::*;
    [
        (&rind::digest::legacy::MD5, Md5, 64),
        (
            &rind::digest::legacy::SHA1,
            AwsLcRs(&digest::SHA1_FOR_LEGACY_USE_ONLY),
            64,
        ),
        (&rind::digest::SHA256, AwsLcRs(&digest::SHA256), 64),
        (&rind::digest::SHA384, AwsLcRs(&digest::SHA384), 128),
        (&rind::digest::SHA512, AwsLcRs(&digest::SHA512), 128),
        (&rind::digest::SHA512_256, AwsLcRs(&digest::SHA512_256), 128),
        (&rind::digest::SHA3_256, AwsLcRs(&digest::SHA3_256), 136),
        (&rind::digest::SHA3_384, AwsLcRs(&digest::SHA3_384), 104),
        (&rind::digest::SHA3_512, AwsLcRs(&digest::SHA3_512), 72),
    ]
}

// Every length to three of SHA-2's larger blocks, so each tail lands on both
// sides of the length field for both block sizes, and SHA-3's padding lands
// in one byte, two, or a block of its own. One-shot, and in updates that end
// on each block boundary, which leave SHA-2 a whole block buffered.
#[test]
fn hashes_every_length() {
    let message: Vec<u8> = (0..3 * 128 + 1).map(|i| (i * 7 + 3) as u8).collect();
    for (ours, theirs, block) in hashes() {
        for len in 0..=message.len() {
            let message = &message[..len];
            let wanted = theirs.digest(message);
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

proptest! {
    #[test]
    fn hashes_match_aws_lc_rs(
        message in vec(any::<u8>(), 0..1024),
        splits in vec(any::<prop::sample::Index>(), 0..4),
    ) {
        // Updates split anywhere exercise the partial-block buffering: one
        // that fills a block exactly, or spans several, after a partial one.
        let mut splits: Vec<_> = splits.iter().map(|s| s.index(message.len() + 1)).collect();
        splits.sort();
        for (ours, theirs, _) in hashes() {
            let mut ctx = rind::digest::Context::new(ours);
            let mut start = 0;
            for &end in splits.iter().chain([&message.len()]) {
                ctx.update(&message[start..end]);
                start = end;
            }
            let got = ctx.finish();
            prop_assert_eq!(got.as_ref(), theirs.digest(&message));
        }
    }

    #[test]
    fn hmac_matches_aws_lc_rs(
        // Up to 300 bytes spans keys below, at, and above both block sizes (64 and 128).
        key in vec(any::<u8>(), 0..300),
        message in vec(any::<u8>(), 0..1024),
        split in any::<prop::sample::Index>(),
    ) {
        let split = split.index(message.len() + 1);
        for (ours, theirs) in [
            (&rind::hmac::legacy::HMAC_SHA1, hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY),
            (&rind::hmac::HMAC_SHA256, hmac::HMAC_SHA256),
            (&rind::hmac::HMAC_SHA384, hmac::HMAC_SHA384),
            (&rind::hmac::HMAC_SHA512, hmac::HMAC_SHA512),
        ] {
            let ours = rind::hmac::Key::new(ours, &key);
            let mut ctx = rind::hmac::Context::with_key(&ours);
            ctx.update(&message[..split]);
            ctx.update(&message[split..]);
            let wanted = hmac::sign(&hmac::Key::new(theirs, &key), &message);
            let got = ctx.sign();
            prop_assert_eq!(got.as_ref(), wanted.as_ref());
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

mod cipher {
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
            prop_assert_eq!(ours, theirs);
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
            match (ours, theirs) {
                (Ok(ours), Ok(theirs)) => prop_assert_eq!(ours, theirs),
                (Err(Error::DecryptFailed), Err(_)) => {}
                (ours, theirs) => prop_assert!(false, "rind {:?}, aws-lc-rs {:?}", ours, theirs),
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
            algorithm in 0..3usize,
            key in any::<[u8; 32]>(),
            sample in any::<[u8; 16]>(),
        ) {
            use rind::aead::quic as ours;
            let (algorithm, theirs) = [
                (&ours::AES_128, &quic::AES_128),
                (&ours::AES_256, &quic::AES_256),
                (&ours::CHACHA20, &quic::CHACHA20),
            ][algorithm];
            let key = &key[..algorithm.key_len()];

            let mask = ours::HeaderProtectionKey::new(algorithm, key).unwrap().mask(&sample);
            let wanted = quic::HeaderProtectionKey::new(theirs, key)
                .unwrap()
                .new_mask(&sample)
                .unwrap();
            prop_assert_eq!(mask, wanted);
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
            prop_assert_eq!(ours, theirs);
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

            let mut unwrapped = vec![0u8; key.len()];
            ours.unwrap_key(Mode::Kw, &wrapped, &mut unwrapped).unwrap();
            prop_assert_eq!(&unwrapped, &key);

            // both refuse any single bit flipped
            let bit = flip.index(wrapped.len() * 8);
            wrapped[bit / 8] ^= 1 << (bit % 8);
            prop_assert_eq!(ours.unwrap_key(Mode::Kw, &wrapped, &mut unwrapped).map(|_| ()), Err(Error::DecryptFailed));
            prop_assert!(theirs(&kek).unwrap(&wrapped, &mut vec![0u8; key.len()]).is_err());
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

            let mut unwrapped = vec![0u8; wrapped.len() - 8];
            prop_assert_eq!(&ours.unwrap_key(Mode::Kwp, &wrapped, &mut unwrapped).unwrap()[..], &key[..]);

            // both refuse any single bit flipped
            let bit = flip.index(wrapped.len() * 8);
            wrapped[bit / 8] ^= 1 << (bit % 8);
            prop_assert_eq!(ours.unwrap_key(Mode::Kwp, &wrapped, &mut unwrapped).map(|_| ()), Err(Error::DecryptFailed));
            prop_assert!(theirs(&kek).unwrap_with_padding(&wrapped, &mut vec![0u8; wrapped.len()]).is_err());
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

    fn algorithms() -> [(&'static hkdf::Algorithm, theirs::Algorithm, usize); 4] {
        [
            (
                &hkdf::legacy::HKDF_SHA1,
                theirs::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
                20,
            ),
            (&hkdf::HKDF_SHA256, theirs::HKDF_SHA256, 32),
            (&hkdf::HKDF_SHA384, theirs::HKDF_SHA384, 48),
            (&hkdf::HKDF_SHA512, theirs::HKDF_SHA512, 64),
        ]
    }

    // Salts either side of both block sizes (64 and 128), info split into
    // parts, and lengths up to a few blocks or either side of each hash's
    // 255-block limit.
    proptest! {
        #[test]
        fn matches_aws_lc_rs(
            algorithm in 0..4usize,
            salt in vec(any::<u8>(), 0..200),
            ikm in vec(any::<u8>(), 0..200),
            info in vec(vec(any::<u8>(), 0..100), 0..4),
            len in 0..200usize,
            at_limit in any::<bool>(),
        ) {
            let (ours, their_alg, hash_len) = algorithms()[algorithm];
            let len = match at_limit {
                true => 255 * hash_len + len - 100,
                false => len,
            };
            let info: Vec<&[u8]> = info.iter().map(Vec::as_slice).collect();

            // An extracted PRK, then the salt taken as a PRK as it is, up to
            // the 64 bytes aws-lc-rs's `new_less_safe` holds before it panics.
            let prk = &salt[..salt.len().min(64)];
            let pairs = [
                (
                    hkdf::Salt::new(ours, &salt).extract(&ikm).unwrap(),
                    theirs::Salt::new(their_alg, &salt).extract(&ikm),
                ),
                (
                    hkdf::Prk::new(ours, prk),
                    theirs::Prk::new_less_safe(their_alg, prk),
                ),
            ];
            for (ours, theirs) in pairs {
                let mut ours_out = vec![0u8; len];
                let result = ours.fill(&info, &mut ours_out);
                match theirs.expand(&info, Len(len)) {
                    Ok(okm) => {
                        result.unwrap();
                        let mut theirs_out = vec![0u8; len];
                        okm.fill(&mut theirs_out).unwrap();
                        prop_assert_eq!(ours_out, theirs_out);
                    }
                    Err(_) => {
                        prop_assert_eq!(result, Err(Error::WrongLength));
                        prop_assert!(ours_out.iter().all(|b| *b == 0));
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
            let (ours_prk_alg, theirs_prk_alg, _) = algorithms()[algorithm];
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

    use aws_lc_rs::pbkdf2 as theirs;
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::{Error, pbkdf2};

    // Passwords either side of both block sizes (64 and 128), and keys of
    // several blocks with a partial last one.
    proptest! {
        #[test]
        fn matches_aws_lc_rs(
            password in vec(any::<u8>(), 0..300),
            salt in vec(any::<u8>(), 0..200),
            iterations in 1..20u32,
            len in 1..200usize,
        ) {
            let iterations = NonZeroU32::new(iterations).unwrap();
            for (ours, theirs, hash_len) in [
                (&pbkdf2::legacy::PBKDF2_HMAC_SHA1, theirs::PBKDF2_HMAC_SHA1, 20),
                (&pbkdf2::PBKDF2_HMAC_SHA256, theirs::PBKDF2_HMAC_SHA256, 32),
                (&pbkdf2::PBKDF2_HMAC_SHA384, theirs::PBKDF2_HMAC_SHA384, 48),
                (&pbkdf2::PBKDF2_HMAC_SHA512, theirs::PBKDF2_HMAC_SHA512, 64),
            ] {
                let mut wanted = vec![0u8; len];
                theirs::derive(theirs, iterations, &salt, &password, &mut wanted);

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
    use aws_lc_rs::aead as theirs;
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

    /// Seals on both sides and compares, then opens aws-lc-rs's output,
    /// first with one bit of its ciphertext or tag flipped if `flip` is set.
    fn check(
        ours: &'static Algorithm,
        theirs: &'static theirs::Algorithm,
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
        for (ours, theirs, key) in [
            (&AES_128_GCM, &theirs::AES_128_GCM, &[1u8; 16][..]),
            (&AES_192_GCM, &theirs::AES_192_GCM, &[4u8; 24][..]),
            (&AES_256_GCM, &theirs::AES_256_GCM, &[2u8; 32][..]),
        ] {
            for len in 0..=32 * 16 + 15 {
                check(ours, theirs, key, [3; 12], b"aad", &msg[..len], None).unwrap();
                check(ours, theirs, key, [3; 12], &msg[..len], b"msg", None).unwrap();
            }
            for len in 2048 - 16..=msg.len() {
                check(ours, theirs, key, [3; 12], b"aad", &msg[..len], None).unwrap();
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
            check(ours, theirs, &key, nonce, &aad, &msg, flip)?;
        }

        #[test]
        fn chacha20_poly1305(
            key in any::<[u8; 32]>(),
            nonce in any::<[u8; 12]>(),
            aad in vec(any::<u8>(), 0..100),
            msg in vec(any::<u8>(), 0..1100),
            flip in any::<Option<Index>>(),
        ) {
            check(&CHACHA20_POLY1305, &theirs::CHACHA20_POLY1305, &key, nonce, &aad, &msg, flip)?;
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

/// ECDSA and ECDH on one curve: aws-lc-rs and rind accept each other's keys,
/// signatures, and public keys.
macro_rules! ec_crosschecks {
    ($curve:ident, $oid:literal, $ecdh:ident, $fixed_signing:ident, $fixed:ident, $asn1_signing:ident, $asn1:ident, $ours_fixed:ident, $ours_asn1:ident) => {
        mod $curve {
            use aws_lc_rs::agreement::{self, $ecdh, EphemeralPrivateKey};
            use aws_lc_rs::encoding::{
                AsBigEndian, AsDer, EcPrivateKeyBin, EcPrivateKeyRfc5915Der,
                EcPublicKeyCompressedBin, Pkcs8V1Der, PublicKeyX509Der,
            };
            use aws_lc_rs::rand::SystemRandom;
            use aws_lc_rs::signature::{
                $asn1, $asn1_signing, $fixed, $fixed_signing, EcdsaKeyPair, KeyPair,
                UnparsedPublicKey,
            };
            use proptest::collection::vec;
            use proptest::prelude::*;
            use rind::ecdsa::{self, sign, verify};

            // Each case generates keys on both sides, which is slow under emulation.
            proptest! {
                #![proptest_config(ProptestConfig::with_cases(32))]

                #[test]
                fn ecdsa(message in vec(any::<u8>(), 0..300)) {
                    // aws-lc-rs accepts our key and derives the same public
                    // key, encodings, and scalar.
                    let ours = ecdsa::KeyPair::generate(&sign::$ours_fixed).unwrap();
                    let encoded = ours.public_key();
                    let public = encoded.as_ref();
                    let theirs_from_ours = EcdsaKeyPair::from_pkcs8(
                        &$fixed_signing,
                        ours.to_pkcs8().as_ref(),
                    )
                    .expect("aws-lc-rs rejected a key we generated");
                    prop_assert_eq!(theirs_from_ours.public_key().as_ref(), public);
                    let spki = theirs_from_ours.public_key().as_der().unwrap();
                    let ours_spki = ours.public_key().to_spki();
                    prop_assert_eq!(spki.as_ref(), ours_spki.as_ref());
                    let scalar = theirs_from_ours.private_key().as_be_bytes().unwrap();
                    let ours_scalar = ours.to_scalar();
                    prop_assert_eq!(ours_scalar.as_ref(), scalar.as_ref());

                    // We load its scalar and point as the same key, and refuse
                    // the scalar with another key's point.
                    let reloaded = ecdsa::KeyPair::from_scalar_and_public_key(
                        &sign::$ours_asn1,
                        scalar.as_ref(),
                        public,
                    )
                    .unwrap();
                    let (reloaded_pkcs8, ours_pkcs8) = (reloaded.to_pkcs8(), ours.to_pkcs8());
                    prop_assert_eq!(reloaded_pkcs8.as_ref(), ours_pkcs8.as_ref());
                    let other = EcdsaKeyPair::generate(&$fixed_signing).unwrap();
                    prop_assert!(ecdsa::KeyPair::from_scalar_and_public_key(
                        &sign::$ours_asn1,
                        scalar.as_ref(),
                        other.public_key().as_ref(),
                    )
                    .is_err());

                    // It verifies our signatures, in both encodings.
                    let theirs_verifier = |alg| UnparsedPublicKey::new(alg, public);
                    let signature = ours.sign(&message).unwrap();
                    theirs_verifier(&$fixed).verify(&message, signature.as_ref()).unwrap();
                    let signature = reloaded.sign(&message).unwrap();
                    theirs_verifier(&$asn1).verify(&message, signature.as_ref()).unwrap();

                    // We verify its signatures, in both encodings, and refuse
                    // one over another message.
                    for (signing, ours_verification) in [
                        (&$fixed_signing, &verify::$ours_fixed),
                        (&$asn1_signing, &verify::$ours_asn1),
                    ] {
                        let theirs = EcdsaKeyPair::generate(signing).unwrap();
                        let signature = theirs.sign(&SystemRandom::new(), &message).unwrap();
                        let verifier =
                            ecdsa::PublicKey::new(ours_verification, theirs.public_key().as_ref())
                                .unwrap();
                        verifier.verify(&message, signature.as_ref()).unwrap();
                        prop_assert!(
                            verifier.verify(&[&message[..], b"!"].concat(), signature.as_ref()).is_err()
                        );
                    }
                }

                #[test]
                fn ecdh(_case in any::<u8>()) {
                    let ours = rind::agreement::PrivateKey::generate(&rind::agreement::$ecdh)
                        .unwrap();
                    let ours_public = ours.public_key();
                    let theirs = EphemeralPrivateKey::generate(&$ecdh, &SystemRandom::new()).unwrap();
                    let theirs_public = theirs.compute_public_key().unwrap();

                    let ours_secret = ours.agree(theirs_public.as_ref()).unwrap();
                    let theirs_secret = agreement::agree_ephemeral(
                        theirs,
                        agreement::UnparsedPublicKey::new(&$ecdh, ours_public.as_ref()),
                        (),
                        |secret| Ok(secret.to_vec()),
                    )
                    .unwrap();
                    prop_assert_eq!(ours_secret.as_ref(), &theirs_secret[..]);
                }

                /// Each side loads the other's stored key, in each encoding
                /// both write, as the same key, which agrees as the original
                /// does, again and again.
                #[test]
                fn ecdh_stored(_case in any::<u8>()) {
                    use rind::agreement::PrivateKey as Ours;

                    let theirs = agreement::PrivateKey::generate(&$ecdh).unwrap();
                    let theirs_public = theirs.compute_public_key().unwrap();
                    let peer = agreement::PrivateKey::generate(&$ecdh).unwrap();
                    let peer_public = peer.compute_public_key().unwrap();
                    let expected = agreement::agree(
                        &theirs,
                        agreement::UnparsedPublicKey::new(&$ecdh, peer_public.as_ref()),
                        (),
                        |secret| Ok(secret.to_vec()),
                    )
                    .unwrap();

                    let ecdh = &rind::agreement::$ecdh;
                    let scalar = AsBigEndian::<EcPrivateKeyBin<'_>>::as_be_bytes(&theirs).unwrap();
                    let pkcs8 = AsDer::<Pkcs8V1Der<'_>>::as_der(&theirs).unwrap();
                    let sec1 = AsDer::<EcPrivateKeyRfc5915Der<'_>>::as_der(&theirs).unwrap();
                    for ours in [
                        Ours::from_scalar(ecdh, scalar.as_ref()).unwrap(),
                        Ours::from_pkcs8(ecdh, pkcs8.as_ref()).unwrap(),
                        Ours::from_sec1(ecdh, sec1.as_ref()).unwrap(),
                    ] {
                        let ours_public = ours.public_key();
                        prop_assert_eq!(ours_public.as_ref(), theirs_public.as_ref());
                        for _ in 0..2 {
                            let secret = ours.agree(peer_public.as_ref()).unwrap();
                            prop_assert_eq!(secret.as_ref(), &expected[..]);
                        }

                        // Ours export as theirs do, and load back into theirs.
                        let (ours_scalar, ours_pkcs8) = (ours.to_scalar(), ours.to_pkcs8());
                        prop_assert_eq!(ours_scalar.as_ref(), scalar.as_ref());
                        prop_assert_eq!(ours_pkcs8.as_ref(), pkcs8.as_ref());
                        for theirs in [
                            agreement::PrivateKey::from_private_key(&$ecdh, ours_scalar.as_ref()),
                            agreement::PrivateKey::from_private_key_der(&$ecdh, ours_pkcs8.as_ref()),
                        ] {
                            let public = theirs.unwrap().compute_public_key().unwrap();
                            prop_assert_eq!(public.as_ref(), theirs_public.as_ref());
                        }

                        // An ECDSA key pair loads it as the same key.
                        let signing = ecdsa::KeyPair::from_pkcs8(&sign::$ours_asn1, ours_pkcs8.as_ref())
                            .unwrap();
                        let signing_public = signing.public_key();
                        prop_assert_eq!(signing_public.as_ref(), theirs_public.as_ref());
                    }
                }

                /// Each side's encodings of a key are the other's: SEC1 and
                /// SPKI, of key pairs, public keys, and agreement keys, and
                /// a compressed point, raw or in SPKI, which both
                /// decompress and agree with alike.
                #[test]
                fn encodings(_case in any::<u8>()) {
                    let theirs = EcdsaKeyPair::generate(&$asn1_signing).unwrap();
                    let pkcs8 = theirs.to_pkcs8v1().unwrap();
                    let ours = ecdsa::KeyPair::from_pkcs8(&sign::$ours_asn1, pkcs8.as_ref())
                        .unwrap();
                    let sec1 = theirs.private_key().as_der().unwrap();
                    let ours_sec1 = ours.to_sec1();
                    prop_assert_eq!(ours_sec1.as_ref(), sec1.as_ref());

                    let public = theirs.public_key();
                    let point = public.as_ref();
                    let spki = AsDer::<PublicKeyX509Der<'_>>::as_der(public).unwrap();
                    let parsed = ecdsa::PublicKey::from_spki(&verify::$ours_asn1, spki.as_ref())
                        .unwrap();
                    prop_assert_eq!(parsed.as_ref(), point);
                    let ours_spki = parsed.to_spki();
                    prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());

                    let ecdh = &rind::agreement::$ecdh;
                    let agreeing = agreement::PrivateKey::generate(&$ecdh).unwrap();
                    let agreeing_public = agreeing.compute_public_key().unwrap();
                    let agreeing_spki = agreeing_public.as_der().unwrap();
                    let parsed = rind::agreement::PublicKey::from_spki(ecdh, agreeing_spki.as_ref())
                        .unwrap();
                    prop_assert_eq!(parsed.as_ref(), agreeing_public.as_ref());
                    let ours_spki = parsed.to_spki();
                    prop_assert_eq!(ours_spki.as_ref(), agreeing_spki.as_ref());

                    let compressed =
                        AsBigEndian::<EcPublicKeyCompressedBin<'_>>::as_be_bytes(public).unwrap();
                    let compressed = compressed.as_ref();
                    let decompressed = rind::agreement::PublicKey::new(ecdh, compressed).unwrap();
                    prop_assert_eq!(decompressed.as_ref(), point);
                    let compressed_spki = crate::der(0x30, &[
                        &crate::der(0x30, &[
                            &crate::der(0x06, &hex::decode("2a8648ce3d0201").unwrap())[..],
                            &crate::der(0x06, &hex::decode($oid).unwrap()),
                        ].concat())[..],
                        &crate::der(0x03, &[&[0][..], compressed].concat()),
                    ].concat());
                    let parsed = ecdsa::PublicKey::from_spki(&verify::$ours_asn1, &compressed_spki)
                        .unwrap();
                    prop_assert_eq!(parsed.as_ref(), point);

                    let ours_agreeing = rind::agreement::PrivateKey::from_scalar(
                        ecdh,
                        AsBigEndian::<EcPrivateKeyBin<'_>>::as_be_bytes(&agreeing).unwrap().as_ref(),
                    )
                    .unwrap();
                    let ours_secret = ours_agreeing.agree(decompressed.as_ref()).unwrap();
                    let theirs_secret = agreement::agree(
                        &agreeing,
                        agreement::UnparsedPublicKey::new(&$ecdh, compressed),
                        (),
                        |secret| Ok(secret.to_vec()),
                    )
                    .unwrap();
                    prop_assert_eq!(ours_secret.as_ref(), &theirs_secret[..]);
                }

                /// A key pair's public key loads compressed, as aws-lc-rs
                /// takes it, but only with its own `y` parity. A hybrid point
                /// is refused, though aws-lc-rs takes it.
                #[test]
                fn public_key_forms(_case in any::<u8>()) {
                    let key = EcdsaKeyPair::generate(&$asn1_signing).unwrap();
                    let scalar = key.private_key().as_be_bytes().unwrap();
                    let scalar = scalar.as_ref();
                    let public = key.public_key();
                    let point = public.as_ref();
                    let (x, y) = point[1..].split_at(point.len() / 2);
                    let parity = y[y.len() - 1] & 1;

                    for (encoded, ours_takes, theirs_takes) in [
                        ([&[0x02 | parity][..], x].concat(), true, true),
                        ([&[0x03 ^ parity][..], x].concat(), false, false),
                        ([&[0x06 | parity][..], x, y].concat(), false, true),
                    ] {
                        let sec1 = crate::der(0x30, &[
                            &[0x02, 0x01, 0x01][..],
                            &crate::der(0x04, scalar),
                            &crate::der(0xa0, &crate::der(0x06, &hex::decode($oid).unwrap())),
                            &crate::der(0xa1, &crate::der(0x03, &[&[0][..], &encoded].concat())),
                        ].concat());
                        let pkcs8 = crate::der(0x30, &[
                            &[0x02, 0x01, 0x00][..],
                            &crate::der(0x30, &[
                                &crate::der(0x06, &hex::decode("2a8648ce3d0201").unwrap())[..],
                                &crate::der(0x06, &hex::decode($oid).unwrap()),
                            ].concat()),
                            &crate::der(0x04, &sec1),
                        ].concat());

                        let ours = [
                            ecdsa::KeyPair::from_scalar_and_public_key(
                                &sign::$ours_asn1, scalar, &encoded,
                            ),
                            ecdsa::KeyPair::from_sec1(&sign::$ours_asn1, &sec1),
                            ecdsa::KeyPair::from_pkcs8(&sign::$ours_asn1, &pkcs8),
                        ];
                        for ours in ours {
                            prop_assert_eq!(ours.is_ok(), ours_takes, "{:02x?}", encoded);
                            if let Ok(ours) = ours {
                                let ours = ours.public_key();
                                prop_assert_eq!(ours.as_ref(), point);
                            }
                        }
                        let ecdh = &rind::agreement::$ecdh;
                        for ours in [
                            rind::agreement::PrivateKey::from_sec1(ecdh, &sec1),
                            rind::agreement::PrivateKey::from_pkcs8(ecdh, &pkcs8),
                        ] {
                            prop_assert_eq!(ours.is_ok(), ours_takes, "{:02x?}", encoded);
                            if let Ok(ours) = ours {
                                let ours = ours.public_key();
                                prop_assert_eq!(ours.as_ref(), point);
                            }
                        }
                        let theirs = [
                            EcdsaKeyPair::from_private_key_and_public_key(
                                &$asn1_signing, scalar, &encoded,
                            ),
                            EcdsaKeyPair::from_private_key_der(&$asn1_signing, &sec1),
                            EcdsaKeyPair::from_pkcs8(&$asn1_signing, &pkcs8),
                        ];
                        for theirs in theirs {
                            prop_assert_eq!(theirs.is_ok(), theirs_takes, "{:02x?}", encoded);
                        }
                    }
                }
            }
        }
    };
}

/// A DER element of `tag` holding `body`.
fn der(tag: u8, body: &[u8]) -> Vec<u8> {
    let len = match body.len() {
        len @ 0..=0x7f => vec![len as u8],
        len @ 0x80..=0xff => vec![0x81, len as u8],
        len => [&[0x82][..], &u16::try_from(len).unwrap().to_be_bytes()].concat(),
    };
    [&[tag][..], &len, body].concat()
}

ec_crosschecks!(
    p256,
    "2a8648ce3d030107",
    ECDH_P256,
    ECDSA_P256_SHA256_FIXED_SIGNING,
    ECDSA_P256_SHA256_FIXED,
    ECDSA_P256_SHA256_ASN1_SIGNING,
    ECDSA_P256_SHA256_ASN1,
    P256_SHA256_FIXED,
    P256_SHA256_ASN1
);

ec_crosschecks!(
    p384,
    "2b81040022",
    ECDH_P384,
    ECDSA_P384_SHA384_FIXED_SIGNING,
    ECDSA_P384_SHA384_FIXED,
    ECDSA_P384_SHA384_ASN1_SIGNING,
    ECDSA_P384_SHA384_ASN1,
    P384_SHA384_FIXED,
    P384_SHA384_ASN1
);

ec_crosschecks!(
    p521,
    "2b81040023",
    ECDH_P521,
    ECDSA_P521_SHA512_FIXED_SIGNING,
    ECDSA_P521_SHA512_FIXED,
    ECDSA_P521_SHA512_ASN1_SIGNING,
    ECDSA_P521_SHA512_ASN1,
    P521_SHA512_FIXED,
    P521_SHA512_ASN1
);

mod ed25519 {
    use aws_lc_rs::encoding::{AsBigEndian, AsDer};
    use aws_lc_rs::signature::{ED25519, Ed25519KeyPair, KeyPair, UnparsedPublicKey};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use proptest::sample::Index;
    use rind::ed25519 as ours;

    proptest! {
        #[test]
        fn sign_verify(
            seed in any::<[u8; 32]>(),
            message in vec(any::<u8>(), 0..300),
            flip in any::<Option<Index>>(),
        ) {
            // Signing is deterministic, so one seed gives both sides the same
            // public key, encodings, seed, and signatures; loading ours checks
            // the public key matches theirs.
            let theirs = Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
            let public = theirs.public_key().as_ref();
            let ours = ours::KeyPair::from_seed_and_public_key(&seed, public).unwrap();
            let spki = theirs.public_key().as_der().unwrap();
            let ours_spki = ours.public_key().to_spki();
            prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());
            let (ours_pkcs8, theirs_pkcs8) = (ours.to_pkcs8(), theirs.to_pkcs8().unwrap());
            prop_assert_eq!(ours_pkcs8.as_ref(), theirs_pkcs8.as_ref());
            let ours_seed = ours.to_seed();
            let theirs_seed = theirs.seed().unwrap().as_be_bytes().unwrap();
            prop_assert_eq!(ours_seed.as_ref(), theirs_seed.as_ref());
            let signature = ours.sign(&message);
            let theirs_signature = theirs.sign(&message);
            prop_assert_eq!(signature.as_ref(), theirs_signature.as_ref());

            // Both verify it, and refuse it with any one bit flipped.
            let mut signature = signature.as_ref().to_vec();
            if let Some(flip) = flip {
                let bit = flip.index(signature.len() * 8);
                signature[bit / 8] ^= 1 << (bit % 8);
            }
            let ours_result = ours::PublicKey::new(public)
                .unwrap()
                .verify(&message, &signature);
            let theirs_result = UnparsedPublicKey::new(&ED25519, public).verify(&message, &signature);
            prop_assert_eq!(ours_result.is_ok(), flip.is_none());
            prop_assert_eq!(theirs_result.is_ok(), flip.is_none());
        }

        /// Both load a seed alone, and encode it as the same PKCS#8 v1, and
        /// the public key as the same SPKI, which each parses.
        #[test]
        fn seed_alone(seed in any::<[u8; 32]>()) {
            let theirs = Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
            let ours = ours::KeyPair::from_seed(&seed).unwrap();
            let public = ours.public_key();
            prop_assert_eq!(public.as_ref(), theirs.public_key().as_ref());
            let (ours_v1, theirs_v1) = (ours.to_pkcs8v1(), theirs.to_pkcs8v1().unwrap());
            prop_assert_eq!(ours_v1.as_ref(), theirs_v1.as_ref());
            Ed25519KeyPair::from_pkcs8(ours_v1.as_ref()).unwrap();

            let spki = theirs.public_key().as_der().unwrap();
            let parsed = ours::PublicKey::from_spki(spki.as_ref())
                .unwrap();
            prop_assert_eq!(parsed.as_ref(), public.as_ref());
            let ours_spki = parsed.to_spki();
            prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());
        }

        #[test]
        fn seed_and_public_key(seed in any::<[u8; 32]>(), other in any::<[u8; 32]>()) {
            // Both load a seed with its public key, and refuse it with another's.
            let public = Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
            let public = public.public_key().as_ref();
            let wrong = Ed25519KeyPair::from_seed_unchecked(&other).unwrap();
            let wrong = wrong.public_key().as_ref();

            ours::KeyPair::from_seed_and_public_key(&seed, public).unwrap();
            Ed25519KeyPair::from_seed_and_public_key(&seed, public).unwrap();
            prop_assert_eq!(
                ours::KeyPair::from_seed_and_public_key(&seed, wrong).is_ok(),
                seed == other
            );
            prop_assert_eq!(
                Ed25519KeyPair::from_seed_and_public_key(&seed, wrong).is_ok(),
                seed == other
            );
        }
    }

    /// libsodium's small-order encodings: each `y` of a small-order point
    /// that fits in 255 bits, with either sign.
    fn small_order() -> impl Iterator<Item = [u8; 32]> {
        [
            "0000000000000000000000000000000000000000000000000000000000000000",
            "0100000000000000000000000000000000000000000000000000000000000000",
            "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05",
            "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a",
            "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
            "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
            "eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        ]
        .into_iter()
        .flat_map(|y| {
            let y: [u8; 32] = hex::decode(y).unwrap().try_into().unwrap();
            [y, {
                let mut negative = y;
                negative[31] |= 0x80;
                negative
            }]
        })
    }

    #[test]
    fn small_order_public_keys() {
        // aws-lc-rs verifies a signature nobody made on each small-order point,
        // `S = 0` with `R = -[k]A`, itself of small order; rind refuses every
        // encoding. With the identity as `A`, `R` is the identity for any
        // message.
        let identity = small_order().nth(2).unwrap();
        let forged = [&identity[..], &[0; 32]].concat();
        UnparsedPublicKey::new(&ED25519, identity)
            .verify(b"any message", &forged)
            .unwrap();

        // `k` depends on `R`, so search the small-order points for one that
        // is `-[k]A`, which each is with odds of one in `A`'s order.
        let points: Vec<_> = small_order().collect();
        for public in small_order() {
            assert_eq!(
                ours::PublicKey::new(&public).unwrap_err().to_string(),
                "a key was rejected: a small-order point"
            );
            let theirs = UnparsedPublicKey::new(&ED25519, public);
            let forged = (0u8..=255).any(|message| {
                points.iter().any(|r| {
                    let forged = [&r[..], &[0; 32]].concat();
                    theirs.verify(&[message], &forged).is_ok()
                })
            });
            // aws-lc-rs verifies nothing on a non-canonical encoding, a sign on
            // `x = 0` or a `y` of `p` or `p + 1`, so the two differ on the eight
            // points alone.
            let canonical = !matches!(
                (public[0], public[31]),
                (0x01 | 0xec, 0x80..) | (0xed | 0xee, _)
            );
            assert_eq!(forged, canonical, "{public:x?}");
        }
    }
}

mod rsa {
    use std::sync::LazyLock;

    use aws_lc_rs::encoding::AsDer;
    use aws_lc_rs::rand::SystemRandom;
    use aws_lc_rs::rsa::{KeyPair, KeySize};
    use aws_lc_rs::signature::RsaPssSaltLength as TheirsSaltLength;
    use aws_lc_rs::signature::{self, KeyPair as _, UnparsedPublicKey};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::Error;
    use rind::rsa::{
        KeyPair as RsaKeyPair, PssSaltLength as RsaPssSaltLength,
        SigningAlgorithm as RsaSigningAlgorithm, VerificationAlgorithm as RsaVerificationAlgorithm,
        sign, verify,
    };

    /// One padding and hash: each side's signing and verification constants.
    struct Scheme {
        ours_sign: &'static RsaSigningAlgorithm,
        ours_verify: &'static RsaVerificationAlgorithm,
        theirs_sign: &'static signature::RsaSignatureEncoding,
        theirs_verify: &'static signature::RsaParameters,
        /// PKCS#1 v1.5 signatures have no randomness, so both sides must agree.
        deterministic: bool,
    }

    const SCHEMES: [Scheme; 6] = [
        Scheme {
            ours_sign: &sign::PKCS1_SHA256,
            ours_verify: &verify::PKCS1_SHA256,
            theirs_sign: &signature::RSA_PKCS1_SHA256,
            theirs_verify: &signature::RSA_PKCS1_2048_8192_SHA256,
            deterministic: true,
        },
        Scheme {
            ours_sign: &sign::PKCS1_SHA384,
            ours_verify: &verify::PKCS1_SHA384,
            theirs_sign: &signature::RSA_PKCS1_SHA384,
            theirs_verify: &signature::RSA_PKCS1_2048_8192_SHA384,
            deterministic: true,
        },
        Scheme {
            ours_sign: &sign::PKCS1_SHA512,
            ours_verify: &verify::PKCS1_SHA512,
            theirs_sign: &signature::RSA_PKCS1_SHA512,
            theirs_verify: &signature::RSA_PKCS1_2048_8192_SHA512,
            deterministic: true,
        },
        Scheme {
            ours_sign: &sign::PSS_SHA256,
            ours_verify: &verify::PSS_SHA256,
            theirs_sign: &signature::RSA_PSS_SHA256,
            theirs_verify: &signature::RSA_PSS_2048_8192_SHA256,
            deterministic: false,
        },
        Scheme {
            ours_sign: &sign::PSS_SHA384,
            ours_verify: &verify::PSS_SHA384,
            theirs_sign: &signature::RSA_PSS_SHA384,
            theirs_verify: &signature::RSA_PSS_2048_8192_SHA384,
            deterministic: false,
        },
        Scheme {
            ours_sign: &sign::PSS_SHA512,
            ours_verify: &verify::PSS_SHA512,
            theirs_sign: &signature::RSA_PSS_SHA512,
            theirs_verify: &signature::RSA_PSS_2048_8192_SHA512,
            deterministic: false,
        },
    ];

    #[test]
    fn key_generation_2048() {
        check_key_generation(rind::rsa::KeySize::Rsa2048);
    }

    #[test]
    fn key_generation_2048_soak() {
        if std::env::var_os("SLOW_TESTS").is_some() {
            for _ in 0..512 {
                check_key_generation(rind::rsa::KeySize::Rsa2048);
            }
        }
    }

    #[test]
    fn key_generation_3072() {
        check_key_generation(rind::rsa::KeySize::Rsa3072);
    }

    #[test]
    fn key_generation_4096() {
        if std::env::var_os("SLOW_TESTS").is_some() {
            check_key_generation(rind::rsa::KeySize::Rsa4096);
        }
    }

    #[test]
    fn key_generation_6144() {
        if std::env::var_os("SLOW_TESTS").is_some() {
            check_key_generation(rind::rsa::KeySize::Rsa6144);
        }
    }

    #[test]
    fn key_generation_8192() {
        if std::env::var_os("SLOW_TESTS").is_some() {
            check_key_generation(rind::rsa::KeySize::Rsa8192);
        }
    }

    /// aws-lc-rs accepts a key we generate and verifies its signatures under
    /// every scheme, as we do.
    fn check_key_generation(size: rind::rsa::KeySize) {
        let ours = RsaKeyPair::generate(size).unwrap();
        let theirs = KeyPair::from_pkcs8(ours.to_pkcs8().as_ref())
            .expect("aws-lc-rs rejected a key we generated");
        let public = theirs.public_key().as_ref();
        for scheme in &SCHEMES {
            let signature = ours.sign(scheme.ours_sign, b"hello").unwrap();
            UnparsedPublicKey::new(scheme.theirs_verify, public)
                .verify(b"hello", signature.as_ref())
                .unwrap();
            rind::rsa::PublicKey::new(public)
                .unwrap()
                .verify(scheme.ours_verify, b"hello", signature.as_ref())
                .unwrap();
        }
    }

    // Loaded by both: one key generated by aws-lc-rs (`check_key_generation`
    // covers the reverse), and OpenSSL keys aws-lc-rs cannot generate: moduli
    // that are not a whole number of words, and a 33-bit public exponent,
    // 2^32 + 1. At 2049 bits PSS's encoded message is a byte shorter than the
    // modulus, at 2050 bits it masks seven top bits, and 2056 bits is a whole
    // number of bytes. Key generation is slow under emulation, so there is
    // one of each.
    static THEIRS: LazyLock<[KeyPair; 5]> = LazyLock::new(|| {
        [
            KeyPair::generate(KeySize::Rsa2048).unwrap(),
            KeyPair::from_pkcs8(include_bytes!("../src/high/rsa/rsa2049.pkcs8.der")).unwrap(),
            KeyPair::from_pkcs8(include_bytes!("../src/high/rsa/rsa2050.pkcs8.der")).unwrap(),
            KeyPair::from_pkcs8(include_bytes!("../src/high/rsa/rsa2056.pkcs8.der")).unwrap(),
            KeyPair::from_pkcs8(include_bytes!("../src/high/rsa/rsa2048-e33.pkcs8.der")).unwrap(),
        ]
    });

    // Each case makes a dozen private-key operations per key, which are slow
    // under emulation.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(8))]

        #[test]
        fn sign_verify(message in vec(any::<u8>(), 0..300)) {
            for theirs in &*THEIRS {
                let ours = RsaKeyPair::from_pkcs8(theirs.as_der().unwrap().as_ref()).unwrap();
                let public = theirs.public_key().as_ref();
                let spki = theirs.public_key().as_der().unwrap();
                let ours_spki = ours.public_key().to_spki();
                prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());
                let rng = SystemRandom::new();
                let len = theirs.public_modulus_len();
                prop_assert_eq!(ours.public_key().modulus_len(), len);

                for scheme in &SCHEMES {
                    prop_assert_eq!(ours.public_key().as_ref(), public);

                    // It verifies our signature.
                    let ours_signature = ours.sign(scheme.ours_sign, &message).unwrap();
                    let ours_signature = ours_signature.as_ref();
                    prop_assert_eq!(ours_signature.len(), len);
                    UnparsedPublicKey::new(scheme.theirs_verify, public)
                        .verify(&message, ours_signature)
                        .unwrap();

                    // We verify its signature, and refuse it over another message.
                    let mut theirs_signature = vec![0u8; len];
                    theirs
                        .sign(scheme.theirs_sign, &rng, &message, &mut theirs_signature)
                        .unwrap();
                    if scheme.deterministic {
                        prop_assert_eq!(ours_signature, &theirs_signature[..]);
                    }
                    let verifier = rind::rsa::PublicKey::new(public).unwrap();
                    let verifier_spki = verifier.to_spki();
                    prop_assert_eq!(verifier_spki.as_ref(), spki.as_ref());
                    verifier.verify(scheme.ours_verify, &message, &theirs_signature).unwrap();
                    prop_assert_eq!(
                        verifier.verify(
                            scheme.ours_verify,
                            &[&message[..], b"!"].concat(),
                            &theirs_signature,
                        ),
                        Err(Error::BadSignature)
                    );
                }
            }
        }
    }

    /// One PSS hash with a chosen salt length: each side's constructor.
    struct PssSalt {
        ours_sign: fn(RsaPssSaltLength) -> RsaSigningAlgorithm,
        ours_verify: fn(RsaPssSaltLength) -> RsaVerificationAlgorithm,
        ours_any_salt: &'static RsaVerificationAlgorithm,
        theirs_sign: fn(TheirsSaltLength) -> signature::RsaSignatureEncoding,
        theirs_verify: fn(TheirsSaltLength) -> signature::RsaParameters,
        hash_len: usize,
    }

    const PSS_SALTS: [PssSalt; 3] = [
        PssSalt {
            ours_sign: RsaSigningAlgorithm::pss_sha256,
            ours_verify: RsaVerificationAlgorithm::pss_sha256,
            ours_any_salt: &verify::PSS_SHA256_ANY_SALT,
            theirs_sign: |salt| signature::RSA_PSS_SHA256.with_pss_salt_length(salt),
            theirs_verify: |salt| signature::RSA_PSS_2048_8192_SHA256.with_pss_salt_length(salt),
            hash_len: 32,
        },
        PssSalt {
            ours_sign: RsaSigningAlgorithm::pss_sha384,
            ours_verify: RsaVerificationAlgorithm::pss_sha384,
            ours_any_salt: &verify::PSS_SHA384_ANY_SALT,
            theirs_sign: |salt| signature::RSA_PSS_SHA384.with_pss_salt_length(salt),
            theirs_verify: |salt| signature::RSA_PSS_2048_8192_SHA384.with_pss_salt_length(salt),
            hash_len: 48,
        },
        PssSalt {
            ours_sign: RsaSigningAlgorithm::pss_sha512,
            ours_verify: RsaVerificationAlgorithm::pss_sha512,
            ours_any_salt: &verify::PSS_SHA512_ANY_SALT,
            theirs_sign: |salt| signature::RSA_PSS_SHA512.with_pss_salt_length(salt),
            theirs_verify: |salt| signature::RSA_PSS_2048_8192_SHA512.with_pss_salt_length(salt),
            hash_len: 64,
        },
    ];

    // As `sign_verify`, a dozen private-key operations per key per case.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(8))]

        /// Each side verifies the other's PSS signatures with any salt length
        /// the modulus allows, as does any-salt verification, and both refuse
        /// one a byte longer.
        #[test]
        fn pss_salt_lengths(salt in any::<u16>(), message in vec(any::<u8>(), 0..300)) {
            for theirs in &*THEIRS {
                let ours = RsaKeyPair::from_pkcs8(theirs.as_der().unwrap().as_ref()).unwrap();
                let public = theirs.public_key().as_ref();
                let bits = signature::RsaParameters::public_modulus_len(public).unwrap() as usize;
                let rng = SystemRandom::new();

                for pss in &PSS_SALTS {
                    let ours_public = rind::rsa::PublicKey::new(public).unwrap();
                    // RFC 8017 section 9.1.1's `emLen - hLen - 2`.
                    let max = u16::try_from((bits - 1).div_ceil(8) - pss.hash_len - 2).unwrap();
                    let custom = salt % (max + 1);

                    for (ours_salt, theirs_salt) in [
                        (RsaPssSaltLength::Custom(custom), TheirsSaltLength::Custom(custom)),
                        (RsaPssSaltLength::Max, TheirsSaltLength::Max),
                        (RsaPssSaltLength::Custom(max + 1), TheirsSaltLength::Custom(max + 1)),
                    ] {
                        // aws-lc-rs takes only `'static` algorithms.
                        let theirs_sign = Box::leak(Box::new((pss.theirs_sign)(theirs_salt)));
                        let theirs_verify = Box::leak(Box::new((pss.theirs_verify)(theirs_salt)));
                        let ours_sign = (pss.ours_sign)(ours_salt);
                        let ours_verify = (pss.ours_verify)(ours_salt);

                        let mut theirs_signature = vec![0u8; theirs.public_modulus_len()];
                        let theirs_signed =
                            theirs.sign(theirs_sign, &rng, &message, &mut theirs_signature);
                        if ours_salt == RsaPssSaltLength::Custom(max + 1) {
                            prop_assert!(theirs_signed.is_err());
                            prop_assert!(matches!(
                                ours.sign(&ours_sign, &message),
                                Err(Error::KeyRejected(_))
                            ));
                            prop_assert!(matches!(
                                ours_public.verify(&ours_verify, &message, &theirs_signature),
                                Err(Error::KeyRejected(_))
                            ));
                            continue;
                        }
                        theirs_signed.unwrap();
                        let other_message = [&message[..], b"!"].concat();
                        for verifier in [&ours_verify, pss.ours_any_salt] {
                            ours_public.verify(verifier, &message, &theirs_signature).unwrap();
                            prop_assert_eq!(
                                ours_public.verify(verifier, &other_message, &theirs_signature),
                                Err(Error::BadSignature)
                            );
                        }

                        let ours_signature = ours.sign(&ours_sign, &message).unwrap();
                        UnparsedPublicKey::new(theirs_verify, public)
                            .verify(&message, ours_signature.as_ref())
                            .unwrap();
                        ours.public_key()
                            .verify(&ours_verify, &message, ours_signature.as_ref())
                            .unwrap();
                    }
                }
            }
        }
    }

    // Every verification algorithm, beside aws-lc-rs's of the same name.
    const VERIFICATION: [(&RsaVerificationAlgorithm, &signature::RsaParameters); 11] = [
        (
            &verify::legacy::PKCS1_1024_SHA1,
            &signature::RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY,
        ),
        (
            &verify::legacy::PKCS1_1024_SHA256,
            &signature::RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY,
        ),
        (
            &verify::legacy::PKCS1_1024_SHA512,
            &signature::RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY,
        ),
        (
            &verify::legacy::PKCS1_SHA1,
            &signature::RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY,
        ),
        (
            &verify::PKCS1_SHA256,
            &signature::RSA_PKCS1_2048_8192_SHA256,
        ),
        (
            &verify::PKCS1_SHA384,
            &signature::RSA_PKCS1_2048_8192_SHA384,
        ),
        (
            &verify::PKCS1_SHA512,
            &signature::RSA_PKCS1_2048_8192_SHA512,
        ),
        (
            &verify::legacy::PKCS1_3072_SHA384,
            &signature::RSA_PKCS1_3072_8192_SHA384,
        ),
        (&verify::PSS_SHA256, &signature::RSA_PSS_2048_8192_SHA256),
        (&verify::PSS_SHA384, &signature::RSA_PSS_2048_8192_SHA384),
        (&verify::PSS_SHA512, &signature::RSA_PSS_2048_8192_SHA512),
    ];

    /// Both accept and refuse the same signatures under every algorithm, for
    /// keys as DER or as components. aws-lc-rs signs neither SHA-1 nor
    /// 1024-bit keys, so the signatures are Wycheproof's.
    #[test]
    fn verification_agrees() {
        for file in [
            "rsa_pkcs1_1024_sig_gen_test.json",
            "rsa_pkcs1_2048_sig_gen_test.json",
        ] {
            let path = format!(
                "{}/../thirdparty/vectors/wycheproof/testvectors_v1/{file}",
                env!("CARGO_MANIFEST_DIR")
            );
            let tests: serde_json::Value =
                serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
            for group in tests["testGroups"].as_array().unwrap() {
                let hex = |value: &serde_json::Value| hex::decode(value.as_str().unwrap()).unwrap();
                let der = hex(&group["keyAsn"]);
                let modulus = hex(&group["privateKey"]["modulus"]);
                let e = hex(&group["privateKey"]["publicExponent"]);
                // A leading zero, as the DER sign byte leaves, is refused.
                let n = modulus.strip_prefix(&[0]).unwrap();

                for (i, test) in group["tests"].as_array().unwrap().iter().enumerate() {
                    let message = hex(&test["msg"]);
                    let signature = hex(&test["sig"]);
                    let other = [&message[..], b"!"].concat();
                    // Another message is refused alike, so checking it once
                    // per group keeps this fast under emulation.
                    let messages = match i {
                        0 => &[&message[..], &other][..],
                        _ => &[&message[..]],
                    };

                    for message in messages {
                        for (ours, theirs) in VERIFICATION {
                            let case = format!("{file} {i} {ours:?}");
                            for n in [n, &modulus] {
                                let components = rind::rsa::PublicKeyComponents { n, e: &e };
                                let ours = rind::rsa::PublicKey::from_components(&components)
                                    .and_then(|key| key.verify(ours, message, &signature));
                                let theirs = signature::RsaPublicKeyComponents { n, e: &e }
                                    .verify(theirs, message, &signature);
                                assert_eq!(ours.is_ok(), theirs.is_ok(), "{case} {ours:?}");
                            }

                            let ours = rind::rsa::PublicKey::new(&der)
                                .and_then(|key| key.verify(ours, message, &signature));
                            let theirs =
                                UnparsedPublicKey::new(theirs, &der).verify(message, &signature);
                            assert_eq!(ours.is_ok(), theirs.is_ok(), "{case} {ours:?}");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn refuses_modulus_below_2048_bits() {
        let private = include_bytes!("../src/high/rsa/rsa2047.pkcs8.der");
        assert!(KeyPair::from_pkcs8(private).is_err());
        assert!(matches!(
            RsaKeyPair::from_pkcs8(private),
            Err(Error::KeyRejected(_))
        ));
        // The public key parses, as a legacy algorithm verifies with it,
        // and the others refuse it.
        let public = include_bytes!("../src/high/rsa/rsa2047.pub.der");
        let public = rind::rsa::PublicKey::new(public).unwrap();
        // So a caller can refuse it at load, as aws-lc-rs's length reads it.
        assert_eq!(public.modulus_len(), 256);
        assert!(matches!(
            public.verify(&verify::PKCS1_SHA256, b"message", &[0; 256]),
            Err(Error::KeyRejected(_))
        ));
    }

    /// An OpenSSL key with e = 2^33 + 1, just past the 33 bits both take, and
    /// its signature over "message", which OpenSSL verifies.
    #[test]
    fn refuses_exponent_over_33_bits() {
        let private = include_bytes!("../src/high/rsa/rsa2048-e34.pkcs8.der");
        assert!(KeyPair::from_pkcs8(private).is_err());
        assert!(matches!(
            RsaKeyPair::from_pkcs8(private),
            Err(Error::KeyRejected(_))
        ));
        let public = include_bytes!("../src/high/rsa/rsa2048-e34.pub.der");
        let signature = include_bytes!("../src/high/rsa/rsa2048-e34.sig");
        assert!(
            UnparsedPublicKey::new(&signature::RSA_PKCS1_2048_8192_SHA256, public)
                .verify(b"message", signature)
                .is_err()
        );
        assert!(matches!(
            rind::rsa::PublicKey::new(public),
            Err(Error::KeyRejected(_))
        ));
    }

    mod oaep {
        use aws_lc_rs::encoding::{AsDer, PublicKeyX509Der};
        use aws_lc_rs::rand::SystemRandom;
        use aws_lc_rs::rsa::{
            OAEP_SHA1_MGF1SHA1, OAEP_SHA256_MGF1SHA256, OAEP_SHA384_MGF1SHA384,
            OAEP_SHA512_MGF1SHA512, OaepAlgorithm, OaepPrivateDecryptingKey,
            OaepPublicEncryptingKey, PrivateDecryptingKey, PublicEncryptingKey,
        };
        use aws_lc_rs::signature::{self, KeyPair as _, UnparsedPublicKey};
        use proptest::collection::vec;
        use proptest::prelude::*;
        use rind::Error;
        use rind::rsa::verify;
        use rind::rsa::{self as ours, DecryptingKey, EncryptingKey};

        use super::THEIRS;
        use crate::der;

        /// The object identifiers of `rsaEncryption`, `id-RSAES-OAEP`, and
        /// X.509's `id-ea-rsa`, all for the same key, and of RSASSA-PSS, which
        /// restricts it.
        const RSA_ENCRYPTION: [u8; 11] = [
            0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01,
        ];
        const RSAES_OAEP: [u8; 11] = [
            0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x07,
        ];
        const EA_RSA: [u8; 6] = [0x06, 0x04, 0x55, 0x08, 0x01, 0x01];
        const RSASSA_PSS: [u8; 11] = [
            0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a,
        ];

        const ALGORITHMS: [(&ours::OaepAlgorithm, &OaepAlgorithm); 4] = [
            (&ours::legacy::OAEP_SHA1, &OAEP_SHA1_MGF1SHA1),
            (&ours::OAEP_SHA256, &OAEP_SHA256_MGF1SHA256),
            (&ours::OAEP_SHA384, &OAEP_SHA384_MGF1SHA384),
            (&ours::OAEP_SHA512, &OAEP_SHA512_MGF1SHA512),
        ];

        /// For each of `THEIRS` and each algorithm: our key, and aws-lc-rs's
        /// and its public key, loaded from its PKCS#8.
        fn keys() -> impl Iterator<
            Item = (
                &'static ours::OaepAlgorithm,
                &'static OaepAlgorithm,
                DecryptingKey,
                OaepPrivateDecryptingKey,
                PublicEncryptingKey,
            ),
        > {
            THEIRS.iter().flat_map(|theirs| {
                let pkcs8 = theirs.as_der().unwrap();
                ALGORITHMS.map(|(ours_algorithm, theirs_algorithm)| {
                    let ours = DecryptingKey::from_pkcs8(ours_algorithm, pkcs8.as_ref()).unwrap();
                    let theirs = PrivateDecryptingKey::from_pkcs8(pkcs8.as_ref()).unwrap();
                    let public = theirs.public_key();
                    (
                        ours_algorithm,
                        theirs_algorithm,
                        ours,
                        OaepPrivateDecryptingKey::new(theirs).unwrap(),
                        public,
                    )
                })
            })
        }

        fn decrypt(
            key: &OaepPrivateDecryptingKey,
            algorithm: &'static OaepAlgorithm,
            ciphertext: &[u8],
            label: &[u8],
        ) -> Option<Vec<u8>> {
            let mut out = vec![0; key.min_output_size()];
            let out = key
                .decrypt(algorithm, ciphertext, &mut out, Some(label))
                .ok()?;
            Some(out.to_vec())
        }

        // Each case makes several private-key operations per key and
        // algorithm, which are slow under emulation.
        proptest! {
            #![proptest_config(ProptestConfig::with_cases(4))]

            /// Each decrypts what the other encrypts, through the SPKI each
            /// gives the other.
            #[test]
            fn encrypt_decrypt(
                message in vec(any::<u8>(), 0..200),
                label in vec(any::<u8>(), 0..40),
            ) {
                for (ours_algorithm, theirs_algorithm, ours, theirs, public) in keys() {
                    let spki: PublicKeyX509Der<'_> = public.as_der().unwrap();
                    let ours_spki = ours.public_key().to_spki();
                    prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());
                    let ours_public = EncryptingKey::from_spki(ours_algorithm, spki.as_ref()).unwrap();
                    let ours_public_spki = ours_public.to_spki();
                    prop_assert_eq!(ours_public_spki.as_ref(), spki.as_ref());
                    let theirs_public = OaepPublicEncryptingKey::new(
                        PublicEncryptingKey::from_der(ours_public_spki.as_ref()).unwrap(),
                    )
                    .unwrap();

                    let max = theirs_public.max_plaintext_size(theirs_algorithm);
                    prop_assert_eq!(ours_public.max_message_len(), max);
                    let message = &message[..message.len().min(max)];

                    let ciphertext = ours_public.encrypt(message, &label).unwrap();
                    let decrypted = decrypt(&theirs, theirs_algorithm, ciphertext.as_ref(), &label);
                    prop_assert_eq!(decrypted.as_deref(), Some(message));

                    let mut ciphertext = vec![0; theirs_public.ciphertext_size()];
                    let ciphertext = theirs_public
                        .encrypt(theirs_algorithm, message, &mut ciphertext, Some(&label))
                        .unwrap();
                    let decrypted = ours.decrypt(ciphertext, &label).unwrap();
                    prop_assert_eq!(decrypted.as_ref(), message);
                }
            }

            /// Both accept the same ciphertexts, tampered with or made up,
            /// and decrypt them to the same message.
            #[test]
            fn decrypt_agrees(
                flip in any::<prop::sample::Index>(),
                bytes in vec(any::<u8>(), 256..=257),
            ) {
                for (_, theirs_algorithm, ours, theirs, _) in keys() {
                    let ciphertext = ours.public_key().encrypt(b"message", b"").unwrap();
                    let mut tampered = ciphertext.as_ref().to_vec();
                    let i = flip.index(tampered.len());
                    tampered[i] ^= 1;
                    for ciphertext in [&tampered, &bytes] {
                        let ours = ours.decrypt(ciphertext, b"");
                        let theirs = decrypt(&theirs, theirs_algorithm, ciphertext, b"");
                        match (&ours, &theirs) {
                            (Ok(ours), Some(theirs)) => prop_assert_eq!(ours.as_ref(), &theirs[..]),
                            (Err(Error::DecryptFailed), None) => {}
                            _ => prop_assert!(false, "ours {:?}, theirs {:?}", ours, theirs),
                        }
                    }
                }
            }
        }

        /// RSA SPKI forms through `EncryptingKey::from_spki` and
        /// `rsa::PublicKey::from_spki`, each beside aws-lc-rs, which also
        /// ignores the algorithm's parameters and bytes after the SPKI.
        #[test]
        fn spki_forms_agree() {
            let theirs = &THEIRS[0];
            let pkcs1 = theirs.public_key().as_ref();
            let rsa_encryption = RSA_ENCRYPTION;
            let ec_public_key = [0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
            let null = |oid: &[u8]| [oid, &[0x05, 0x00]].concat();
            let rsa_null = null(&rsa_encryption);
            let spki = |algorithm: &[u8], bits: &[u8]| {
                der(0x30, &[der(0x30, algorithm), der(0x03, bits)].concat())
            };
            let key = [&[0][..], pkcs1].concat();

            // Each form, whether rind takes it, and whether aws-lc-rs does.
            let cases: [(&str, Vec<u8>, bool, bool); 14] = [
                ("canonical", spki(&rsa_null, &key), true, true),
                ("no parameters", spki(&rsa_encryption, &key), true, true),
                ("id-RSAES-OAEP", spki(&null(&RSAES_OAEP), &key), true, true),
                (
                    "id-RSAES-OAEP, no parameters",
                    spki(&RSAES_OAEP, &key),
                    true,
                    true,
                ),
                (
                    "id-RSAES-OAEP, default RSAES-OAEP-params",
                    spki(&[&RSAES_OAEP[..], &[0x30, 0x00]].concat(), &key),
                    false,
                    true,
                ),
                ("id-ea-rsa", spki(&null(&EA_RSA), &key), true, true),
                ("id-ea-rsa, no parameters", spki(&EA_RSA, &key), true, true),
                (
                    "empty-sequence parameters",
                    spki(&[&rsa_encryption[..], &[0x30, 0x00]].concat(), &key),
                    false,
                    true,
                ),
                ("RSASSA-PSS", spki(&null(&RSASSA_PSS), &key), false, false),
                ("EC", spki(&null(&ec_public_key), &key), false, false),
                (
                    "unused bits",
                    spki(&rsa_null, &[&[1][..], pkcs1].concat()),
                    false,
                    false,
                ),
                ("empty bit string", spki(&rsa_null, &[]), false, false),
                (
                    "trailing data",
                    [spki(&rsa_null, &key), vec![0]].concat(),
                    false,
                    true,
                ),
                (
                    "trailing key data",
                    spki(&rsa_null, &[&key[..], &[0]].concat()),
                    false,
                    false,
                ),
            ];
            assert_eq!(cases[0].1, theirs.public_key().as_der().unwrap().as_ref());

            let message = b"message";
            let mut signature = vec![0; theirs.public_modulus_len()];
            theirs
                .sign(
                    &signature::RSA_PKCS1_SHA256,
                    &SystemRandom::new(),
                    message,
                    &mut signature,
                )
                .unwrap();

            for (case, der, ours_take, theirs_take) in &cases {
                assert_eq!(
                    PublicEncryptingKey::from_der(der).is_ok(),
                    *theirs_take,
                    "{case}"
                );
                let ours = EncryptingKey::from_spki(&ours::OAEP_SHA256, der);
                assert_eq!(ours.is_ok(), *ours_take, "{case}: {ours:?}");
                if let Ok(ours) = ours {
                    assert_eq!(ours.as_ref(), pkcs1, "{case}");
                }

                let theirs = UnparsedPublicKey::new(&signature::RSA_PKCS1_2048_8192_SHA256, der)
                    .verify(message, &signature);
                assert_eq!(theirs.is_ok(), *theirs_take, "{case}");
                let ours = ours::PublicKey::from_spki(der);
                assert_eq!(ours.is_ok(), *ours_take, "{case}: {ours:?}");
                if let Ok(ours) = ours {
                    assert_eq!(ours.as_ref(), pkcs1, "{case}");
                    ours.verify(&verify::PKCS1_SHA256, message, &signature)
                        .unwrap();
                }
            }
        }

        /// RSA PKCS#8 algorithm identifiers through `DecryptingKey` and
        /// `rsa::KeyPair`, each beside aws-lc-rs, which requires `NULL`
        /// parameters for every RSA algorithm it takes.
        #[test]
        fn pkcs8_algorithms_agree() {
            let theirs = &THEIRS[0];
            let canonical = theirs.as_der().unwrap();
            let canonical = canonical.as_ref();
            let rsa_null = [
                0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01, 0x05,
                0x00,
            ];
            let at = canonical
                .windows(rsa_null.len())
                .position(|w| w == rsa_null)
                .unwrap();
            let (version, private_key) = (&canonical[4..at], &canonical[at + rsa_null.len()..]);
            let pkcs8 = |algorithm: &[u8]| {
                der(
                    0x30,
                    &[version, &der(0x30, algorithm), private_key].concat(),
                )
            };
            let null = |oid: &[u8]| [oid, &[0x05, 0x00]].concat();

            // Each algorithm identifier, and whether both sides take it.
            let cases: [(&str, Vec<u8>, bool); 9] = [
                ("rsaEncryption", null(&RSA_ENCRYPTION), true),
                (
                    "rsaEncryption, no parameters",
                    RSA_ENCRYPTION.to_vec(),
                    false,
                ),
                ("id-RSAES-OAEP", null(&RSAES_OAEP), true),
                ("id-RSAES-OAEP, no parameters", RSAES_OAEP.to_vec(), false),
                (
                    "id-RSAES-OAEP, default RSAES-OAEP-params",
                    [&RSAES_OAEP[..], &[0x30, 0x00]].concat(),
                    false,
                ),
                ("id-ea-rsa", null(&EA_RSA), true),
                ("id-ea-rsa, no parameters", EA_RSA.to_vec(), false),
                (
                    "id-ea-rsa, KeySize",
                    [&EA_RSA[..], &[0x02, 0x02, 0x08, 0x00]].concat(),
                    false,
                ),
                ("RSASSA-PSS", null(&RSASSA_PSS), false),
            ];
            assert_eq!(pkcs8(&cases[0].1), canonical);

            let public = theirs.public_key().as_ref();
            for (case, algorithm, take) in &cases {
                let der = pkcs8(algorithm);
                let theirs = PrivateDecryptingKey::from_pkcs8(&der);
                assert_eq!(theirs.is_ok(), *take, "{case}");
                let theirs = aws_lc_rs::rsa::KeyPair::from_pkcs8(&der);
                assert_eq!(theirs.is_ok(), *take, "{case}");

                let ours = DecryptingKey::from_pkcs8(&ours::OAEP_SHA256, &der);
                assert_eq!(ours.is_ok(), *take, "{case}: {ours:?}");
                if let Ok(ours) = ours {
                    assert_eq!(ours.public_key().as_ref(), public, "{case}");
                    // It writes back as `rsaEncryption`, as aws-lc does.
                    assert_eq!(ours.to_pkcs8().as_ref(), canonical, "{case}");
                }
                let ours = ours::KeyPair::from_pkcs8(&der);
                assert_eq!(ours.is_ok(), *take, "{case}: {ours:?}");
                if let Ok(ours) = ours {
                    assert_eq!(ours.public_key().as_ref(), public, "{case}");
                }
            }
        }
    }
}

mod mlkem {
    use aws_lc_rs::kem::{
        Algorithm, AlgorithmId, Ciphertext, DecapsulationKey, ML_KEM_512, ML_KEM_768, ML_KEM_1024,
    };
    use proptest::prelude::*;
    use rind::kem;

    // aws-lc-rs decapsulates what we encapsulate to its key.
    fn encapsulated_by_ours<A: kem::Algorithm>(
        algorithm: &'static Algorithm<AlgorithmId>,
    ) -> Result<(), TestCaseError> {
        let theirs = DecapsulationKey::generate(algorithm).unwrap();
        let theirs_public = theirs.encapsulation_key().unwrap().key_bytes().unwrap();
        let (ciphertext, secret) = kem::EncapsulationKey::<A>::new(theirs_public.as_ref())
            .unwrap()
            .encapsulate()
            .unwrap();
        let theirs_secret = theirs
            .decapsulate(Ciphertext::from(ciphertext.as_ref()))
            .unwrap();
        prop_assert_eq!(secret.as_ref(), theirs_secret.as_ref());
        Ok(())
    }

    // Each case generates a key, which is slow under emulation.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(32))]

        #[test]
        fn encapsulated_by_ours_512(_case in any::<u8>()) {
            encapsulated_by_ours::<kem::MlKem512>(&ML_KEM_512)?;
        }

        #[test]
        fn encapsulated_by_ours_768(_case in any::<u8>()) {
            encapsulated_by_ours::<kem::MlKem768>(&ML_KEM_768)?;
        }

        #[test]
        fn encapsulated_by_ours_1024(_case in any::<u8>()) {
            encapsulated_by_ours::<kem::MlKem1024>(&ML_KEM_1024)?;
        }
    }
}

/// PKCS#8's optional attributes: both sides skip them, uninterpreted, and
/// refuse the same malformed ones, on every key type.
mod pkcs8_attributes {
    use aws_lc_rs::rsa::KeyPair as TheirsRsaKeyPair;
    use aws_lc_rs::signature::{self as theirs, KeyPair as _};
    use rind::{ecdsa, ed25519, rsa};

    /// A PKCS#8 document, and each side's loader for its key type, which
    /// gives the public key.
    struct Key {
        pkcs8: Vec<u8>,
        /// Whether the document is v2, ending in a public key.
        v2: bool,
        ours: fn(&[u8]) -> Option<Vec<u8>>,
        theirs: fn(&[u8]) -> Option<Vec<u8>>,
    }

    macro_rules! ecdsa {
        ($ours:ident, $theirs:ident) => {
            Key {
                pkcs8: ecdsa::KeyPair::generate(&ecdsa::sign::$ours)
                    .unwrap()
                    .to_pkcs8()
                    .as_ref()
                    .to_vec(),
                v2: false,
                ours: |der| {
                    let key = ecdsa::KeyPair::from_pkcs8(&ecdsa::sign::$ours, der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
                theirs: |der| {
                    let key = theirs::EcdsaKeyPair::from_pkcs8(&theirs::$theirs, der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
            }
        };
    }

    fn keys() -> [Key; 5] {
        [
            ecdsa!(P256_SHA256_ASN1, ECDSA_P256_SHA256_ASN1_SIGNING),
            ecdsa!(P384_SHA384_ASN1, ECDSA_P384_SHA384_ASN1_SIGNING),
            ecdsa!(P521_SHA512_ASN1, ECDSA_P521_SHA512_ASN1_SIGNING),
            Key {
                pkcs8: include_bytes!("../src/high/rsa/rsa2056.pkcs8.der").to_vec(),
                v2: false,
                ours: |der| {
                    let key = rsa::KeyPair::from_pkcs8(der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
                theirs: |der| {
                    let key = TheirsRsaKeyPair::from_pkcs8(der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
            },
            Key {
                pkcs8: ed25519::KeyPair::generate()
                    .unwrap()
                    .to_pkcs8()
                    .as_ref()
                    .to_vec(),
                v2: true,
                ours: |der| {
                    let key = ed25519::KeyPair::from_pkcs8(der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
                theirs: |der| {
                    let key = theirs::Ed25519KeyPair::from_pkcs8(der);
                    key.ok().map(|key| key.public_key().as_ref().to_vec())
                },
            },
        ]
    }

    /// The header and body lengths of the DER element starting `der`.
    fn element(der: &[u8]) -> (usize, usize) {
        match der[1] {
            len @ 0..=0x7f => (2, usize::from(len)),
            0x81 => (3, usize::from(der[2])),
            0x82 => (4, usize::from(u16::from_be_bytes([der[2], der[3]]))),
            _ => unreachable!("no test document is that long"),
        }
    }

    /// `pkcs8` with `fields` inserted after its first `after` fields.
    fn insert(pkcs8: &[u8], after: usize, fields: &[u8]) -> Vec<u8> {
        let (header, len) = element(pkcs8);
        let mut body = pkcs8[header..header + len].to_vec();
        let mut at = 0;
        for _ in 0..after {
            let (header, len) = element(&body[at..]);
            at += header + len;
        }
        body.splice(at..at, fields.iter().copied());

        let header = match body.len() {
            len @ 0..=0x7f => vec![0x30, len as u8],
            len @ 0x80..=0xff => vec![0x30, 0x81, len as u8],
            len => [
                &[0x30, 0x82][..],
                &u16::try_from(len).unwrap().to_be_bytes(),
            ]
            .concat(),
        };
        [header, body].concat()
    }

    /// Both sides refuse an ECDSA or RSA v2 document with its public key, which
    /// would go unchecked. Ed25519 checks it.
    #[test]
    fn ecdsa_and_rsa_refuse_v2() {
        for key in keys() {
            let public = (key.ours)(&key.pkcs8).unwrap();
            let v2 = match key.v2 {
                true => key.pkcs8.clone(),
                false => {
                    let field = crate::der(0x81, &[&[0][..], &public].concat());
                    let mut v2 = insert(&key.pkcs8, 3, &field);
                    let (header, _) = element(&v2);
                    assert_eq!(v2[header..header + 3], [0x02, 0x01, 0x00]);
                    v2[header + 2] = 0x01;
                    v2
                }
            };
            let expected = key.v2.then_some(&public[..]);
            assert_eq!((key.ours)(&v2).as_deref(), expected, "{v2:02x?}");
            assert_eq!((key.theirs)(&v2).as_deref(), expected, "{v2:02x?}");
        }
    }

    /// `pkcs8`, a v1 document, as version 2 without a public key.
    fn as_v2(pkcs8: &[u8]) -> Vec<u8> {
        let mut v2 = pkcs8.to_vec();
        let (header, _) = element(&v2);
        assert_eq!(v2[header..header + 3], [0x02, 0x01, 0x00]);
        v2[header + 2] = 0x01;
        v2
    }

    /// RFC 5958 makes a v2 document's public key optional, and both sides
    /// take one without it, for every key type.
    #[test]
    fn v2_without_public_key() {
        use aws_lc_rs::signature::{ML_DSA_44_SIGNING, PqdsaKeyPair};
        use rind::ml_dsa::{KeyPair as MlDsaKeyPair, MlDsa44};

        for key in keys() {
            let v1 = match key.v2 {
                // Drop the Ed25519 document's trailing 32-byte public key.
                true => {
                    let mut body = key.pkcs8[2..key.pkcs8.len() - 35].to_vec();
                    body[2] = 0x00;
                    [&[0x30, body.len() as u8][..], &body].concat()
                }
                false => key.pkcs8.clone(),
            };
            let public = (key.ours)(&v1).unwrap();
            let v2 = as_v2(&v1);
            assert_eq!((key.ours)(&v2).as_deref(), Some(&public[..]), "{v2:02x?}");
            assert_eq!((key.theirs)(&v2).as_deref(), Some(&public[..]), "{v2:02x?}");
        }

        let ours = MlDsaKeyPair::<MlDsa44>::from_seed(&[7; 32]).unwrap();
        let v2 = as_v2(ours.to_pkcs8().as_ref());
        let theirs = PqdsaKeyPair::from_pkcs8(&ML_DSA_44_SIGNING, &v2).unwrap();
        let ours = MlDsaKeyPair::<MlDsa44>::from_pkcs8(&v2).unwrap();
        assert_eq!(ours.public_key().as_ref(), theirs.public_key().as_ref());

        let private = [9; 32];
        let ours =
            rind::agreement::PrivateKey::from_scalar(&rind::agreement::X25519, &private).unwrap();
        let v2 = as_v2(ours.to_pkcs8().as_ref());
        assert_eq!(crate::ecdh_scalars::aws_lc_x25519_from_pkcs8(&v2), private);
        let loaded =
            rind::agreement::PrivateKey::from_pkcs8(&rind::agreement::X25519, &v2).unwrap();
        assert_eq!(loaded.public_key().as_ref(), ours.public_key().as_ref());
    }

    #[test]
    fn attributes() {
        // RFC 8410's example, and contents that are not DER at all.
        let rfc_8410 =
            hex::decode("a01f301d060a2a864886f70d01090914310f0c0d437572646c6520436861697273")
                .unwrap();
        let skipped: [&[u8]; 3] = [&[0xa0, 0x00], &rfc_8410, &[0xa0, 0x03, 0xff, 0xff, 0xff]];
        let refused: [&[u8]; 5] = [
            &[0xa0, 0x7f, 0x31, 0x00], // truncated
            &[0x80, 0x00],             // primitive
            &[0xa2, 0x00],             // another tag
            &[0xa0, 0x00, 0x05, 0x00], // trailing garbage
            &[0xa0, 0x00, 0xa0, 0x00], // twice
        ];

        for key in keys() {
            let plain = (key.ours)(&key.pkcs8).unwrap();
            let check = |pkcs8: &[u8], expected: Option<&[u8]>| {
                let (ours, theirs) = ((key.ours)(pkcs8), (key.theirs)(pkcs8));
                assert_eq!(ours.as_deref(), expected, "{pkcs8:02x?}");
                assert_eq!(theirs.as_deref(), expected, "{pkcs8:02x?}");
            };

            // After the version, algorithm, and private key.
            for fields in skipped {
                check(&insert(&key.pkcs8, 3, fields), Some(&plain));
            }
            for fields in refused {
                check(&insert(&key.pkcs8, 3, fields), None);
            }
            // Following a v2 document's public key, out of order.
            if key.v2 {
                check(&insert(&key.pkcs8, 4, &[0xa0, 0x00]), None);
            }
        }
    }
}

mod ecdh_scalars {
    use aws_lc_rs::agreement::{self, ECDH_P256, PrivateKey, UnparsedPublicKey, X25519};
    use aws_lc_rs::encoding::{AsBigEndian, AsDer, Curve25519SeedBin};
    use proptest::prelude::*;
    use rind::agreement as ours;

    /// n - 1, the largest P-256 private key.
    const N_MINUS_1: [u8; 32] = [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63,
        0x25, 0x50,
    ];

    /// (n - 1) / 2, the largest scalar `p256_scalarmul` leaves unnegated.
    const HALF_N: [u8; 32] = [
        0x7f, 0xff, 0xff, 0xff, 0x80, 0x00, 0x00, 0x00, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xde, 0x73, 0x7d, 0x56, 0xd3, 0x8b, 0xcf, 0x42, 0x79, 0xdc, 0xe5, 0x61, 0x7e, 0x31,
        0x92, 0xa8,
    ];

    /// `x + d`, for a last byte that neither carries nor borrows.
    fn add_small(mut x: [u8; 32], d: i8) -> [u8; 32] {
        x[31] = x[31].checked_add_signed(d).unwrap();
        x
    }

    /// A P-256 private key, biased to 1, n - 1, and either side of n / 2,
    /// where the scalar multiplication negates it.
    fn p256_scalar() -> impl Strategy<Value = [u8; 32]> {
        let small = |k| add_small([0; 32], k);
        prop_oneof![
            // Below n, as its first byte is.
            4 => any::<[u8; 32]>().prop_map(|mut k| {
                k[0] %= 0xff;
                k
            }),
            1 => prop_oneof![
                Just(small(1)),
                Just(small(2)),
                Just(add_small(N_MINUS_1, -1)),
                Just(N_MINUS_1),
                Just(HALF_N),
                Just(add_small(HALF_N, 1)),
            ],
        ]
    }

    // Any 32 bytes is a private key or a peer's u-coordinate, including
    // coordinates at or above the field prime. The fixed peers have small
    // order, which both sides refuse for the all-zero secret they give.
    fn x25519_peer() -> impl Strategy<Value = [u8; 32]> {
        let mut one = [0u8; 32];
        one[0] = 1;
        prop_oneof![
            8 => any::<[u8; 32]>(),
            1 => Just([0u8; 32]),
            1 => Just(one),
        ]
    }

    /// Both sides load `private` and agree with `peer`, which is an encoded
    /// public key for `ecdh`; both refuse it, or give the same secret.
    fn check(
        ours_alg: &'static ours::Algorithm,
        theirs_alg: &'static agreement::Algorithm,
        private: &[u8],
        peer: &[u8],
    ) -> Result<(), TestCaseError> {
        let ours = ours::PrivateKey::from_scalar(ours_alg, private).unwrap();
        let theirs = PrivateKey::from_private_key(theirs_alg, private).unwrap();
        let theirs_public = theirs.compute_public_key().unwrap();
        let ours_public = ours.public_key();
        prop_assert_eq!(ours_public.as_ref(), theirs_public.as_ref());

        let ours_secret = ours.agree(peer).map(|secret| secret.as_ref().to_vec());
        let theirs_secret = agreement::agree(
            &theirs,
            UnparsedPublicKey::new(theirs_alg, peer),
            (),
            |secret| Ok(secret.to_vec()),
        );
        match (ours_secret, theirs_secret) {
            (Ok(ours), Ok(theirs)) => prop_assert_eq!(ours, theirs),
            (Err(_), Err(())) => {}
            (ours, theirs) => prop_assert!(
                false,
                "rind gave {:?}, aws-lc-rs {:?}",
                ours.err(),
                theirs.err()
            ),
        }
        Ok(())
    }

    proptest! {
        #[test]
        fn p256(private in p256_scalar(), peer in p256_scalar()) {
            let peer = PrivateKey::from_private_key(&ECDH_P256, &peer)
                .unwrap()
                .compute_public_key()
                .unwrap();
            check(&ours::ECDH_P256, &ECDH_P256, &private, peer.as_ref())?;
        }

        #[test]
        fn x25519(private in any::<[u8; 32]>(), peer in x25519_peer()) {
            check(&ours::X25519, &X25519, &private, &peer)?;

            // Both encode the public key as the same SPKI, which ours parses.
            let theirs = PrivateKey::from_private_key(&X25519, &private).unwrap();
            let theirs_public = theirs.compute_public_key().unwrap();
            let spki = theirs_public.as_der().unwrap();
            let parsed = ours::PublicKey::from_spki(&ours::X25519, spki.as_ref()).unwrap();
            prop_assert_eq!(parsed.as_ref(), theirs_public.as_ref());
            let ours_spki = parsed.to_spki();
            prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());

            // Both keep the 32 bytes as given, unclamped.
            let theirs = PrivateKey::from_private_key(&X25519, &private).unwrap();
            let theirs = AsBigEndian::<Curve25519SeedBin<'_>>::as_be_bytes(&theirs).unwrap();
            let ours = ours::PrivateKey::from_scalar(&ours::X25519, &private)
                .unwrap()
                .to_scalar();
            prop_assert_eq!(ours.as_ref(), theirs.as_ref());
        }

        /// aws-lc-rs's agreement API has no X25519 PKCS#8, so this checks
        /// ours against aws-lc's `EVP` encoding of the same key, each way.
        #[test]
        fn x25519_pkcs8(private in any::<[u8; 32]>()) {
            let ours = ours::PrivateKey::from_scalar(&ours::X25519, &private).unwrap();
            let ours_pkcs8 = ours.to_pkcs8();
            let theirs_pkcs8 = aws_lc_x25519_pkcs8(&private);
            prop_assert_eq!(ours_pkcs8.as_ref(), &theirs_pkcs8[..]);
            let loaded = ours::PrivateKey::from_pkcs8(&ours::X25519, &theirs_pkcs8).unwrap();
            let (loaded, ours) = (loaded.public_key(), ours.public_key());
            prop_assert_eq!(loaded.as_ref(), ours.as_ref());
            prop_assert_eq!(aws_lc_x25519_from_pkcs8(ours_pkcs8.as_ref()), private);
        }
    }

    /// aws-lc's PKCS#8 encoding of the X25519 key `private`.
    fn aws_lc_x25519_pkcs8(private: &[u8; 32]) -> Vec<u8> {
        use aws_lc_sys::*;
        // SAFETY: each pointer and length describes a live buffer, and each
        // allocation is freed once, after its last use.
        unsafe {
            let key = EVP_PKEY_new_raw_private_key(
                EVP_PKEY_X25519,
                core::ptr::null_mut(),
                private.as_ptr(),
                private.len(),
            );
            assert!(!key.is_null());
            let mut cbb = core::mem::zeroed::<CBB>();
            assert_eq!(CBB_init(&mut cbb, 64), 1);
            assert_eq!(EVP_marshal_private_key(&mut cbb, key), 1);
            let (mut out, mut len) = (core::ptr::null_mut(), 0);
            assert_eq!(CBB_finish(&mut cbb, &mut out, &mut len), 1);
            let der = core::slice::from_raw_parts(out, len).to_vec();
            OPENSSL_free(out.cast());
            EVP_PKEY_free(key);
            der
        }
    }

    /// The X25519 key aws-lc parses from PKCS#8 `der`.
    pub(crate) fn aws_lc_x25519_from_pkcs8(der: &[u8]) -> [u8; 32] {
        use aws_lc_sys::*;
        // SAFETY: as `aws_lc_x25519_pkcs8`.
        unsafe {
            let mut cbs = core::mem::zeroed::<CBS>();
            CBS_init(&mut cbs, der.as_ptr(), der.len());
            let key = EVP_parse_private_key(&mut cbs);
            assert!(!key.is_null());
            assert_eq!(EVP_PKEY_id(key), EVP_PKEY_X25519);
            let mut private = [0u8; 32];
            let mut len = private.len();
            assert_eq!(
                EVP_PKEY_get_raw_private_key(key, private.as_mut_ptr(), &mut len),
                1
            );
            EVP_PKEY_free(key);
            assert_eq!(len, 32);
            private
        }
    }
}

/// ECDSA over a digest: aws-lc-rs verifies what rind signs over each curve,
/// hash, and encoding it has an algorithm for, and rind verifies what
/// aws-lc-rs signs over a digest, with an algorithm whose hash is not the
/// digest's, since the digest names its hash.
mod ecdsa_digest {
    use aws_lc_rs::digest as theirs_digest;
    use aws_lc_rs::rand::SystemRandom;
    use aws_lc_rs::signature::{self as theirs, KeyPair, UnparsedPublicKey};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::digest::{self, SHA256, SHA384, SHA512};
    use rind::ecdsa::{self, sign, verify};

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(8))]

        #[test]
        fn theirs_verify_ours(message in vec(any::<u8>(), 0..300)) {
            let cases: [(_, _, &'static theirs::EcdsaVerificationAlgorithm); 14] = [
                (&sign::P256_SHA256_ASN1, &SHA256, &theirs::ECDSA_P256_SHA256_ASN1),
                (&sign::P256_SHA256_ASN1, &SHA384, &theirs::ECDSA_P256_SHA384_ASN1),
                (&sign::P256_SHA256_ASN1, &SHA512, &theirs::ECDSA_P256_SHA512_ASN1),
                (&sign::P256_SHA256_FIXED, &SHA256, &theirs::ECDSA_P256_SHA256_FIXED),
                (&sign::P384_SHA384_ASN1, &SHA256, &theirs::ECDSA_P384_SHA256_ASN1),
                (&sign::P384_SHA384_ASN1, &SHA384, &theirs::ECDSA_P384_SHA384_ASN1),
                (&sign::P384_SHA384_ASN1, &SHA512, &theirs::ECDSA_P384_SHA512_ASN1),
                (&sign::P384_SHA384_FIXED, &SHA384, &theirs::ECDSA_P384_SHA384_FIXED),
                (&sign::P521_SHA512_ASN1, &SHA256, &theirs::ECDSA_P521_SHA256_ASN1),
                (&sign::P521_SHA512_ASN1, &SHA384, &theirs::ECDSA_P521_SHA384_ASN1),
                (&sign::P521_SHA512_ASN1, &SHA512, &theirs::ECDSA_P521_SHA512_ASN1),
                (&sign::P521_SHA512_FIXED, &SHA256, &theirs::ECDSA_P521_SHA256_FIXED),
                (&sign::P521_SHA512_FIXED, &SHA384, &theirs::ECDSA_P521_SHA384_FIXED),
                (&sign::P521_SHA512_FIXED, &SHA512, &theirs::ECDSA_P521_SHA512_FIXED),
            ];
            for (signing, hash, theirs) in cases {
                let ours = ecdsa::KeyPair::generate(signing).unwrap();
                let signature = ours.sign_digest(&digest::digest(hash, &message)).unwrap();
                let public_key = ours.public_key();
                let verifier = UnparsedPublicKey::new(theirs, public_key.as_ref());
                prop_assert!(
                    verifier.verify(&message, signature.as_ref()).is_ok(),
                    "{:?} {:?}", signing, hash
                );
                prop_assert!(verifier.verify(b"other", signature.as_ref()).is_err());
            }
        }

        #[test]
        fn ours_verify_theirs(message in vec(any::<u8>(), 0..300)) {
            let cases: [(&'static theirs::EcdsaSigningAlgorithm, _, _, _); 10] = [
                (&theirs::ECDSA_P256_SHA256_ASN1_SIGNING, &theirs_digest::SHA256, &SHA256, &verify::P256_SHA256_ASN1),
                (&theirs::ECDSA_P256_SHA256_FIXED_SIGNING, &theirs_digest::SHA256, &SHA256, &verify::P256_SHA256_FIXED),
                (&theirs::ECDSA_P384_SHA384_ASN1_SIGNING, &theirs_digest::SHA384, &SHA384, &verify::P384_SHA384_ASN1),
                (&theirs::ECDSA_P384_SHA384_FIXED_SIGNING, &theirs_digest::SHA384, &SHA384, &verify::P384_SHA384_FIXED),
                (&theirs::ECDSA_P521_SHA256_ASN1_SIGNING, &theirs_digest::SHA256, &SHA256, &verify::P521_SHA512_ASN1),
                (&theirs::ECDSA_P521_SHA256_FIXED_SIGNING, &theirs_digest::SHA256, &SHA256, &verify::P521_SHA512_FIXED),
                (&theirs::ECDSA_P521_SHA384_ASN1_SIGNING, &theirs_digest::SHA384, &SHA384, &verify::P521_SHA512_ASN1),
                (&theirs::ECDSA_P521_SHA384_FIXED_SIGNING, &theirs_digest::SHA384, &SHA384, &verify::P521_SHA512_FIXED),
                (&theirs::ECDSA_P521_SHA512_ASN1_SIGNING, &theirs_digest::SHA512, &SHA512, &verify::P521_SHA512_ASN1),
                (&theirs::ECDSA_P521_SHA512_FIXED_SIGNING, &theirs_digest::SHA512, &SHA512, &verify::P521_SHA512_FIXED),
            ];
            for (signing, theirs_hash, ours_hash, verification) in cases {
                let theirs = theirs::EcdsaKeyPair::generate(signing).unwrap();
                let signature = theirs
                    .sign_digest(&theirs_digest::digest(theirs_hash, &message))
                    .unwrap();
                // A signature over the message is one over its digest too.
                let over_message = theirs.sign(&SystemRandom::new(), &message).unwrap();
                let verifier =
                    ecdsa::PublicKey::new(verification, theirs.public_key().as_ref()).unwrap();
                let digest = digest::digest(ours_hash, &message);
                for signature in [signature.as_ref(), over_message.as_ref()] {
                    prop_assert!(
                        verifier.verify_digest(&digest, signature).is_ok(),
                        "{:?}", signing
                    );
                    let other = digest::digest(ours_hash, b"other");
                    prop_assert!(verifier.verify_digest(&other, signature).is_err());
                }
            }
        }
    }
}

/// HPKE against hpke-rs, as aws-lc-rs exposes none: rind-rustls's tests
/// compare its twelve suites with rustls's over aws-lc's primitives.
mod hpke {
    use hpke_rs::hpke_types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm};
    use hpke_rs::rustcrypto::HpkeRustCrypto;
    use hpke_rs::{Hpke, HpkePrivateKey, HpkePublicKey, Mode};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::hpke::*;

    // hpke-rs's RustCrypto backend has no P-521; RFC 9180's vectors cover it.
    const KEMS: [(&Kem, KemAlgorithm); 3] = [
        (&DHKEM_X25519_HKDF_SHA256, KemAlgorithm::DhKem25519),
        (&DHKEM_P256_HKDF_SHA256, KemAlgorithm::DhKemP256),
        (&DHKEM_P384_HKDF_SHA384, KemAlgorithm::DhKemP384),
    ];
    const KDFS: [(&Kdf, KdfAlgorithm); 3] = [
        (&HKDF_SHA256, KdfAlgorithm::HkdfSha256),
        (&HKDF_SHA384, KdfAlgorithm::HkdfSha384),
        (&HKDF_SHA512, KdfAlgorithm::HkdfSha512),
    ];
    // `None` is export-only.
    const AEADS: [(Option<&Aead>, AeadAlgorithm); 4] = [
        (Some(&AES_128_GCM), AeadAlgorithm::Aes128Gcm),
        (Some(&AES_256_GCM), AeadAlgorithm::Aes256Gcm),
        (Some(&CHACHA20_POLY1305), AeadAlgorithm::ChaCha20Poly1305),
        (None, AeadAlgorithm::HpkeExport),
    ];

    fn export(f: impl FnOnce(&mut [u8]) -> Result<(), rind::Error>, len: usize) -> Vec<u8> {
        let mut out = vec![0; len];
        f(&mut out).unwrap();
        out
    }

    proptest! {
        #[test]
        fn matches_hpke_rs(
            kem in 0..KEMS.len(),
            kdf in 0..KDFS.len(),
            aead in 0..AEADS.len(),
            ikm in vec(any::<u8>(), 0..80),
            info in vec(any::<u8>(), 0..64),
            aad in vec(any::<u8>(), 0..64),
            plaintext in vec(any::<u8>(), 0..300),
            context in vec(any::<u8>(), 0..64),
            len in 0..300usize,
        ) {
            let ((kem, their_kem), (kdf, their_kdf), (aead, their_aead)) = (KEMS[kem], KDFS[kdf], AEADS[aead]);
            let mut theirs = Hpke::<HpkeRustCrypto>::new(Mode::Base, their_kem, their_kdf, their_aead);

            // `DeriveKeyPair` gives the same key, which each side loads.
            let private_key = PrivateKey::derive(kem, &ikm).unwrap();
            let public_key = private_key.public_key();
            let (their_private, their_public) = theirs.derive_key_pair(&ikm).unwrap().into_keys();
            prop_assert_eq!(public_key.as_ref(), their_public.as_slice());
            let loaded = PrivateKey::from_scalar(kem, their_private.as_slice()).unwrap();
            let loaded = loaded.public_key();
            prop_assert_eq!(loaded.as_ref(), public_key.as_ref());
            let their_private = HpkePrivateKey::new(private_key.to_scalar().as_ref().to_vec());
            let their_public = HpkePublicKey::new(public_key.as_ref().to_vec());

            // Their sender to our recipient.
            let (enc, mut their_sender) = theirs
                .setup_sender(&their_public, &info, None, None, None)
                .unwrap();
            let their_export = their_sender.export(&context, len).unwrap();
            match aead {
                Some(aead) => {
                    let suite = Suite { kdf, aead };
                    let ct = their_sender.seal(&aad, &plaintext).unwrap();
                    let mut recipient = Recipient::new(suite, &private_key, &enc, &info).unwrap();
                    let mut in_out = ct.clone();
                    prop_assert_eq!(&*recipient.open_in_place(&aad, &mut in_out).unwrap(), &plaintext[..]);
                    prop_assert_eq!(export(|out| recipient.export(&context, out), len), their_export);
                }
                None => {
                    let recipient = Exporter::recipient(kdf, &private_key, &enc, &info).unwrap();
                    prop_assert_eq!(export(|out| recipient.export(&context, out), len), their_export);
                }
            }

            // Our sender to their recipient.
            let (enc, our_export, ct) = match aead {
                Some(aead) => {
                    let (enc, mut sender) = Sender::new(Suite { kdf, aead }, public_key, &info).unwrap();
                    let mut ct = plaintext.clone();
                    sender.seal_in_place_append_tag(&aad, &mut ct).unwrap();
                    (enc, export(|out| sender.export(&context, out), len), Some(ct))
                }
                None => {
                    let (enc, sender) = Exporter::sender(kdf, public_key, &info).unwrap();
                    (enc, export(|out| sender.export(&context, out), len), None)
                }
            };
            let mut their_recipient = theirs
                .setup_receiver(enc.as_ref(), &their_private, &info, None, None, None)
                .unwrap();
            prop_assert_eq!(their_recipient.export(&context, len).unwrap(), our_export);
            if let Some(ct) = ct {
                prop_assert_eq!(their_recipient.open(&aad, &ct).unwrap(), plaintext);
            }
        }
    }
}

/// ML-DSA against aws-lc-rs, which runs mldsa-native with the same
/// s2n-bignum kernels.
macro_rules! ml_dsa_crosschecks {
    ($set:ident, $signing:ident, $verify:ident) => {
        use aws_lc_rs::encoding::{AsDer, AsRawBytes};
        use aws_lc_rs::signature::{KeyPair, PqdsaKeyPair, UnparsedPublicKey, $signing};
        use proptest::collection::vec;
        use proptest::prelude::*;
        use proptest::sample::Index;
        use rind::ml_dsa::{KeyPair as MlDsaKeyPair, PublicKey, $set};

        // Each case makes several signatures, which are slow in a debug
        // build and under emulation.
        proptest! {
            #![proptest_config(ProptestConfig::with_cases(16))]

            #[test]
            fn sign_verify(
                seed in any::<[u8; 32]>(),
                message in vec(any::<u8>(), 0..300),
                flip in any::<Option<Index>>(),
            ) {
                // One seed gives both sides the same key and encodings.
                let theirs = PqdsaKeyPair::from_seed(&$signing, &seed).unwrap();
                let ours = MlDsaKeyPair::<$set>::from_seed(&seed).unwrap();
                let public = theirs.public_key().as_ref();
                let ours_public = ours.public_key();
                prop_assert_eq!(ours_public.as_ref(), public);
                let spki = theirs.public_key().as_der().unwrap();
                let ours_spki = ours_public.to_spki();
                prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());
                let (ours_pkcs8, theirs_pkcs8) = (ours.to_pkcs8(), theirs.to_pkcs8v1().unwrap());
                prop_assert_eq!(ours_pkcs8.as_ref(), theirs_pkcs8.as_ref());

                // Signing is hedged, so each verifies the other's signature
                // rather than matching its bytes.
                let ours_signature = ours.sign(&message).unwrap();
                UnparsedPublicKey::new(&aws_lc_rs::signature::$verify, public)
                    .verify(&message, ours_signature.as_ref())
                    .unwrap();
                let mut signature = vec![0; $signing.signature_len()];
                theirs.sign(&message, &mut signature).unwrap();
                let verifier = PublicKey::<$set>::from_spki(spki.as_ref()).unwrap();
                verifier.verify(&message, &signature).unwrap();

                // Both refuse it with any one bit flipped.
                if let Some(flip) = flip {
                    let bit = flip.index(signature.len() * 8);
                    signature[bit / 8] ^= 1 << (bit % 8);
                    prop_assert!(verifier.verify(&message, &signature).is_err());
                    prop_assert!(
                        UnparsedPublicKey::new(&aws_lc_rs::signature::$verify, public)
                            .verify(&message, &signature)
                            .is_err()
                    );
                }
            }

            /// Both load the other's expanded key, which has no seed, and
            /// sign alike with it.
            #[test]
            fn expanded(seed in any::<[u8; 32]>(), message in vec(any::<u8>(), 0..300)) {
                let theirs = PqdsaKeyPair::from_seed(&$signing, &seed).unwrap();
                let expanded = theirs.private_key().as_raw_bytes().unwrap();
                let expanded = expanded.as_ref();
                let ours = MlDsaKeyPair::<$set>::from_pkcs8(&expanded_pkcs8(
                    theirs_pkcs8_prefix(&theirs),
                    expanded,
                ))
                .unwrap();
                prop_assert!(ours.to_seed().is_none());
                let ours_public = ours.public_key();
                prop_assert_eq!(ours_public.as_ref(), theirs.public_key().as_ref());

                // Ours writes the expanded form, which theirs loads.
                let ours_pkcs8 = ours.to_pkcs8();
                let reloaded = PqdsaKeyPair::from_pkcs8(&$signing, ours_pkcs8.as_ref()).unwrap();
                prop_assert_eq!(reloaded.public_key().as_ref(), theirs.public_key().as_ref());
                let signature = ours.sign(&message).unwrap();
                UnparsedPublicKey::new(&aws_lc_rs::signature::$verify, theirs.public_key().as_ref())
                    .verify(&message, signature.as_ref())
                    .unwrap();
            }
        }

        /// The PKCS#8 v1 header up to the private key, from the seed form
        /// aws-lc writes: version and algorithm identifier.
        fn theirs_pkcs8_prefix(theirs: &PqdsaKeyPair) -> Vec<u8> {
            let pkcs8 = theirs.to_pkcs8v1().unwrap();
            // SEQUENCE { INTEGER 0, AlgorithmIdentifier (13 bytes), ... }
            pkcs8.as_ref()[2..2 + 3 + 13].to_vec()
        }

        /// A PKCS#8 v1 key in RFC 9881's expanded form.
        fn expanded_pkcs8(prefix: Vec<u8>, expanded: &[u8]) -> Vec<u8> {
            let inner = super::der(0x04, expanded);
            let body = [prefix, super::der(0x04, &inner)].concat();
            super::der(0x30, &body)
        }
    };
}

mod ml_dsa_44 {
    ml_dsa_crosschecks!(MlDsa44, ML_DSA_44_SIGNING, ML_DSA_44);
}

mod ml_dsa_65 {
    ml_dsa_crosschecks!(MlDsa65, ML_DSA_65_SIGNING, ML_DSA_65);
}

mod ml_dsa_87 {
    ml_dsa_crosschecks!(MlDsa87, ML_DSA_87_SIGNING, ML_DSA_87);
}

// aws-lc-rs has no SLH-DSA, so RustCrypto's and integritychain's `fips205`
// stand in for it. Signing is randomized, so each verifies the others'
// signatures rather than matching their bytes; the ACVP vectors match bytes.
macro_rules! slh_dsa_crosschecks {
    ($set:ident, $rustcrypto:ident, $fips205:ident, $n:literal) => {
        use fips205::traits::{KeyGen, SerDes, Signer as _, Verifier as _};
        use pkcs8::{EncodePrivateKey, EncodePublicKey};
        use proptest::collection::vec;
        use proptest::prelude::*;
        use proptest::sample::Index;
        use rind::slh_dsa::{KeyPair, PublicKey, $set};
        use slh_dsa::signature::Verifier;

        type Theirs = slh_dsa::SigningKey<slh_dsa::$rustcrypto>;

        // RustCrypto's is generic, so it compiles into this test at the
        // test's own optimisation level, and unoptimised it signs for
        // minutes. The release run, which every tier makes, takes these.
        proptest! {
            #![proptest_config(ProptestConfig::with_cases(4))]

            #[test]
            #[cfg_attr(debug_assertions, ignore = "RustCrypto signs for minutes unoptimised")]
            fn sign_verify(
                seeds in any::<[[u8; $n]; 3]>(),
                addrnd in any::<[u8; $n]>(),
                message in vec(any::<u8>(), 0..300),
                flip in any::<Option<Index>>(),
            ) {
                // The same seeds give all three the same key and encodings.
                let [sk_seed, sk_prf, pk_seed] = seeds;
                let theirs = Theirs::slh_keygen_internal(&sk_seed, &sk_prf, &pk_seed);
                let (fips_public, fips_private) =
                    fips205::$fips205::KG::keygen_from_seed(&sk_seed, &sk_prf, &pk_seed);
                prop_assert_eq!(
                    &fips_private.clone().into_bytes()[..],
                    &theirs.to_bytes()[..]
                );
                let pkcs8 = theirs.to_pkcs8_der().unwrap();
                let ours = KeyPair::<$set>::from_pkcs8(pkcs8.as_bytes()).unwrap();
                let ours_pkcs8 = ours.to_pkcs8();
                prop_assert_eq!(ours_pkcs8.as_ref(), pkcs8.as_bytes());
                let spki = theirs.as_ref().to_public_key_der().unwrap();
                let ours_spki = ours.public_key().to_spki();
                prop_assert_eq!(ours_spki.as_ref(), spki.as_bytes());

                // Each verifies the others' signatures.
                let ours_signature = ours.sign(&message).unwrap();
                let parsed = slh_dsa::Signature::try_from(ours_signature.as_ref()).unwrap();
                theirs.as_ref().verify(&message, &parsed).unwrap();
                prop_assert!(fips_public.verify(
                    &message,
                    ours_signature.as_ref().try_into().unwrap(),
                    b""
                ));
                let verifier = PublicKey::<$set>::from_spki(spki.as_bytes()).unwrap();
                let mut signature = theirs
                    .try_sign_with_context(&message, b"", Some(&addrnd))
                    .unwrap()
                    .to_vec();
                verifier.verify(&message, &signature).unwrap();
                let fips_signature = fips_private.try_sign(&message, b"", true).unwrap();
                verifier.verify(&message, &fips_signature).unwrap();

                // All refuse it with any one bit flipped.
                if let Some(flip) = flip {
                    let bit = flip.index(signature.len() * 8);
                    signature[bit / 8] ^= 1 << (bit % 8);
                    prop_assert!(verifier.verify(&message, &signature).is_err());
                    let parsed = slh_dsa::Signature::try_from(signature.as_slice()).unwrap();
                    prop_assert!(theirs.as_ref().verify(&message, &parsed).is_err());
                    prop_assert!(!fips_public.verify(
                        &message,
                        signature.as_slice().try_into().unwrap(),
                        b""
                    ));
                }
            }
        }
    };
}

mod slh_dsa_sha2_128s {
    slh_dsa_crosschecks!(SlhDsaSha2_128s, Sha2_128s, slh_dsa_sha2_128s, 16);
}

mod slh_dsa_sha2_128f {
    slh_dsa_crosschecks!(SlhDsaSha2_128f, Sha2_128f, slh_dsa_sha2_128f, 16);
}

mod slh_dsa_sha2_192s {
    slh_dsa_crosschecks!(SlhDsaSha2_192s, Sha2_192s, slh_dsa_sha2_192s, 24);
}

mod slh_dsa_sha2_192f {
    slh_dsa_crosschecks!(SlhDsaSha2_192f, Sha2_192f, slh_dsa_sha2_192f, 24);
}

mod slh_dsa_sha2_256s {
    slh_dsa_crosschecks!(SlhDsaSha2_256s, Sha2_256s, slh_dsa_sha2_256s, 32);
}

mod slh_dsa_sha2_256f {
    slh_dsa_crosschecks!(SlhDsaSha2_256f, Sha2_256f, slh_dsa_sha2_256f, 32);
}

mod slh_dsa_shake_128s {
    slh_dsa_crosschecks!(SlhDsaShake128s, Shake128s, slh_dsa_shake_128s, 16);
}

mod slh_dsa_shake_128f {
    slh_dsa_crosschecks!(SlhDsaShake128f, Shake128f, slh_dsa_shake_128f, 16);
}

mod slh_dsa_shake_192s {
    slh_dsa_crosschecks!(SlhDsaShake192s, Shake192s, slh_dsa_shake_192s, 24);
}

mod slh_dsa_shake_192f {
    slh_dsa_crosschecks!(SlhDsaShake192f, Shake192f, slh_dsa_shake_192f, 24);
}

mod slh_dsa_shake_256s {
    slh_dsa_crosschecks!(SlhDsaShake256s, Shake256s, slh_dsa_shake_256s, 32);
}

mod slh_dsa_shake_256f {
    slh_dsa_crosschecks!(SlhDsaShake256f, Shake256f, slh_dsa_shake_256f, 32);
}

/// Each side of RFC 9474's protocol against blind-rsa-signatures' other
/// side, for each variant.
mod blind_rsa {
    use blind_rsa_signatures::{
        DefaultRng, Deterministic, MessagePrepare, MessageRandomizer, PSS, PSSZero, Randomized,
        SaltMode, SecretKey, Sha384,
    };
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::blind_rsa::*;

    // Their keys are 2048 to 4096 bits.
    const KEYS: [&[u8]; 2] = [
        include_bytes!("../src/high/rsa/rsa2048.pkcs8.der"),
        include_bytes!("../src/high/rsa/rsa4096.pkcs8.der"),
    ];

    fn check<S: SaltMode, M: MessagePrepare>(algorithm: &'static Algorithm, message: &[u8]) {
        for der in KEYS {
            let ours = KeyPair::from_pkcs8(algorithm, der).unwrap();
            let theirs = SecretKey::<Sha384, S, M>::from_der(der).unwrap();
            let our_public = ours.public_key();
            let their_public = theirs.public_key().unwrap();
            let spki = their_public.to_spki().unwrap();
            assert_eq!(our_public.to_spki().as_ref(), spki);
            PublicKey::from_spki(algorithm, &spki).unwrap();

            // Our client, their server.
            let (blinded, blinding) = our_public.blind(message).unwrap();
            let blind_signature = theirs.blind_sign(blinded.as_ref()).unwrap();
            let signature = blinding.finalize(&blind_signature).unwrap();
            let (prefix, rsa_signature) = signature.as_ref().split_at(match M::RANDOMIZE {
                true => 32,
                false => 0,
            });
            let randomizer = M::RANDOMIZE.then(|| MessageRandomizer(prefix.try_into().unwrap()));
            their_public
                .verify(&rsa_signature.to_vec().into(), randomizer, message)
                .unwrap();

            // Their client, our server.
            let result = their_public.blind(&mut DefaultRng, message).unwrap();
            let blind_signature = ours.blind_sign(&result.blind_message).unwrap();
            let blind_signature = blind_signature.as_ref().to_vec().into();
            let signature = their_public
                .finalize(&blind_signature, &result, message)
                .unwrap();
            let prefix = result.msg_randomizer.as_ref().map_or(&[][..], |r| &r.0[..]);
            our_public
                .verify(message, &[prefix, &signature].concat())
                .unwrap();
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(16))]

        #[test]
        fn matches_blind_rsa_signatures(message in vec(any::<u8>(), 0..300)) {
            check::<PSS, Randomized>(&RSABSSA_SHA384_PSS_RANDOMIZED, &message);
            check::<PSSZero, Randomized>(&RSABSSA_SHA384_PSSZERO_RANDOMIZED, &message);
            check::<PSS, Deterministic>(&RSABSSA_SHA384_PSS_DETERMINISTIC, &message);
            check::<PSSZero, Deterministic>(&RSABSSA_SHA384_PSSZERO_DETERMINISTIC, &message);
        }
    }
}

/// ECVRF against `akd_core`'s Edwards25519 suite, which key transparency's
/// `akd` runs, and `vrf-rfc9381`'s P-256 suite: each proves the same bytes
/// for a key and input, and verifies the other's proofs.
mod vrf {
    use akd_core::ecvrf::{VRFPrivateKey, VRFPublicKey};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::vrf::*;
    use vrf_rfc9381::ec::p256::EcVrfProof;
    use vrf_rfc9381::ec::p256::tai::{EcVrfP256TaiPublicKey, EcVrfP256TaiSecretKey};
    use vrf_rfc9381::{Proof as _, Prover as _, Verifier as _};

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        #[test]
        fn matches_akd(seed in any::<[u8; 32]>(), alpha in vec(any::<u8>(), 0..300)) {
            let ours = KeyPair::from_seed(&ECVRF_EDWARDS25519_SHA512_TAI, &seed).unwrap();
            let theirs = VRFPrivateKey::try_from(&seed[..]).unwrap();
            let their_public = VRFPublicKey::from(&theirs);
            prop_assert_eq!(ours.public_key().as_ref(), their_public.as_bytes());

            let (proof, output) = ours.prove(&alpha).unwrap();
            let their_proof = theirs.prove(&alpha);
            prop_assert_eq!(proof.as_ref(), their_proof.to_bytes());
            their_public.verify(&their_proof, &alpha).unwrap();

            let public_key =
                PublicKey::new(&ECVRF_EDWARDS25519_SHA512_TAI, their_public.as_bytes()).unwrap();
            let verified = public_key.verify(&alpha, &their_proof.to_bytes()).unwrap();
            prop_assert_eq!(verified.as_ref(), output.as_ref());
        }

        #[test]
        fn matches_vrf_rfc9381(alpha in vec(any::<u8>(), 0..300)) {
            let ours = KeyPair::generate(&ECVRF_P256_SHA256_TAI).unwrap();
            let theirs = EcVrfP256TaiSecretKey::from_slice(ours.to_seed().as_ref()).unwrap();
            let their_public = theirs.verifier();

            let (proof, output) = ours.prove(&alpha).unwrap();
            let their_proof = theirs.prove(&alpha).unwrap();
            prop_assert_eq!(proof.as_ref(), &their_proof.encode_to_pi()[..]);
            prop_assert!(
                EcVrfP256TaiPublicKey::from_slice(ours.public_key().as_ref()).unwrap()
                    == their_public
            );
            let their_output = their_public
                .verify(&alpha, EcVrfProof::decode_pi(proof.as_ref()).unwrap())
                .unwrap();
            prop_assert_eq!(&their_output[..], output.as_ref());

            let verified = ours
                .public_key()
                .verify(&alpha, &their_proof.encode_to_pi())
                .unwrap();
            prop_assert_eq!(verified.as_ref(), output.as_ref());
        }
    }
}

mod oprf {
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rand_core_voprf::OsRng;
    use rind::oprf::voprf as rind_voprf;
    use rind::oprf::{P256_SHA256, P384_SHA384, P521_SHA512, RISTRETTO255_SHA512};
    use voprf::{
        BlindedElement, EvaluationElement, Group, OprfClient, OprfServer, Proof, VoprfClient,
        VoprfServer,
    };

    /// Each suite against the `voprf` crate: the same key from one seed,
    /// rind's clients finalizing the crate's evaluations and proofs, the
    /// crate's clients finalizing rind's, and both servers' direct outputs.
    macro_rules! matches_voprf {
        ($cs:ty, $suite:expr, $seed:expr, $info:expr, $inputs:expr) => {{
            let (seed, info, inputs): ([u8; 32], Vec<u8>, Vec<Vec<u8>>) = ($seed, $info, $inputs);
            type G = <$cs as voprf::CipherSuite>::Group;
            let suite = $suite;

            // The OPRF mode.
            let ours = rind::oprf::ServerKey::derive(suite, &seed, &info).unwrap();
            let theirs = OprfServer::<$cs>::new_from_seed(&seed, &info).unwrap();
            // The crate derives the same key: loaded from rind's
            // encoding, it evaluates as the key it derived.
            let loaded = OprfServer::<$cs>::new_with_key(ours.to_scalar().as_ref()).unwrap();
            prop_assert_eq!(
                &loaded.evaluate(b"key").unwrap()[..],
                &theirs.evaluate(b"key").unwrap()[..]
            );
            for input in &inputs {
                let direct = theirs.evaluate(input).unwrap();
                let output = ours.evaluate(input).unwrap();
                prop_assert_eq!(output.as_ref(), &direct[..]);

                let (blind, blinded) = rind::oprf::Blind::new(suite, input).unwrap();
                let evaluated =
                    theirs.blind_evaluate(&BlindedElement::deserialize(blinded.as_ref()).unwrap());
                let output = blind.finalize(&evaluated.serialize()).unwrap();
                prop_assert_eq!(output.as_ref(), &direct[..]);

                let blinded = OprfClient::<$cs>::blind(input, &mut OsRng).unwrap();
                let evaluated = ours.blind_evaluate(&blinded.message.serialize()).unwrap();
                let output = blinded
                    .state
                    .finalize(
                        input,
                        &EvaluationElement::deserialize(evaluated.as_ref()).unwrap(),
                    )
                    .unwrap();
                prop_assert_eq!(&output[..], &direct[..]);
            }

            // The VOPRF mode, batched.
            let ours = rind_voprf::ServerKey::derive(suite, &seed, &info).unwrap();
            let theirs = VoprfServer::<$cs>::new_from_seed(&seed, &info).unwrap();
            prop_assert_eq!(
                ours.public_key().as_ref(),
                &G::serialize_elem(theirs.get_public_key())[..]
            );
            let direct = inputs
                .iter()
                .map(|input| theirs.evaluate(input).unwrap().to_vec())
                .collect::<Vec<_>>();
            for (input, direct) in inputs.iter().zip(&direct) {
                let output = ours.evaluate(input).unwrap();
                prop_assert_eq!(output.as_ref(), &direct[..]);
            }

            let mut blinds = Vec::new();
            let mut blinded = Vec::new();
            for input in &inputs {
                let (blind, element) = rind_voprf::Blind::new(suite, input).unwrap();
                blinds.push(blind);
                blinded.push(BlindedElement::<$cs>::deserialize(element.as_ref()).unwrap());
            }
            let evaluated = theirs.batch_blind_evaluate(&mut OsRng, &blinded).unwrap();
            let messages = evaluated
                .messages
                .iter()
                .flat_map(|message| message.serialize())
                .collect::<Vec<_>>();
            let public_key =
                rind_voprf::PublicKey::new(suite, &G::serialize_elem(theirs.get_public_key()))
                    .unwrap();
            let outputs = rind_voprf::Blind::finalize_batch(
                blinds,
                &messages,
                &evaluated.proof.serialize(),
                &public_key,
            )
            .unwrap();
            for (output, direct) in outputs.iter().zip(&direct) {
                prop_assert_eq!(output.as_ref(), &direct[..]);
            }

            let mut clients = Vec::new();
            let mut blinded = Vec::new();
            for input in &inputs {
                let result = VoprfClient::<$cs>::blind(input, &mut OsRng).unwrap();
                clients.push(result.state);
                blinded.extend_from_slice(&result.message.serialize());
            }
            let (evaluated, proof) = ours.blind_evaluate(&blinded).unwrap();
            let element_len = evaluated.as_ref().len() / inputs.len();
            let messages = evaluated
                .as_ref()
                .chunks(element_len)
                .map(|bytes| EvaluationElement::<$cs>::deserialize(bytes).unwrap())
                .collect::<Vec<_>>();
            let proof = Proof::<$cs>::deserialize(proof.as_ref()).unwrap();
            let outputs = VoprfClient::batch_finalize(
                &inputs,
                &clients,
                &messages,
                &proof,
                theirs.get_public_key(),
            )
            .unwrap();
            for (output, direct) in outputs.zip(&direct) {
                prop_assert_eq!(&output.unwrap()[..], &direct[..]);
            }
        }};
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(16))]

        #[test]
        fn ristretto255_matches_voprf(
            seed in any::<[u8; 32]>(),
            info in vec(any::<u8>(), 0..40),
            inputs in vec(vec(any::<u8>(), 0..100), 1..4),
        ) {
            matches_voprf!(voprf::Ristretto255, &RISTRETTO255_SHA512, seed, info, inputs);
        }

        #[test]
        fn p256_matches_voprf(
            seed in any::<[u8; 32]>(),
            info in vec(any::<u8>(), 0..40),
            inputs in vec(vec(any::<u8>(), 0..100), 1..4),
        ) {
            matches_voprf!(p256_voprf::NistP256, &P256_SHA256, seed, info, inputs);
        }

        #[test]
        fn p384_matches_voprf(
            seed in any::<[u8; 32]>(),
            info in vec(any::<u8>(), 0..40),
            inputs in vec(vec(any::<u8>(), 0..100), 1..4),
        ) {
            matches_voprf!(p384_voprf::NistP384, &P384_SHA384, seed, info, inputs);
        }

        #[test]
        fn p521_matches_voprf(
            seed in any::<[u8; 32]>(),
            info in vec(any::<u8>(), 0..40),
            inputs in vec(vec(any::<u8>(), 0..100), 1..4),
        ) {
            matches_voprf!(p521_voprf::NistP521, &P521_SHA512, seed, info, inputs);
        }
    }
}

/// FROST against the Zcash Foundation's `frost-*` crates, as aws-lc-rs has
/// no FROST.
mod frost {
    use std::collections::{BTreeMap, BTreeSet};

    use rand_core_voprf::OsRng;
    use rind::frost::*;

    /// Every suite's identifiers and scalars are 32 bytes.
    const SCALAR_LEN: usize = 32;

    macro_rules! differential {
        ($frost:ident, $suite:expr) => {
            use $frost::keys::{
                IdentifierList, KeyPackage, PublicKeyPackage, SecretShare,
                SigningShare as FrostShare, VerifiableSecretSharingCommitment,
                generate_with_dealer,
            };
            use $frost::round1::{NonceCommitment, SigningCommitments};
            use $frost::{Identifier as FrostId, SigningPackage as FrostPackage, round1, round2};

            const SUITE: &Suite = $suite;

            fn commitments_of(c: &SigningCommitments, id: &FrostId) -> Commitments {
                let bytes = [
                    id.serialize(),
                    c.hiding().serialize().unwrap(),
                    c.binding().serialize().unwrap(),
                ]
                .concat();
                Commitments::new(SUITE, &bytes).unwrap()
            }

            fn frost_commitments(c: &Commitments) -> (FrostId, SigningCommitments) {
                let len = (c.as_ref().len() - SCALAR_LEN) / 2;
                let (id, rest) = c.as_ref().split_at(SCALAR_LEN);
                (
                    FrostId::deserialize(id).unwrap(),
                    SigningCommitments::new(
                        NonceCommitment::deserialize(&rest[..len]).unwrap(),
                        NonceCommitment::deserialize(&rest[len..]).unwrap(),
                    ),
                )
            }

            /// The reference's dealer, and signers split between rind and
            /// the reference: each side's coordinator reaches the same
            /// signature, and each verifies it.
            #[test]
            fn reference_dealer_mixed_signers() {
                for message in [&b""[..], b"message", &[0xa5; 1000]] {
                    let (secret_shares, pubkeys) =
                        generate_with_dealer(5, 3, IdentifierList::Default, &mut OsRng).unwrap();
                    let vss = secret_shares
                        .values()
                        .next()
                        .unwrap()
                        .commitment()
                        .serialize_whole()
                        .unwrap();
                    let commitment = VssCommitment::new(SUITE, &vss).unwrap();
                    assert_eq!(
                        commitment.public_key().as_ref(),
                        pubkeys.verifying_key().serialize().unwrap()
                    );

                    // Participants 1 and 4 run rind; 3 runs the reference.
                    let mut ours = BTreeMap::new();
                    for n in [1u16, 4] {
                        let id = FrostId::try_from(n).unwrap();
                        let share = &secret_shares[&id];
                        let identifier = Identifier::new(SUITE, &id.serialize()).unwrap();
                        let share = rind::frost::SigningShare::from_scalar(
                            &identifier,
                            &share.signing_share().serialize(),
                            &commitment,
                        )
                        .unwrap();
                        ours.insert(id, share);
                    }
                    let theirs_id = FrostId::try_from(3u16).unwrap();
                    let theirs = KeyPackage::try_from(secret_shares[&theirs_id].clone()).unwrap();

                    let mut our_nonces = BTreeMap::new();
                    let mut commitments = Vec::new();
                    for (id, share) in &ours {
                        let (n, c) = SigningNonces::commit(share).unwrap();
                        our_nonces.insert(*id, n);
                        commitments.push(c);
                    }
                    let (their_nonces, their_commitments) =
                        round1::commit(theirs.signing_share(), &mut OsRng);
                    commitments.push(commitments_of(&their_commitments, &theirs_id));

                    let package =
                        SigningPackage::new(commitment.public_key(), &commitments, message)
                            .unwrap();
                    let frost_package = FrostPackage::new(
                        commitments.iter().map(frost_commitments).collect(),
                        message,
                    );

                    let mut shares = Vec::new();
                    let mut frost_shares = BTreeMap::new();
                    for (id, n) in our_nonces {
                        let share = n.sign(&ours[&id], &package).unwrap();
                        frost_shares.insert(
                            id,
                            round2::SignatureShare::deserialize(&share.as_ref()[SCALAR_LEN..])
                                .unwrap(),
                        );
                        shares.push(share);
                    }
                    let their_share = round2::sign(&frost_package, &their_nonces, &theirs).unwrap();
                    let bytes = [theirs_id.serialize(), their_share.serialize()].concat();
                    shares.push(SignatureShare::new(SUITE, &bytes).unwrap());
                    frost_shares.insert(theirs_id, their_share);

                    for share in &shares {
                        package.verify_share(share, &commitment).unwrap();
                    }
                    let signature = package.aggregate(&shares).unwrap();
                    let frost_signature =
                        $frost::aggregate(&frost_package, &frost_shares, &pubkeys).unwrap();
                    assert_eq!(signature.as_ref(), frost_signature.serialize().unwrap());
                    commitment
                        .public_key()
                        .verify(message, signature.as_ref())
                        .unwrap();
                    pubkeys
                        .verifying_key()
                        .verify(message, &frost_signature)
                        .unwrap();
                }
            }

            /// rind's dealer, whose shares and commitment the reference
            /// loads and signs with, and whose signature rind verifies.
            #[test]
            fn rind_dealer_reference_signers() {
                let (shares, commitment) = deal(SUITE, 3, 4).unwrap();
                let frost_commitment =
                    VerifiableSecretSharingCommitment::deserialize_whole(commitment.as_ref())
                        .unwrap();
                let ids: BTreeSet<FrostId> = shares
                    .iter()
                    .map(|s| FrostId::deserialize(s.identifier().as_ref()).unwrap())
                    .collect();
                let pubkeys = PublicKeyPackage::from_commitment(&ids, &frost_commitment).unwrap();
                assert_eq!(
                    pubkeys.verifying_key().serialize().unwrap(),
                    commitment.public_key().as_ref()
                );

                let key_packages: BTreeMap<FrostId, KeyPackage> = shares[1..]
                    .iter()
                    .map(|s| {
                        let id = FrostId::deserialize(s.identifier().as_ref()).unwrap();
                        let share = FrostShare::deserialize(s.to_scalar().as_ref()).unwrap();
                        let secret = SecretShare::new(id, share, frost_commitment.clone());
                        (id, KeyPackage::try_from(secret).unwrap())
                    })
                    .collect();
                let mut nonces = BTreeMap::new();
                let mut frost_commitments = BTreeMap::new();
                for (id, key_package) in &key_packages {
                    let (n, c) = round1::commit(key_package.signing_share(), &mut OsRng);
                    nonces.insert(*id, n);
                    frost_commitments.insert(*id, c);
                }
                let frost_package = FrostPackage::new(frost_commitments.clone(), b"message");
                let commitments: Vec<_> = frost_commitments
                    .iter()
                    .map(|(id, c)| commitments_of(c, id))
                    .collect();
                let package =
                    SigningPackage::new(commitment.public_key(), &commitments, b"message").unwrap();
                let signature_shares: Vec<_> = key_packages
                    .iter()
                    .map(|(id, key_package)| {
                        let share = round2::sign(&frost_package, &nonces[id], key_package).unwrap();
                        let bytes = [id.serialize(), share.serialize()].concat();
                        SignatureShare::new(SUITE, &bytes).unwrap()
                    })
                    .collect();
                for share in &signature_shares {
                    package.verify_share(share, &commitment).unwrap();
                }
                let signature = package.aggregate(&signature_shares).unwrap();
                commitment
                    .public_key()
                    .verify(b"message", signature.as_ref())
                    .unwrap();
                let frost_signature = $frost::Signature::deserialize(signature.as_ref()).unwrap();
                pubkeys
                    .verifying_key()
                    .verify(b"message", &frost_signature)
                    .unwrap();
            }
        };
    }

    mod ed25519 {
        use super::*;
        differential!(frost_ed25519, &ED25519_SHA512);
    }

    mod ristretto255 {
        use super::*;
        differential!(frost_ristretto255, &RISTRETTO255_SHA512);
    }

    mod p256 {
        use super::*;
        differential!(frost_p256, &P256_SHA256);
    }
}

/// Oracles that share no code with rind's path, besides aws-lc-rs: RustCrypto's
/// crates, and dalek's on the tiers where rind runs s2n-bignum. Each test
/// runs the same inputs through rind and the oracle and demands equal
/// answers, so a routine aws-lc-rs and rind both take from s2n-bignum,
/// mlkem-native, or mldsa-native is checked against a third implementation.
mod independent {
    use proptest::collection::vec;
    use proptest::prelude::*;
    use proptest::sample::Index;

    proptest! {
        #[test]
        fn sha2_sha3_hmac(
            message in vec(any::<u8>(), 0..1100),
            key in vec(any::<u8>(), 0..300),
            split in any::<Index>(),
        ) {
            use hmac::{KeyInit, Mac};
            use sha2::Digest as _;

            let split = split.index(message.len() + 1);
            let digest = |algorithm| {
                let mut ctx = rind::digest::Context::new(algorithm);
                ctx.update(&message[..split]);
                ctx.update(&message[split..]);
                ctx.finish()
            };
            { let (got, wanted) = (digest(&rind::digest::SHA256), sha2::Sha256::digest(&message)); prop_assert_eq!(got.as_ref(), &wanted[..]); }
            { let (got, wanted) = (digest(&rind::digest::SHA384), sha2::Sha384::digest(&message)); prop_assert_eq!(got.as_ref(), &wanted[..]); }
            { let (got, wanted) = (digest(&rind::digest::SHA512), sha2::Sha512::digest(&message)); prop_assert_eq!(got.as_ref(), &wanted[..]); }
            { let (got, wanted) = (digest(&rind::digest::SHA512_256), sha2::Sha512_256::digest(&message)); prop_assert_eq!(got.as_ref(), &wanted[..]); }
            { let (got, wanted) = (digest(&rind::digest::SHA3_256), sha3::Sha3_256::digest(&message)); prop_assert_eq!(got.as_ref(), &wanted[..]); }
            { let (got, wanted) = (digest(&rind::digest::SHA3_384), sha3::Sha3_384::digest(&message)); prop_assert_eq!(got.as_ref(), &wanted[..]); }
            { let (got, wanted) = (digest(&rind::digest::SHA3_512), sha3::Sha3_512::digest(&message)); prop_assert_eq!(got.as_ref(), &wanted[..]); }

            macro_rules! mac {
                ($ours:expr, $theirs:ty) => {{
                    let ours = rind::hmac::Key::new($ours, &key);
                    let wanted = {
                        let mut mac = <hmac::Hmac<$theirs> as KeyInit>::new_from_slice(&key).unwrap();
                        mac.update(&message);
                        mac.finalize().into_bytes()
                    };
                    let got = rind::hmac::sign(&ours, &message);
                    prop_assert_eq!(got.as_ref(), &wanted[..]);
                }};
            }
            mac!(&rind::hmac::HMAC_SHA256, sha2::Sha256);
            mac!(&rind::hmac::HMAC_SHA384, sha2::Sha384);
            mac!(&rind::hmac::HMAC_SHA512, sha2::Sha512);
        }

        #[test]
        fn aead(
            key in any::<[u8; 32]>(),
            nonce in any::<[u8; 12]>(),
            aad in vec(any::<u8>(), 0..100),
            msg in vec(any::<u8>(), 0..1100),
            flip in any::<Option<Index>>(),
        ) {
            use aes_gcm::aead::{AeadInOut, KeyInit};

            // Seals with the oracle, opens with rind, and the other way
            // round, with one bit of the sealed message flipped for `flip`.
            macro_rules! check {
                ($ours:expr, $theirs:ty, $key:expr) => {{
                    let theirs = <$theirs>::new_from_slice($key).unwrap();
                    let mut sealed = msg.clone();
                    let tag = theirs
                        .encrypt_inout_detached(&nonce.into(), &aad, sealed.as_mut_slice().into())
                        .unwrap();
                    sealed.extend_from_slice(&tag);

                    let ours = rind::aead::Key::new($ours, $key).unwrap();
                    let mut mine = msg.clone();
                    ours.seal_in_place_append_tag(
                        rind::aead::Nonce::assume_unique_for_key(nonce),
                        &aad,
                        &mut mine,
                    )
                    .unwrap();
                    prop_assert_eq!(&mine, &sealed);

                    if let Some(flip) = flip {
                        let bit = flip.index(sealed.len() * 8);
                        sealed[bit / 8] ^= 1 << (bit % 8);
                    }
                    let opened = ours
                        .open_in_place(rind::aead::Nonce::assume_unique_for_key(nonce), &aad, &mut sealed)
                        .map(|plain| plain.to_vec());
                    if flip.is_some() {
                        prop_assert_eq!(opened, Err(rind::Error::DecryptFailed));
                    } else {
                        prop_assert_eq!(opened, Ok(msg.clone()));
                    }
                }};
            }
            check!(&rind::aead::AES_128_GCM, aes_gcm::Aes128Gcm, &key[..16]);
            check!(&rind::aead::AES_256_GCM, aes_gcm::Aes256Gcm, &key[..]);
            check!(&rind::aead::CHACHA20_POLY1305, chacha20poly1305::ChaCha20Poly1305, &key[..]);
        }
    }

    // Each case generates a key, which is slow under emulation.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(16))]

        #[test]
        fn ml_kem(seed in any::<[u8; 64]>(), m in any::<[u8; 32]>()) {
            use ml_kem::{Decapsulate as _, KeyExport as _};

            macro_rules! check {
                ($ours:ty, $theirs:ident, $kem:ident) => {{
                    // ml-kem's key, which rind encapsulates to and ml-kem
                    // decapsulates for.
                    let dk = ml_kem::$theirs::DecapsulationKey::from_seed(seed.into());
                    let ek = dk.encapsulation_key();
                    let (ciphertext, secret) =
                        rind::kem::EncapsulationKey::<$ours>::new(&ek.to_bytes())
                            .unwrap()
                            .encapsulate()
                            .unwrap();
                    let ciphertext =
                        ml_kem::Ciphertext::<ml_kem::$kem>::try_from(ciphertext.as_ref()).unwrap();
                    prop_assert_eq!(secret.as_ref(), &dk.decapsulate(&ciphertext)[..]);

                    // rind's key, which ml-kem encapsulates to and rind
                    // decapsulates for.
                    let ours = rind::kem::DecapsulationKey::<$ours>::generate().unwrap();
                    let theirs = ml_kem::$theirs::EncapsulationKey::new(
                        &ml_kem::Key::<ml_kem::$theirs::EncapsulationKey>::try_from(
                            ours.public_key().as_ref(),
                        )
                        .unwrap(),
                    )
                    .unwrap();
                    let (ciphertext, secret) = theirs.encapsulate_deterministic(&m.into());
                    let got = ours
                        .decapsulate(&rind::kem::Ciphertext::<$ours>::new(ciphertext.as_ref()).unwrap());
                    prop_assert_eq!(got.as_ref(), &secret[..]);
                }};
            }
            check!(rind::kem::MlKem512, ml_kem_512, MlKem512);
            check!(rind::kem::MlKem768, ml_kem_768, MlKem768);
            check!(rind::kem::MlKem1024, ml_kem_1024, MlKem1024);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(16))]

        #[test]
        fn ml_dsa(seed in any::<[u8; 32]>(), message in vec(any::<u8>(), 0..300), flip in any::<Option<Index>>()) {
            use ml_dsa::{Keypair as _, KeyExport as _, Signer as _, Verifier as _};

            macro_rules! check {
                ($ours:ty, $theirs:ty) => {{
                    let theirs = ml_dsa::SigningKey::<$theirs>::from_seed(&seed.into());
                    let ours = rind::ml_dsa::KeyPair::<$ours>::from_seed(&seed).unwrap();
                    let public = theirs.verifying_key();
                    prop_assert_eq!(ours.public_key().as_ref(), &public.to_bytes()[..]);

                    // Each verifies the other's signature, and refuses it
                    // with one bit flipped.
                    let mut signature = ours.sign(&message).unwrap().as_ref().to_vec();
                    let theirs_signature = theirs.sign(&message).encode().to_vec();
                    let verifier = rind::ml_dsa::PublicKey::<$ours>::new(&public.to_bytes()).unwrap();
                    verifier.verify(&message, &theirs_signature).unwrap();
                    if let Some(flip) = flip {
                        let bit = flip.index(signature.len() * 8);
                        signature[bit / 8] ^= 1 << (bit % 8);
                    }
                    let accepted = ml_dsa::Signature::<$theirs>::decode(&signature.as_slice().try_into().unwrap())
                        .is_some_and(|signature| public.verify(&message, &signature).is_ok());
                    prop_assert_eq!(accepted, flip.is_none());
                }};
            }
            check!(rind::ml_dsa::MlDsa44, ml_dsa::MlDsa44);
            check!(rind::ml_dsa::MlDsa65, ml_dsa::MlDsa65);
            check!(rind::ml_dsa::MlDsa87, ml_dsa::MlDsa87);
        }
    }

    // dalek on the tiers where rind runs s2n-bignum; armv7 and the portable
    // backend run dalek, which would check it against itself.
    #[cfg(all(
        any(target_arch = "x86_64", target_arch = "aarch64"),
        target_endian = "little",
        not(rind_portable)
    ))]
    proptest! {
        #[test]
        fn ed25519_x25519(
            seed in any::<[u8; 32]>(),
            peer in any::<[u8; 32]>(),
            message in vec(any::<u8>(), 0..300),
            flip in any::<Option<Index>>(),
        ) {
            use ed25519_dalek::Signer as _;

            let theirs = ed25519_dalek::SigningKey::from_bytes(&seed);
            let ours = rind::ed25519::KeyPair::from_seed(&seed).unwrap();
            let (ours_public, theirs_public) = (ours.public_key(), theirs.verifying_key());
            prop_assert_eq!(ours_public.as_ref(), theirs_public.as_bytes());
            let signature = theirs.sign(&message);
            let ours_signature = ours.sign(&message);
            prop_assert_eq!(ours_signature.as_ref(), &signature.to_bytes()[..]);
            let mut signature = signature.to_bytes();
            if let Some(flip) = flip {
                let bit = flip.index(signature.len() * 8);
                signature[bit / 8] ^= 1 << (bit % 8);
            }
            prop_assert_eq!(
                rind::ed25519::PublicKey::new(theirs.verifying_key().as_bytes())
                    .unwrap()
                    .verify(&message, &signature)
                    .is_ok(),
                flip.is_none()
            );

            // Any 32 bytes is a private key and a peer's u-coordinate; both
            // refuse a low-order peer's all-zero secret.
            let secret = x25519_dalek::StaticSecret::from(seed);
            let public = x25519_dalek::PublicKey::from(&secret);
            let ours = rind::agreement::PrivateKey::from_scalar(&rind::agreement::X25519, &seed).unwrap();
            prop_assert_eq!(ours.public_key().as_ref(), public.as_bytes());
            let shared = secret.diffie_hellman(&x25519_dalek::PublicKey::from(peer));
            match ours.agree(&peer) {
                Ok(got) => {
                    prop_assert!(shared.was_contributory());
                    prop_assert_eq!(got.as_ref(), shared.as_bytes());
                }
                Err(_) => prop_assert!(!shared.was_contributory()),
            }
        }
    }

    /// What each curve's tests run: the curve's own hash with both encodings,
    /// and the other hashes with the ASN.1 one, which rind verifies for them.
    struct Case {
        hash: &'static rind::digest::Algorithm,
        asn1: &'static rind::ecdsa::VerificationAlgorithm,
        fixed: Option<&'static rind::ecdsa::VerificationAlgorithm>,
    }

    struct NistCurve {
        /// The scalar and field element length in bytes.
        len: usize,
        ecdh: &'static rind::agreement::Algorithm,
        sign_fixed: &'static rind::ecdsa::SigningAlgorithm,
        sign_asn1: &'static rind::ecdsa::SigningAlgorithm,
        cases: Vec<Case>,
    }

    fn nist_curves() -> [NistCurve; 3] {
        use rind::agreement::{ECDH_P256, ECDH_P384, ECDH_P521};
        use rind::digest::{SHA256, SHA384, SHA512};
        use rind::ecdsa::{sign, verify};
        [
            NistCurve {
                len: 32,
                ecdh: &ECDH_P256,
                sign_fixed: &sign::P256_SHA256_FIXED,
                sign_asn1: &sign::P256_SHA256_ASN1,
                cases: vec![
                    Case {
                        hash: &SHA256,
                        asn1: &verify::P256_SHA256_ASN1,
                        fixed: Some(&verify::P256_SHA256_FIXED),
                    },
                    Case {
                        hash: &SHA384,
                        asn1: &verify::P256_SHA384_ASN1,
                        fixed: None,
                    },
                    Case {
                        hash: &SHA512,
                        asn1: &verify::P256_SHA512_ASN1,
                        fixed: None,
                    },
                ],
            },
            NistCurve {
                len: 48,
                ecdh: &ECDH_P384,
                sign_fixed: &sign::P384_SHA384_FIXED,
                sign_asn1: &sign::P384_SHA384_ASN1,
                cases: vec![
                    Case {
                        hash: &SHA384,
                        asn1: &verify::P384_SHA384_ASN1,
                        fixed: Some(&verify::P384_SHA384_FIXED),
                    },
                    Case {
                        hash: &SHA256,
                        asn1: &verify::P384_SHA256_ASN1,
                        fixed: None,
                    },
                    Case {
                        hash: &SHA512,
                        asn1: &verify::P384_SHA512_ASN1,
                        fixed: None,
                    },
                ],
            },
            NistCurve {
                len: 66,
                ecdh: &ECDH_P521,
                sign_fixed: &sign::P521_SHA512_FIXED,
                sign_asn1: &sign::P521_SHA512_ASN1,
                cases: vec![
                    Case {
                        hash: &SHA512,
                        asn1: &verify::P521_SHA512_ASN1,
                        fixed: Some(&verify::P521_SHA512_FIXED),
                    },
                    Case {
                        hash: &SHA256,
                        asn1: &verify::P521_SHA256_ASN1,
                        fixed: None,
                    },
                    Case {
                        hash: &SHA384,
                        asn1: &verify::P521_SHA384_ASN1,
                        fixed: None,
                    },
                ],
            },
        ]
    }

    #[cfg(all(
        any(target_arch = "x86_64", target_arch = "aarch64"),
        target_endian = "little",
        not(rind_portable)
    ))]
    /// A scalar of the curve's length: P-521's leading byte keeps its nine
    /// bits. It may still be zero, or n or more, which no private key is, so
    /// the test screens it.
    fn scalar(len: usize, bytes: &[u8]) -> Vec<u8> {
        let mut scalar = bytes[..len].to_vec();
        if len == 66 {
            scalar[0] &= 1;
        }
        scalar
    }

    /// Splits an ASN.1 `ECDSA-Sig-Value` into `r || s`, each `len` bytes.
    fn fixed_from_der(der: &[u8], len: usize) -> Vec<u8> {
        let mut at = if der[1] & 0x80 == 0 {
            2
        } else {
            2 + usize::from(der[1] & 0x7f)
        };
        let mut out = Vec::new();
        for _ in 0..2 {
            assert_eq!(der[at], 2);
            let int = &der[at + 2..at + 2 + usize::from(der[at + 1])];
            let int = &int[int.iter().take_while(|&&b| b == 0).count()..];
            out.extend_from_slice(&vec![0; len - int.len()]);
            out.extend_from_slice(int);
            at += 2 + usize::from(der[at + 1]);
        }
        out
    }

    /// The reverse: a minimal DER `ECDSA-Sig-Value` for `r || s`.
    fn der_from_fixed(fixed: &[u8]) -> Vec<u8> {
        let int = |bytes: &[u8]| {
            let bytes = &bytes[bytes.iter().take_while(|&&b| b == 0).count()..];
            let padded = if bytes.first().is_none_or(|b| b & 0x80 != 0) {
                [&[0][..], bytes].concat()
            } else {
                bytes.to_vec()
            };
            crate::der(2, &padded)
        };
        let (r, s) = fixed.split_at(fixed.len() / 2);
        crate::der(0x30, &[int(r), int(s)].concat())
    }

    /// Schoolbook affine P-384 and P-521 over `num-bigint`: each point
    /// operation divides, with no table, no projective coordinates, and no
    /// field code of any kind, so it shares nothing with rind on any tier,
    /// including armv7 and the portable backend, where RustCrypto's crates
    /// run fiat-crypto's arithmetic as rind does. It is slow and variable
    /// time, and checks its constants against the curve equation and the
    /// group's order.
    mod reference {
        use num_bigint::{BigInt, BigUint, Sign};

        pub type Point = Option<(BigUint, BigUint)>;

        pub struct Curve {
            pub p: BigUint,
            pub n: BigUint,
            pub b: BigUint,
            pub g: (BigUint, BigUint),
            pub len: usize,
        }

        fn hex(digits: &str) -> BigUint {
            BigUint::parse_bytes(digits.as_bytes(), 16).unwrap()
        }

        pub fn p384() -> Curve {
            let one = BigUint::from(1u8);
            Curve {
                p: (&one << 384) - (&one << 128) - (&one << 96) + (&one << 32) - &one,
                n: hex(
                    "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
                ),
                b: hex(
                    "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef",
                ),
                g: (
                    hex(
                        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
                    ),
                    hex(
                        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
                    ),
                ),
                len: 48,
            }
        }

        pub fn p521() -> Curve {
            let one = BigUint::from(1u8);
            Curve {
                p: (&one << 521) - &one,
                n: hex(
                    "1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409",
                ),
                b: hex(
                    "0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00",
                ),
                g: (
                    hex(
                        "00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66",
                    ),
                    hex(
                        "011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650",
                    ),
                ),
                len: 66,
            }
        }

        /// `a`'s inverse modulo the prime `m`, by the extended Euclidean
        /// algorithm.
        fn inverse(a: &BigUint, m: &BigUint) -> BigUint {
            let m = BigInt::from(m.clone());
            let (mut r0, mut r1) = (m.clone(), BigInt::from(a.clone()) % &m);
            let (mut t0, mut t1) = (BigInt::from(0), BigInt::from(1));
            while r1.sign() != Sign::NoSign {
                let q = &r0 / &r1;
                let r2 = &r0 - &q * &r1;
                (r0, r1) = (r1, r2);
                let t2 = &t0 - &q * &t1;
                (t0, t1) = (t1, t2);
            }
            assert_eq!(r0, BigInt::from(1));
            (((t0 % &m) + &m) % &m).to_biguint().unwrap()
        }

        /// The big-endian `len` bytes of `x`.
        pub fn be(x: &BigUint, len: usize) -> Vec<u8> {
            let bytes = x.to_bytes_be();
            [vec![0; len - bytes.len()], bytes].concat()
        }

        impl Curve {
            fn sub(&self, a: &BigUint, b: &BigUint) -> BigUint {
                (a + &self.p - b) % &self.p
            }

            pub fn on_curve(&self, (x, y): &(BigUint, BigUint)) -> bool {
                let rhs = (x * x % &self.p * x + &self.p * 3u8 - x * 3u8 + &self.b) % &self.p;
                y * y % &self.p == rhs
            }

            pub fn add(&self, a: &Point, b: &Point) -> Point {
                let (Some((x1, y1)), Some((x2, y2))) = (a, b) else {
                    return a.clone().or_else(|| b.clone());
                };
                let lambda = if x1 == x2 {
                    if y1 != y2 || *y1 == BigUint::from(0u8) {
                        return None;
                    }
                    // a = -3, so the slope is (3x^2 - 3) / 2y.
                    let numerator = (x1 * x1 * 3u8 + &self.p - 3u8) % &self.p;
                    numerator * inverse(&(y1 * 2u8), &self.p) % &self.p
                } else {
                    self.sub(y2, y1) * inverse(&self.sub(x2, x1), &self.p) % &self.p
                };
                let x3 = self.sub(&self.sub(&(&lambda * &lambda % &self.p), x1), x2);
                let y3 = self.sub(&(&lambda * self.sub(x1, &x3) % &self.p), y1);
                Some((x3, y3))
            }

            /// `k * point`, by double and add from the top bit.
            pub fn mul(&self, k: &BigUint, point: &Point) -> Point {
                let mut acc = None;
                for bit in (0..k.bits()).rev() {
                    acc = self.add(&acc, &acc);
                    if k.bit(bit) {
                        acc = self.add(&acc, point);
                    }
                }
                acc
            }

            pub fn generator(&self) -> Point {
                Some(self.g.clone())
            }

            /// X9.62's uncompressed point.
            pub fn encode(&self, point: &Point) -> Vec<u8> {
                let (x, y) = point.as_ref().expect("not the point at infinity");
                [&[4][..], &be(x, self.len), &be(y, self.len)].concat()
            }

            /// Checks the constants: G is on the curve, and n * G is the point
            /// at infinity.
            pub fn check_constants(&self) {
                assert!(self.on_curve(&self.g));
                assert_eq!(self.mul(&self.n, &self.generator()), None);
            }

            /// A scalar from 1 to n - 1 out of any bytes.
            pub fn scalar(&self, bytes: &[u8]) -> BigUint {
                BigUint::from_bytes_be(bytes) % (&self.n - 1u8) + 1u8
            }

            /// The ECDH shared secret: the x-coordinate of `d * peer`.
            pub fn ecdh(&self, d: &BigUint, peer: &Point) -> Vec<u8> {
                let shared = self.mul(d, peer).expect("not the point at infinity");
                be(&shared.0, self.len)
            }

            /// The digest as FIPS 186-5 takes it: its leftmost n.bits() bits.
            pub fn hash_to_scalar(&self, digest: &[u8]) -> BigUint {
                let e = BigUint::from_bytes_be(digest);
                let excess = (digest.len() * 8).saturating_sub(self.n.bits() as usize);
                e >> excess
            }

            /// An ECDSA signature `r || s` of `digest`, by the nonce `k`, or
            /// nothing where `r` or `s` is zero.
            pub fn sign(&self, d: &BigUint, k: &BigUint, digest: &[u8]) -> Option<Vec<u8>> {
                let zero = BigUint::from(0u8);
                let (x, _) = self.mul(k, &self.generator())?;
                let r = x % &self.n;
                let s = inverse(k, &self.n) * (self.hash_to_scalar(digest) + &r * d) % &self.n;
                (r != zero && s != zero).then(|| [be(&r, self.len), be(&s, self.len)].concat())
            }

            /// Whether `r || s` signs `digest` under `public`.
            pub fn verify(&self, public: &Point, digest: &[u8], signature: &[u8]) -> bool {
                let (r, s) = signature.split_at(self.len);
                let (r, s) = (BigUint::from_bytes_be(r), BigUint::from_bytes_be(s));
                let zero = BigUint::from(0u8);
                if r == zero || s == zero || r >= self.n || s >= self.n {
                    return false;
                }
                let w = inverse(&s, &self.n);
                let u1 = self.hash_to_scalar(digest) * &w % &self.n;
                let u2 = &r * &w % &self.n;
                let point = self.add(&self.mul(&u1, &self.generator()), &self.mul(&u2, public));
                point.is_some_and(|(x, _)| x % &self.n == r)
            }
        }
    }

    #[test]
    fn reference_constants() {
        reference::p384().check_constants();
        reference::p521().check_constants();
    }

    // Three 66-byte values cover the private key, the peer's, and the nonce
    // of the largest curve; the smaller ones reduce them.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(4))]

        // P-384 and P-521 against the schoolbook reference, on every tier.
        #[test]
        fn p384_p521_reference(
            bytes in vec(any::<u8>(), 198),
            message in vec(any::<u8>(), 0..300),
        ) {
            let curves = nist_curves();
            for (curve, reference) in [
                (&curves[1], reference::p384()),
                (&curves[2], reference::p521()),
            ] {
                let d = reference.scalar(&bytes[..66]);
                let peer = reference.scalar(&bytes[66..132]);
                let k = reference.scalar(&bytes[132..]);
                let public = reference.mul(&d, &reference.generator());
                let peer_public = reference.mul(&peer, &reference.generator());
                let encoded = reference.encode(&public);

                // Key derivation and ECDH.
                let d_bytes = reference::be(&d, curve.len);
                let ours = rind::agreement::PrivateKey::from_scalar(curve.ecdh, &d_bytes).unwrap();
                prop_assert_eq!(ours.public_key().as_ref(), &encoded[..]);
                let shared = ours.agree(&reference.encode(&peer_public)).unwrap();
                prop_assert_eq!(shared.as_ref(), &reference.ecdh(&d, &peer_public)[..]);

                for case in &curve.cases {
                    let digest = rind::digest::digest(case.hash, &message);
                    let other = rind::digest::digest(case.hash, b"other");

                    // rind signs; the reference verifies.
                    for (sign, is_asn1) in [(curve.sign_fixed, false), (curve.sign_asn1, true)] {
                        let pair = rind::ecdsa::KeyPair::from_scalar_and_public_key(sign, &d_bytes, &encoded).unwrap();
                        let signature = pair.sign_digest(&digest).unwrap();
                        let fixed = if is_asn1 {
                            fixed_from_der(signature.as_ref(), curve.len)
                        } else {
                            signature.as_ref().to_vec()
                        };
                        prop_assert!(reference.verify(&public, digest.as_ref(), &fixed));
                        prop_assert!(!reference.verify(&public, other.as_ref(), &fixed));
                    }

                    // The reference signs; rind verifies.
                    let Some(fixed) = reference.sign(&d, &k, digest.as_ref()) else { continue };
                    let verifier = rind::ecdsa::PublicKey::new(case.asn1, &encoded).unwrap();
                    let der = der_from_fixed(&fixed);
                    prop_assert!(verifier.verify_digest(&digest, &der).is_ok());
                    prop_assert!(verifier.verify_digest(&other, &der).is_err());
                    if let Some(verification) = case.fixed {
                        let verifier = rind::ecdsa::PublicKey::new(verification, &encoded).unwrap();
                        prop_assert!(verifier.verify_digest(&digest, &fixed).is_ok());
                        prop_assert!(verifier.verify_digest(&other, &fixed).is_err());
                    }
                }
            }
        }
    }

    // RustCrypto's NIST curves on the tiers where rind runs s2n-bignum,
    // verified-garbage, or Graviola; armv7 and the portable backend run
    // fiat-crypto, as its crates do, so the test leaves them out.
    #[cfg(all(
        any(target_arch = "x86_64", target_arch = "aarch64"),
        target_endian = "little",
        not(rind_portable)
    ))]
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(16))]

        #[test]
        fn nist_rustcrypto(
            bytes in vec(any::<u8>(), 198),
            message in vec(any::<u8>(), 0..300),
        ) {
            macro_rules! check {
                ($theirs:ident, $curve:expr) => {{
                    use $theirs::ecdsa::signature::hazmat::{PrehashSigner, PrehashVerifier};

                    let curve = &$curve;
                    let (d, peer) = (scalar(curve.len, &bytes), scalar(curve.len, &bytes[66..]));
                    // Zero and n or more are no private key, and proptest
                    // weights the bytes that make them (all zero, all ones):
                    // both sides must refuse them alike, and the rest of the
                    // case needs two keys.
                    let ours = rind::agreement::PrivateKey::from_scalar(curve.ecdh, &d);
                    let ours_peer = rind::agreement::PrivateKey::from_scalar(curve.ecdh, &peer);
                    let secret = $theirs::SecretKey::from_slice(&d);
                    let peer_secret = $theirs::SecretKey::from_slice(&peer);
                    prop_assert_eq!(ours.is_ok(), secret.is_ok());
                    prop_assert_eq!(ours_peer.is_ok(), peer_secret.is_ok());
                    prop_assume!(secret.is_ok() && peer_secret.is_ok());
                    let (ours, ours_peer) = (ours.unwrap(), ours_peer.unwrap());
                    let (secret, peer_secret) = (secret.unwrap(), peer_secret.unwrap());
                    let public = secret.public_key();
                    let peer_public = peer_secret.public_key();
                    prop_assert_eq!(ours.public_key().as_ref(), &public.to_sec1_bytes()[..]);

                    // ECDH, both ways.
                    let shared = $theirs::elliptic_curve::ecdh::diffie_hellman(
                        secret.to_nonzero_scalar(),
                        peer_public.as_affine(),
                    );
                    let agreed = ours.agree(&peer_public.to_sec1_bytes()).unwrap();
                    prop_assert_eq!(agreed.as_ref(), &shared.raw_secret_bytes()[..]);
                    let agreed = ours_peer.agree(ours.public_key().as_ref()).unwrap();
                    prop_assert_eq!(agreed.as_ref(), &shared.raw_secret_bytes()[..]);

                    let signing = $theirs::ecdsa::SigningKey::from(&secret);
                    let verifying = *signing.verifying_key();
                    for case in &curve.cases {
                        let digest = rind::digest::digest(case.hash, &message);
                        let other = rind::digest::digest(case.hash, b"other");

                        // They sign; rind verifies, in each encoding it has.
                        let signature: $theirs::ecdsa::Signature =
                            signing.sign_prehash(digest.as_ref()).unwrap();
                        let verifier = rind::ecdsa::PublicKey::new(case.asn1, ours.public_key().as_ref()).unwrap();
                        prop_assert!(verifier.verify_digest(&digest, signature.to_der().as_bytes()).is_ok());
                        prop_assert!(verifier.verify_digest(&other, signature.to_der().as_bytes()).is_err());
                        if let Some(fixed) = case.fixed {
                            let verifier = rind::ecdsa::PublicKey::new(fixed, ours.public_key().as_ref()).unwrap();
                            prop_assert!(verifier.verify_digest(&digest, &signature.to_bytes()).is_ok());
                        }

                        // rind signs; they verify.
                        for (sign, is_asn1) in [(curve.sign_fixed, false), (curve.sign_asn1, true)] {
                            let pair = rind::ecdsa::KeyPair::from_scalar_and_public_key(
                                sign,
                                &d,
                                ours.public_key().as_ref(),
                            )
                            .unwrap();
                            let signature = pair.sign_digest(&digest).unwrap();
                            let theirs = if is_asn1 {
                                $theirs::ecdsa::Signature::from_der(signature.as_ref())
                            } else {
                                $theirs::ecdsa::Signature::from_slice(signature.as_ref())
                            }
                            .unwrap();
                            prop_assert!(verifying.verify_prehash(digest.as_ref(), &theirs).is_ok());
                            prop_assert!(verifying.verify_prehash(other.as_ref(), &theirs).is_err());
                        }
                    }
                }};
            }
            let curves = nist_curves();
            let [p256, p384, p521] = curves;
            check!(p256, p256);
            check!(p384, p384);
            check!(p521, p521);
        }
    }

    // libcrux's P-256 (HACL*) on armv7 and the portable backend, where
    // RustCrypto's p256 runs fiat-crypto's field arithmetic as rind does.
    // HACL* signs a digest of 32 bytes or more by its leftmost 32.
    #[cfg(not(all(
        any(target_arch = "x86_64", target_arch = "aarch64"),
        target_endian = "little",
        not(rind_portable)
    )))]
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(16))]

        #[test]
        fn p256_libcrux(
            d in any::<[u8; 32]>(),
            peer in any::<[u8; 32]>(),
            nonce in any::<[u8; 32]>(),
            message in vec(any::<u8>(), 0..300),
        ) {
            let curve = &nist_curves()[0];
            let (mut theirs_public, mut peer_public) = ([0u8; 64], [0u8; 64]);
            prop_assume!(libcrux_p256::dh_initiator(&mut theirs_public, &d));
            prop_assume!(libcrux_p256::dh_initiator(&mut peer_public, &peer));
            let ours = rind::agreement::PrivateKey::from_scalar(curve.ecdh, &d).unwrap();
            let encoded = [&[4][..], &theirs_public].concat();
            prop_assert_eq!(ours.public_key().as_ref(), &encoded[..]);

            // ECDH: HACL* returns the point, whose x-coordinate is the secret.
            let mut shared = [0u8; 64];
            prop_assert!(libcrux_p256::dh_responder(&mut shared, &peer_public, &d));
            let agreed = ours.agree(&[&[4][..], &peer_public].concat()).unwrap();
            prop_assert_eq!(agreed.as_ref(), &shared[..32]);

            for case in &curve.cases {
                let digest = rind::digest::digest(case.hash, &message);
                let other = rind::digest::digest(case.hash, b"other");

                // HACL* signs; rind verifies.
                let mut signature = [0u8; 64];
                prop_assume!(libcrux_p256::ecdsa_sign_p256_without_hash(
                    &mut signature,
                    digest.as_ref().len() as u32,
                    digest.as_ref(),
                    &d,
                    &nonce,
                ));
                let verifier = rind::ecdsa::PublicKey::new(case.asn1, &encoded).unwrap();
                prop_assert!(verifier.verify_digest(&digest, &der_from_fixed(&signature)).is_ok());
                prop_assert!(verifier.verify_digest(&other, &der_from_fixed(&signature)).is_err());
                if let Some(fixed) = case.fixed {
                    let verifier = rind::ecdsa::PublicKey::new(fixed, &encoded).unwrap();
                    prop_assert!(verifier.verify_digest(&digest, &signature).is_ok());
                }

                // rind signs; HACL* verifies.
                for (sign, is_asn1) in [(curve.sign_fixed, false), (curve.sign_asn1, true)] {
                    let pair = rind::ecdsa::KeyPair::from_scalar_and_public_key(sign, &d, &encoded).unwrap();
                    let signature = pair.sign_digest(&digest).unwrap();
                    let fixed = if is_asn1 {
                        fixed_from_der(signature.as_ref(), 32)
                    } else {
                        signature.as_ref().to_vec()
                    };
                    let verified = |digest: &rind::digest::Digest| {
                        libcrux_p256::ecdsa_verif_without_hash(
                            digest.as_ref().len() as u32,
                            digest.as_ref(),
                            &theirs_public,
                            &fixed[..32],
                            &fixed[32..],
                        )
                    };
                    prop_assert!(verified(&digest));
                    prop_assert!(!verified(&other));
                }
            }
        }
    }
}
