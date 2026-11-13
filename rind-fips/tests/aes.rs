// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES through the module agrees with rind's, which its own tests check
//! against Wycheproof and aws-lc-rs: the block cipher, CTR, CBC, key
//! wrapping, QUIC header protection, and AES-GCM opening what rind seals.

use rind_fips::{Error, aead, cipher, hkdf, key_wrap};

/// `len` bytes that differ for each `seed`.
fn bytes(seed: &str, len: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(len);
    let mut counter = 0u32;
    while out.len() < len {
        let mut ctx = rind::digest::Context::new(&rind::digest::SHA256);
        ctx.update(seed.as_bytes());
        ctx.update(&counter.to_be_bytes());
        out.extend_from_slice(ctx.finish().as_ref());
        counter += 1;
    }
    out.truncate(len);
    out
}

/// Asserts both calls failed with the same error, or both succeeded.
#[track_caller]
fn same<T, U>(ours: &Result<T, Error>, theirs: &Result<U, rind::Error>) {
    assert_eq!(
        format!("{:?}", ours.as_ref().err()),
        format!("{:?}", theirs.as_ref().err())
    );
}

/// Asserts both values print alike.
#[track_caller]
fn same_debug(ours: &impl core::fmt::Debug, theirs: &impl core::fmt::Debug) {
    assert_eq!(format!("{ours:?}"), format!("{theirs:?}"));
}

/// Lengths around every block boundary that matters, and empty.
const LENGTHS: [usize; 12] = [0, 1, 15, 16, 17, 31, 32, 33, 63, 64, 255, 1000];

const AEADS: [(&aead::Algorithm, &rind::aead::Algorithm); 3] = [
    (&aead::AES_128_GCM, &rind::aead::AES_128_GCM),
    (&aead::AES_192_GCM, &rind::aead::AES_192_GCM),
    (&aead::AES_256_GCM, &rind::aead::AES_256_GCM),
];

const CIPHERS: [(&cipher::Algorithm, &rind::cipher::Algorithm, usize); 3] = [
    (&cipher::AES_128, &rind::cipher::AES_128, 16),
    (&cipher::AES_192, &rind::cipher::AES_192, 24),
    (&cipher::AES_256, &rind::cipher::AES_256, 32),
];

#[test]
fn aead_opens_what_rind_seals() {
    for (ours, theirs) in AEADS {
        assert_eq!(ours.key_len(), theirs.key_len());
        assert_eq!(ours.tag_len(), theirs.tag_len());
        assert_eq!(ours.nonce_len(), theirs.nonce_len());
        same_debug(ours, theirs);
        for len in 0..=33 {
            let key = bytes("key", len);
            same(
                &aead::Key::new(ours, &key),
                &rind::aead::Key::new(theirs, &key),
            );
        }

        let key_value = bytes("key", ours.key_len());
        let key = aead::Key::new(ours, &key_value).unwrap();
        let reference = rind::aead::Key::new(theirs, &key_value).unwrap();
        same_debug(&key, &reference);
        for len in LENGTHS {
            for aad_len in [0, 1, 16, 17] {
                let plaintext = bytes("plaintext", len);
                let aad = bytes("aad", aad_len);
                let n: [u8; 12] = bytes(&format!("nonce {len} {aad_len}"), 12)
                    .try_into()
                    .unwrap();
                let theirs_nonce = || rind::aead::Nonce::assume_unique_for_key(n);
                let nonce = || aead::Nonce::assume_unique_for_key(n);
                let mut sealed = plaintext.clone();
                reference
                    .seal_in_place_append_tag(theirs_nonce(), &aad, &mut sealed)
                    .unwrap();

                let mut opened = sealed.clone();
                assert_eq!(
                    key.open_in_place(nonce(), &aad, &mut opened).unwrap(),
                    plaintext
                );

                let (ciphertext, tag) = sealed.split_at(len);
                let tag = aead::Tag::try_from(tag).unwrap();
                let mut separate = ciphertext.to_vec();
                assert_eq!(
                    key.open_in_place_separate_tag(nonce(), &aad, tag, &mut separate)
                        .unwrap(),
                    plaintext
                );

                // A flipped ciphertext, tag, or AAD byte fails as rind's
                // does, leaving the buffer as rind's leaves it.
                let mut cases = vec![(sealed.len() - 1, false)];
                if len > 0 {
                    cases.push((0, false));
                }
                if aad_len > 0 {
                    cases.push((0, true));
                }
                for (at, in_aad) in cases {
                    let (mut ours_buf, mut theirs_buf) = (sealed.clone(), sealed.clone());
                    let mut bad_aad = aad.clone();
                    if in_aad {
                        bad_aad[at] ^= 1;
                    } else {
                        ours_buf[at] ^= 1;
                        theirs_buf[at] ^= 1;
                    }
                    let result = key
                        .open_in_place(nonce(), &bad_aad, &mut ours_buf)
                        .map(|_| ());
                    let expected = reference
                        .open_in_place(theirs_nonce(), &bad_aad, &mut theirs_buf)
                        .map(|_| ());
                    assert_eq!(result, Err(Error::DecryptFailed));
                    same(&result, &expected);
                    assert_eq!(ours_buf, theirs_buf);
                }
            }
        }

        // Shorter than a tag: refused, unchanged.
        let mut short = [0xaa; 15];
        assert_eq!(
            key.open_in_place(aead::Nonce::assume_unique_for_key([0; 12]), &[], &mut short),
            Err(Error::DecryptFailed)
        );
        assert_eq!(short, [0xaa; 15]);
    }

    for len in 0..=17 {
        let tag = &[0u8; 17][..len];
        same(&aead::Tag::try_from(tag), &rind::aead::Tag::try_from(tag));
    }
    same_debug(
        &aead::Nonce::assume_unique_for_key([1; 12]),
        &rind::aead::Nonce::assume_unique_for_key([1; 12]),
    );
    same_debug(
        &aead::Tag::try_from(&[2; 16][..]).unwrap(),
        &rind::aead::Tag::try_from(&[2; 16][..]).unwrap(),
    );
}

#[test]
fn gcm_opens_what_rind_seals() {
    use aead::gcm::{Iv, Key, TagLength};
    use rind::aead::gcm as theirs_gcm;

    let lengths = [
        (TagLength::Full, theirs_gcm::TagLength::Full),
        (TagLength::Truncated120, theirs_gcm::TagLength::Truncated120),
        (TagLength::Truncated112, theirs_gcm::TagLength::Truncated112),
        (TagLength::Truncated104, theirs_gcm::TagLength::Truncated104),
        (TagLength::Truncated96, theirs_gcm::TagLength::Truncated96),
        (TagLength::Truncated64, theirs_gcm::TagLength::Truncated64),
        (TagLength::Truncated32, theirs_gcm::TagLength::Truncated32),
    ];
    for (ours, theirs, key_len) in CIPHERS {
        for len in [0, 15, 16, 17, 24, 32, 33] {
            let key = bytes("key", len);
            same(
                &Key::new(ours, &key, TagLength::Full),
                &theirs_gcm::Key::new(theirs, &key, theirs_gcm::TagLength::Full),
            );
        }
        let key_value = bytes("key", key_len);
        for (tag_ours, tag_theirs) in lengths {
            same_debug(&tag_ours, &tag_theirs);
            let key = Key::new(ours, &key_value, tag_ours).unwrap();
            let reference = theirs_gcm::Key::new(theirs, &key_value, tag_theirs).unwrap();
            assert_eq!(key.tag_len(), reference.tag_len());
            same_debug(&key, &reference);
            let tag_len = key.tag_len();

            for iv_len in [1, 8, 12, 16, 60] {
                for len in [0, 1, 16, 17, 100] {
                    let iv = bytes("iv", iv_len);
                    let plaintext = bytes("plaintext", len);
                    let aad = bytes("aad", len % 7);
                    let theirs_iv = || theirs_gcm::Iv::assume_unique_for_key(&iv).unwrap();
                    let our_iv = || Iv::assume_unique_for_key(&iv).unwrap();
                    let mut sealed = plaintext.clone();
                    reference
                        .seal_in_place_append_tag(theirs_iv(), &aad, &mut sealed)
                        .unwrap();

                    let mut opened = sealed.clone();
                    assert_eq!(
                        key.open_in_place(our_iv(), &aad, &mut opened).unwrap(),
                        plaintext
                    );
                    let (ciphertext, tag) = sealed.split_at(len);
                    let mut separate = ciphertext.to_vec();
                    assert_eq!(
                        key.open_in_place_separate_tag(our_iv(), &aad, tag, &mut separate)
                            .unwrap(),
                        plaintext
                    );

                    // A tag of another length is refused, leaving the buffer.
                    let wrong = [tag, &[0]].concat();
                    let (mut ours_buf, mut theirs_buf) = (ciphertext.to_vec(), ciphertext.to_vec());
                    let result = key
                        .open_in_place_separate_tag(our_iv(), &aad, &wrong, &mut ours_buf)
                        .map(|_| ());
                    let expected = reference
                        .open_in_place_separate_tag(theirs_iv(), &aad, &wrong, &mut theirs_buf)
                        .map(|_| ());
                    assert_eq!(result, Err(Error::WrongLength));
                    same(&result, &expected);
                    assert_eq!(ours_buf, theirs_buf);

                    let (mut ours_buf, mut theirs_buf) = (sealed.clone(), sealed.clone());
                    ours_buf[0] ^= 1;
                    theirs_buf[0] ^= 1;
                    let result = key.open_in_place(our_iv(), &aad, &mut ours_buf).map(|_| ());
                    let expected = reference
                        .open_in_place(theirs_iv(), &aad, &mut theirs_buf)
                        .map(|_| ());
                    assert_eq!(result, Err(Error::DecryptFailed));
                    same(&result, &expected);
                    assert_eq!(ours_buf, theirs_buf);
                }
            }

            let mut short = vec![0xaa; tag_len - 1];
            assert_eq!(
                key.open_in_place(
                    Iv::assume_unique_for_key(&[0; 12]).unwrap(),
                    &[],
                    &mut short
                ),
                Err(Error::DecryptFailed)
            );
            assert_eq!(short, vec![0xaa; tag_len - 1]);
        }
    }
    same(
        &Iv::assume_unique_for_key(&[]),
        &theirs_gcm::Iv::assume_unique_for_key(&[]),
    );
    same_debug(
        &Iv::assume_unique_for_key(&[1]).unwrap(),
        &theirs_gcm::Iv::assume_unique_for_key(&[1]).unwrap(),
    );
}

#[test]
fn quic_masks_match_rind() {
    use aead::quic::{AES_128, AES_256, HeaderProtectionKey, SAMPLE_LEN};
    use rind::aead::quic as theirs_quic;
    assert_eq!(SAMPLE_LEN, theirs_quic::SAMPLE_LEN);

    for (ours, theirs) in [
        (&AES_128, &theirs_quic::AES_128),
        (&AES_256, &theirs_quic::AES_256),
    ] {
        assert_eq!(ours.key_len(), theirs.key_len());
        same_debug(ours, theirs);
        for len in [0, 15, 16, 17, 24, 32, 33] {
            let key = bytes("key", len);
            same(
                &HeaderProtectionKey::new(ours, &key),
                &theirs_quic::HeaderProtectionKey::new(theirs, &key),
            );
        }
        let key_value = bytes("key", ours.key_len());
        let key = HeaderProtectionKey::new(ours, &key_value).unwrap();
        let reference = theirs_quic::HeaderProtectionKey::new(theirs, &key_value).unwrap();
        same_debug(&key, &reference);
        for i in 0..64 {
            let sample: [u8; 16] = bytes(&format!("sample {i}"), 16).try_into().unwrap();
            assert_eq!(key.mask(&sample), reference.mask(&sample));
        }
    }
}

#[test]
fn block_cipher_and_ctr_match_rind() {
    for (ours, theirs, key_len) in CIPHERS {
        same_debug(ours, theirs);
        for len in [0, 15, 16, 17, 24, 31, 32, 33] {
            let key = bytes("key", len);
            let expected = rind::cipher::Aes::new(theirs, &key);
            same(&cipher::Aes::new(ours, &key), &expected);
            same(&cipher::AesCtr::new(ours, &key, 32), &expected);
            same(&cipher::AesCbcEncryptingKey::new(ours, &key), &expected);
            same(&cipher::AesCbcDecryptingKey::new(ours, &key), &expected);
            same(&key_wrap::AesKek::new(ours, &key), &expected);
        }

        let key_value = bytes("key", key_len);
        let aes = cipher::Aes::new(ours, &key_value).unwrap();
        let reference = rind::cipher::Aes::new(theirs, &key_value).unwrap();
        same_debug(&aes, &reference);
        for i in 0..16 {
            let mut block: [u8; 16] = bytes(&format!("block {i}"), 16).try_into().unwrap();
            let mut expected = block;
            aes.encrypt_block(&mut block);
            reference.encrypt_block(&mut expected);
            assert_eq!(block, expected);
        }

        for counter_bits in [0, 1, 2, 16, 32, 64, 127, 128, 129] {
            let ctr = cipher::AesCtr::new(ours, &key_value, counter_bits);
            let theirs_ctr = rind::cipher::AesCtr::new(theirs, &key_value, counter_bits);
            same(&ctr, &theirs_ctr);
            let (Ok(ctr), Ok(theirs_ctr)) = (ctr, theirs_ctr) else {
                continue;
            };
            same_debug(&ctr, &theirs_ctr);
            // Counter blocks about to wrap their counter, the low 32 bits,
            // and the whole block.
            for counter in [0u128, (1 << 32) - 2, u128::MAX - 1, 0x1234] {
                let counter_block = counter.to_be_bytes();
                for len in LENGTHS {
                    let mut ours_buf = bytes("ctr", len);
                    let mut theirs_buf = ours_buf.clone();
                    same(
                        &ctr.apply_keystream(&counter_block, &mut ours_buf),
                        &theirs_ctr.apply_keystream(&counter_block, &mut theirs_buf),
                    );
                    assert_eq!(
                        ours_buf, theirs_buf,
                        "{counter_bits} bits from {counter:#x}, {len} bytes"
                    );
                }
            }
        }
    }
}

#[test]
fn cbc_matches_rind() {
    for (ours, theirs, key_len) in CIPHERS {
        let key_value = bytes("key", key_len);
        let encrypting = cipher::AesCbcEncryptingKey::new(ours, &key_value).unwrap();
        let decrypting = cipher::AesCbcDecryptingKey::new(ours, &key_value).unwrap();
        let theirs_encrypting = rind::cipher::AesCbcEncryptingKey::new(theirs, &key_value).unwrap();
        let theirs_decrypting = rind::cipher::AesCbcDecryptingKey::new(theirs, &key_value).unwrap();
        same_debug(&encrypting, &theirs_encrypting);
        same_debug(&decrypting, &theirs_decrypting);

        for len in LENGTHS {
            let iv: [u8; 16] = bytes(&format!("iv {len}"), 16).try_into().unwrap();
            let ours_iv = || cipher::CbcIv::assume_unpredictable(iv);
            let theirs_iv = || rind::cipher::CbcIv::assume_unpredictable(iv);
            let plaintext = bytes("plaintext", len);

            // Padded, both ways.
            let mut ours_buf = plaintext.clone();
            let mut theirs_buf = plaintext.clone();
            encrypting.encrypt(ours_iv(), &mut ours_buf);
            theirs_encrypting.encrypt(theirs_iv(), &mut theirs_buf);
            assert_eq!(ours_buf, theirs_buf);
            assert_eq!(decrypting.decrypt(&iv, &mut ours_buf).unwrap(), plaintext);

            // Unpadded.
            let mut ours_buf = plaintext.clone();
            let mut theirs_buf = plaintext.clone();
            same(
                &encrypting.encrypt_blocks(ours_iv(), &mut ours_buf),
                &theirs_encrypting.encrypt_blocks(theirs_iv(), &mut theirs_buf),
            );
            assert_eq!(ours_buf, theirs_buf);
            same(
                &decrypting.decrypt_blocks(&iv, &mut ours_buf),
                &theirs_decrypting.decrypt_blocks(&iv, &mut theirs_buf),
            );
            assert_eq!(ours_buf, theirs_buf);

            // Unpadded data as padded ciphertext: mostly malformed padding,
            // which fails and clears the buffer as rind's does.
            let mut ours_buf = plaintext.clone();
            let mut theirs_buf = plaintext.clone();
            let result = decrypting.decrypt(&iv, &mut ours_buf).map(|p| p.to_vec());
            let expected = theirs_decrypting
                .decrypt(&iv, &mut theirs_buf)
                .map(|p| p.to_vec());
            same(&result, &expected);
            assert_eq!(result.ok(), expected.ok());
            assert_eq!(ours_buf, theirs_buf);
        }
    }

    let (a, b) = (
        cipher::CbcIv::random().unwrap(),
        cipher::CbcIv::random().unwrap(),
    );
    assert_ne!(a.as_bytes(), b.as_bytes());
    same_debug(&a, &rind::cipher::CbcIv::assume_unpredictable([0; 16]));
}

#[test]
fn key_wrap_matches_rind() {
    for (ours, theirs, key_len) in CIPHERS {
        let key_value = bytes("kek", key_len);
        let kek = key_wrap::AesKek::new(ours, &key_value).unwrap();
        let reference = rind::key_wrap::AesKek::new(theirs, &key_value).unwrap();
        same_debug(&kek, &reference);

        for len in [0, 8, 15, 16, 24, 32, 40, 64] {
            let key = bytes(&format!("key {len}"), len);
            for wrapped_len in [len + 8, len + 16, len] {
                let mut ours_buf = vec![0xaa; wrapped_len];
                let mut theirs_buf = ours_buf.clone();
                same(
                    &kek.wrap(&key, &mut ours_buf),
                    &reference.wrap(&key, &mut theirs_buf),
                );
                assert_eq!(ours_buf, theirs_buf);
            }

            let mut wrapped = vec![0; len + 8];
            if reference.wrap(&key, &mut wrapped).is_ok() {
                let mut unwrapped = vec![0; len];
                kek.unwrap(&wrapped, &mut unwrapped).unwrap();
                assert_eq!(unwrapped, key);
                // Altered: refused, clearing the output as rind's does.
                wrapped[len / 2] ^= 1;
                let (mut ours_buf, mut theirs_buf) = (vec![0xaa; len], vec![0xaa; len]);
                let result = kek.unwrap(&wrapped, &mut ours_buf);
                assert_eq!(result, Err(Error::DecryptFailed));
                same(&result, &reference.unwrap(&wrapped, &mut theirs_buf));
                assert_eq!(ours_buf, theirs_buf);
            }
            // Lengths refused as rind refuses them.
            let wrapped = bytes("wrapped", len);
            for key_len in [len.saturating_sub(8), len, len + 1] {
                let (mut ours_buf, mut theirs_buf) = (vec![0xaa; key_len], vec![0xaa; key_len]);
                same(
                    &kek.unwrap(&wrapped, &mut ours_buf),
                    &reference.unwrap(&wrapped, &mut theirs_buf),
                );
                assert_eq!(ours_buf, theirs_buf);
            }
        }

        for len in 0..=41 {
            let key = bytes(&format!("padded {len}"), len);
            let wrapped_len = len.next_multiple_of(8) + 8;
            for out_len in [wrapped_len, wrapped_len + 8] {
                let mut ours_buf = vec![0xaa; out_len];
                let mut theirs_buf = ours_buf.clone();
                same(
                    &kek.wrap_padded(&key, &mut ours_buf),
                    &reference.wrap_padded(&key, &mut theirs_buf),
                );
                assert_eq!(ours_buf, theirs_buf);
            }

            let mut wrapped = vec![0; wrapped_len];
            if reference.wrap_padded(&key, &mut wrapped).is_ok() {
                let mut unwrapped = vec![0; wrapped_len - 8];
                assert_eq!(kek.unwrap_padded(&wrapped, &mut unwrapped).unwrap(), key);
                wrapped[0] ^= 1;
                let mut ours_buf = vec![0xaa; wrapped_len - 8];
                let mut theirs_buf = ours_buf.clone();
                let result = kek.unwrap_padded(&wrapped, &mut ours_buf).map(|_| ());
                let expected = reference
                    .unwrap_padded(&wrapped, &mut theirs_buf)
                    .map(|_| ());
                assert_eq!(result, Err(Error::DecryptFailed));
                same(&result, &expected);
                assert_eq!(ours_buf, theirs_buf);
            }
            let wrapped = bytes("wrapped", len);
            for key_len in [len.saturating_sub(8), len] {
                let (mut ours_buf, mut theirs_buf) = (vec![0xaa; key_len], vec![0xaa; key_len]);
                let result = kek
                    .unwrap_padded(&wrapped, &mut ours_buf)
                    .map(|k| k.to_vec());
                let expected = reference
                    .unwrap_padded(&wrapped, &mut theirs_buf)
                    .map(|k| k.to_vec());
                same(&result, &expected);
                assert_eq!(result.ok(), expected.ok());
                assert_eq!(ours_buf, theirs_buf);
            }
        }
    }
}

#[test]
fn hkdf_derives_the_keys_rind_does() {
    let hkdfs = [
        (&hkdf::legacy::HKDF_SHA1, &rind::hkdf::legacy::HKDF_SHA1),
        (&hkdf::HKDF_SHA256, &rind::hkdf::HKDF_SHA256),
        (&hkdf::HKDF_SHA384, &rind::hkdf::HKDF_SHA384),
        (&hkdf::HKDF_SHA512, &rind::hkdf::HKDF_SHA512),
    ];
    let quics = [
        (&aead::quic::AES_128, &rind::aead::quic::AES_128),
        (&aead::quic::AES_256, &rind::aead::quic::AES_256),
    ];
    for (ours, theirs) in hkdfs {
        let prk = hkdf::Salt::new(ours, b"salt").extract(b"secret");
        let reference = rind::hkdf::Salt::new(theirs, b"salt").extract(b"secret");
        let (a, b) = (bytes("a", 10), bytes("b", 300));
        let infos: [&[&[u8]]; 3] = [&[], &[&a], &[&a, &b]];
        for info in infos {
            for (aead_ours, aead_theirs) in AEADS {
                let key = aead::Key::from(prk.expand(info, aead_ours));
                let reference_key = rind::aead::Key::from(reference.expand(info, aead_theirs));
                same_debug(&key, &reference_key);
                let mut sealed = b"hello".to_vec();
                reference_key
                    .seal_in_place_append_tag(
                        rind::aead::Nonce::assume_unique_for_key([7; 12]),
                        b"",
                        &mut sealed,
                    )
                    .unwrap();
                let nonce = aead::Nonce::assume_unique_for_key([7; 12]);
                assert_eq!(
                    key.open_in_place(nonce, b"", &mut sealed).unwrap(),
                    b"hello"
                );
            }
            for (quic_ours, quic_theirs) in quics {
                let key = aead::quic::HeaderProtectionKey::from(prk.expand(info, quic_ours));
                let reference_key = rind::aead::quic::HeaderProtectionKey::from(
                    reference.expand(info, quic_theirs),
                );
                same_debug(&key, &reference_key);
                let sample = [0x5a; 16];
                assert_eq!(key.mask(&sample), reference_key.mask(&sample));
            }
        }
    }
}
