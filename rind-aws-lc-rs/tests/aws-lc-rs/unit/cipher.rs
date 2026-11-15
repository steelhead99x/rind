// Copyright 2018 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::cipher::{
    AES_128, AES_256, Algorithm, DecryptingKey, DecryptionContext, EncryptingKey,
    EncryptionContext, OperatingMode, PaddedBlockDecryptingKey, PaddedBlockEncryptingKey,
    UnboundCipherKey,
};
use aws_lc_rs::error::Unspecified;
use aws_lc_rs::iv::FixedLength;

use crate::test::from_hex;

mod padded;

// rind-aws-lc-rs: `EncryptingKey::new` and `DecryptingKey::new` are private, so
// these call the public constructor for each mode, which calls them.
fn encrypting_key(
    key: UnboundCipherKey,
    mode: OperatingMode,
) -> Result<EncryptingKey, Unspecified> {
    match mode {
        OperatingMode::CBC => EncryptingKey::cbc(key),
        OperatingMode::CTR => EncryptingKey::ctr(key),
        _ => unreachable!("{mode:?}"),
    }
}

fn decrypting_key(
    key: UnboundCipherKey,
    mode: OperatingMode,
) -> Result<DecryptingKey, Unspecified> {
    match mode {
        OperatingMode::CBC => DecryptingKey::cbc(key),
        OperatingMode::CTR => DecryptingKey::ctr(key),
        _ => unreachable!("{mode:?}"),
    }
}

#[test]
fn test_debug() {
    {
        let aes_128_key_bytes = from_hex("000102030405060708090a0b0c0d0e0f").unwrap();
        let cipher_key = UnboundCipherKey::new(&AES_128, aes_128_key_bytes.as_slice()).unwrap();
        assert_eq!(
            "UnboundCipherKey { algorithm: Algorithm { id: Aes128, key_len: 16, block_len: 16 } }",
            format!("{cipher_key:?}")
        );
    }

    {
        let aes_256_key_bytes =
            from_hex("000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f").unwrap();
        let cipher_key = UnboundCipherKey::new(&AES_256, aes_256_key_bytes.as_slice()).unwrap();
        assert_eq!(
            "UnboundCipherKey { algorithm: Algorithm { id: Aes256, key_len: 32, block_len: 16 } }",
            format!("{cipher_key:?}")
        );
    }

    {
        let key_bytes = &[0u8; 16];
        let key = PaddedBlockEncryptingKey::cbc_pkcs7(
            UnboundCipherKey::new(&AES_128, key_bytes).unwrap(),
        )
        .unwrap();
        assert_eq!(
            "PaddedBlockEncryptingKey { algorithm: Algorithm { id: Aes128, key_len: 16, block_len: 16 }, mode: CBC, padding: PKCS7, .. }",
            format!("{key:?}")
        );
        let mut data = vec![0u8; 16];
        let context = key.encrypt(&mut data).unwrap();
        assert_eq!("Iv128", format!("{context:?}"));
        let key = PaddedBlockDecryptingKey::cbc_pkcs7(
            UnboundCipherKey::new(&AES_128, key_bytes).unwrap(),
        )
        .unwrap();
        assert_eq!(
            "PaddedBlockDecryptingKey { algorithm: Algorithm { id: Aes128, key_len: 16, block_len: 16 }, mode: CBC, padding: PKCS7, .. }",
            format!("{key:?}")
        );
    }

    {
        let key_bytes = &[0u8; 16];
        let key = EncryptingKey::ctr(UnboundCipherKey::new(&AES_128, key_bytes).unwrap()).unwrap();
        assert_eq!(
            "EncryptingKey { algorithm: Algorithm { id: Aes128, key_len: 16, block_len: 16 }, mode: CTR, .. }",
            format!("{key:?}")
        );
        let mut data = vec![0u8; 16];
        let context = key.encrypt(&mut data).unwrap();
        assert_eq!("Iv128", format!("{context:?}"));
        let key = DecryptingKey::ctr(UnboundCipherKey::new(&AES_128, key_bytes).unwrap()).unwrap();
        assert_eq!(
            "DecryptingKey { algorithm: Algorithm { id: Aes128, key_len: 16, block_len: 16 }, mode: CTR, .. }",
            format!("{key:?}")
        );
    }
}

fn helper_test_cipher_n_bytes(key: &[u8], alg: &'static Algorithm, mode: OperatingMode, n: usize) {
    let mut input: Vec<u8> = Vec::with_capacity(n);
    for i in 0..n {
        let byte: u8 = i.try_into().unwrap();
        input.push(byte);
    }

    let cipher_key = UnboundCipherKey::new(alg, key).unwrap();
    let encrypting_key = encrypting_key(cipher_key, mode).unwrap();

    let mut in_out = input.clone();
    let decrypt_iv = encrypting_key.encrypt(&mut in_out).unwrap();

    if n > 5 {
        // There's no more than a 1 in 2^48 chance that this will fail randomly
        assert_ne!(input.as_slice(), in_out);
    }

    let cipher_key2 = UnboundCipherKey::new(alg, key).unwrap();
    let decrypting_key = decrypting_key(cipher_key2, mode).unwrap();

    let plaintext = decrypting_key.decrypt(&mut in_out, decrypt_iv).unwrap();
    assert_eq!(input.as_slice(), plaintext);
}

#[test]
fn test_aes_128_ctr() {
    let key = from_hex("000102030405060708090a0b0c0d0e0f").unwrap();
    for i in 0..=50 {
        helper_test_cipher_n_bytes(key.as_slice(), &AES_128, OperatingMode::CTR, i);
    }
}

#[test]
fn test_aes_256_ctr() {
    let key = from_hex("000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f").unwrap();
    for i in 0..=50 {
        helper_test_cipher_n_bytes(key.as_slice(), &AES_256, OperatingMode::CTR, i);
    }
}

#[test]
fn test_aes_128_cbc() {
    let key = from_hex("000102030405060708090a0b0c0d0e0f").unwrap();
    // CBC mode requires input to be a multiple of block size (16 bytes)
    for i in 0..=3 {
        let size = i * 16; // Test with 0, 16, 32, 48 bytes
        helper_test_cipher_n_bytes(key.as_slice(), &AES_128, OperatingMode::CBC, size);
    }
}

#[test]
fn test_aes_256_cbc() {
    let key = from_hex("000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f").unwrap();
    // CBC mode requires input to be a multiple of block size (16 bytes)
    for i in 0..=3 {
        let size = i * 16; // Test with 0, 16, 32, 48 bytes
        helper_test_cipher_n_bytes(key.as_slice(), &AES_256, OperatingMode::CBC, size);
    }
}

macro_rules! cipher_kat {
    ($name:ident, $alg:expr, $mode:expr, $key:literal, $iv: literal, $plaintext:literal, $ciphertext:literal) => {
        #[test]
        fn $name() {
            let key = from_hex($key).unwrap();
            let input = from_hex($plaintext).unwrap();
            let expected_ciphertext = from_hex($ciphertext).unwrap();
            let mut iv = from_hex($iv).unwrap();
            let iv = {
                let slice = iv.as_mut_slice();
                let mut iv = [0u8; $iv.len() / 2];
                {
                    let x = iv.as_mut_slice();
                    x.copy_from_slice(slice);
                }
                iv
            };

            let ec = EncryptionContext::Iv128(FixedLength::from(iv));

            let alg = $alg;

            let unbound_key = UnboundCipherKey::new(alg, &key).unwrap();

            let encrypting_key = encrypting_key(unbound_key, $mode).unwrap();

            let mut in_out = input.clone();

            let context = encrypting_key.less_safe_encrypt(&mut in_out, ec).unwrap();

            assert_eq!(expected_ciphertext, in_out);

            let unbound_key2 = UnboundCipherKey::new(alg, &key).unwrap();
            let decrypting_key = decrypting_key(unbound_key2, $mode).unwrap();

            let plaintext = decrypting_key.decrypt(&mut in_out, context).unwrap();
            assert_eq!(input.as_slice(), plaintext);
        }
    };
    ($name:ident, $alg:expr, $mode:expr, $key:literal, $plaintext:literal, $ciphertext:literal) => {
        #[test]
        fn $name() {
            let key = from_hex($key).unwrap();
            let input = from_hex($plaintext).unwrap();
            let expected_ciphertext = from_hex($ciphertext).unwrap();

            let alg = $alg;

            let unbound_key = UnboundCipherKey::new(alg, &key).unwrap();

            let encrypting_key = encrypting_key(unbound_key, $mode).unwrap();

            let mut in_out = input.clone();

            let context = encrypting_key
                .less_safe_encrypt(&mut in_out, EncryptionContext::None)
                .unwrap();

            assert_eq!(expected_ciphertext, in_out);

            let unbound_key2 = UnboundCipherKey::new(alg, &key).unwrap();
            let decrypting_key = decrypting_key(unbound_key2, $mode).unwrap();

            let plaintext = decrypting_key.decrypt(&mut in_out, context).unwrap();
            assert_eq!(input.as_slice(), plaintext);
        }
    };
}

cipher_kat!(
    test_iv_aes_128_ctr_16_bytes,
    &AES_128,
    OperatingMode::CTR,
    "000102030405060708090a0b0c0d0e0f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddeeff",
    "c6b01904c3da3df5e7d62bd96d153686"
);

cipher_kat!(
    test_iv_aes_256_ctr_15_bytes,
    &AES_256,
    OperatingMode::CTR,
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddee",
    "f28122856e1cf9a7216a30d111f399"
);

cipher_kat!(
    test_openssl_aes_128_ctr_15_bytes,
    &AES_128,
    OperatingMode::CTR,
    "244828580821c1652582c76e34d299f5",
    "093145d5af233f46072a5eb5adc11aa1",
    "3ee38cec171e6cf466bf0df98aa0e1",
    "bd7d928f60e3422d96b3f8cd614eb2"
);

cipher_kat!(
    test_openssl_aes_256_ctr_15_bytes,
    &AES_256,
    OperatingMode::CTR,
    "0857db8240ea459bdf660b4cced66d1f2d3734ff2de7b81e92740e65e7cc6a1d",
    "f028ecb053f801102d11fccc9d303a27",
    "eca7285d19f3c20e295378460e8729",
    "b5098e5e788de6ac2f2098eb2fc6f8"
);

cipher_kat!(
    test_sp800_38a_cbc_aes128,
    &AES_128,
    OperatingMode::CBC,
    "2b7e151628aed2a6abf7158809cf4f3c",
    "000102030405060708090a0b0c0d0e0f",
    "6bc1bee22e409f96e93d7e117393172a",
    "7649abac8119b246cee98e9b12e9197d"
);

cipher_kat!(
    test_sp800_38a_cbc_aes256,
    &AES_256,
    OperatingMode::CBC,
    "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4",
    "000102030405060708090a0b0c0d0e0f",
    "6bc1bee22e409f96e93d7e117393172a",
    "f58c4c04d6e5f1ba779eabfb5f7bfbd6"
);

cipher_kat!(
    test_sp800_38a_cbc_aes128_multi_block,
    &AES_128,
    OperatingMode::CBC,
    "2b7e151628aed2a6abf7158809cf4f3c",
    "000102030405060708090a0b0c0d0e0f",
    "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710",
    "7649abac8119b246cee98e9b12e9197d5086cb9b507219ee95db113a917678b273bed6b8e3c1743b7116e69e222295163ff1caa1681fac09120eca307586e1a7"
);

cipher_kat!(
    test_sp800_38a_cbc_aes256_multi_block,
    &AES_256,
    OperatingMode::CBC,
    "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4",
    "000102030405060708090a0b0c0d0e0f",
    "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710",
    "f58c4c04d6e5f1ba779eabfb5f7bfbd69cfc4e967edb808d679f777bc6702c7d39f23369a9d9bacfa530e26304231461b2eb05e2c39be9fcda6c19078c6a9d1b"
);

#[test]
fn test_decrypting_key_rejects_invalid_context() {
    type Constructor = fn(UnboundCipherKey) -> Result<DecryptingKey, Unspecified>;
    let key = || UnboundCipherKey::new(&AES_128, &[0u8; 16]).unwrap();
    let iv_modes: [(&str, Constructor); 2] =
        [("CBC", DecryptingKey::cbc), ("CTR", DecryptingKey::ctr)];
    for (name, constructor) in iv_modes {
        let decrypting_key = constructor(key()).unwrap();
        let mut in_out = [0u8; 16];
        assert!(
            decrypting_key
                .decrypt(&mut in_out, DecryptionContext::None)
                .is_err(),
            "AES + {name} + DecryptionContext::None should be rejected"
        );
    }
}
