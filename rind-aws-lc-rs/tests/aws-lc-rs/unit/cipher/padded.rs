// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::cipher::{
    AES_128, AES_256, Algorithm, EncryptionContext, OperatingMode, PaddedBlockDecryptingKey,
    PaddedBlockEncryptingKey, UnboundCipherKey,
};
use aws_lc_rs::error::Unspecified;
use aws_lc_rs::iv::FixedLength;

use crate::test::from_hex;

// rind-aws-lc-rs: `PaddingStrategy` and the keys' `new` are private, so these
// call the public constructor for each mode and padding, which calls `new`.
// ISO 10126 padding is not offered.
#[derive(Clone, Copy, PartialEq)]
enum PaddingStrategy {
    PKCS7,
}

fn padded_encrypting_key(
    key: UnboundCipherKey,
    mode: OperatingMode,
    PaddingStrategy::PKCS7: PaddingStrategy,
) -> Result<PaddedBlockEncryptingKey, Unspecified> {
    match mode {
        OperatingMode::CBC => PaddedBlockEncryptingKey::cbc_pkcs7(key),
        _ => unreachable!("{mode:?}"),
    }
}

fn padded_decrypting_key(
    key: UnboundCipherKey,
    mode: OperatingMode,
    PaddingStrategy::PKCS7: PaddingStrategy,
) -> Result<PaddedBlockDecryptingKey, Unspecified> {
    match mode {
        OperatingMode::CBC => PaddedBlockDecryptingKey::cbc_pkcs7(key),
        _ => unreachable!("{mode:?}"),
    }
}

fn helper_test_padded_cipher_n_bytes(
    key: &[u8],
    alg: &'static Algorithm,
    mode: OperatingMode,
    padding: PaddingStrategy,
    n: usize,
) {
    let mut input: Vec<u8> = Vec::with_capacity(n);
    for i in 0..n {
        let byte: u8 = i.try_into().unwrap();
        input.push(byte);
    }

    let cipher_key = UnboundCipherKey::new(alg, key).unwrap();
    let encrypting_key = padded_encrypting_key(cipher_key, mode, padding).unwrap();

    let mut in_out = input.clone();
    let decrypt_iv = encrypting_key.encrypt(&mut in_out).unwrap();

    if n > 5 {
        // There's no more than a 1 in 2^48 chance that this will fail randomly
        assert_ne!(input.as_slice(), in_out);
    }

    let cipher_key2 = UnboundCipherKey::new(alg, key).unwrap();
    let decrypting_key = padded_decrypting_key(cipher_key2, mode, padding).unwrap();

    let plaintext = decrypting_key.decrypt(&mut in_out, decrypt_iv).unwrap();
    assert_eq!(input.as_slice(), plaintext);
}

#[test]
fn test_aes_128_cbc() {
    let key = from_hex("000102030405060708090a0b0c0d0e0f").unwrap();
    for i in 0..=50 {
        helper_test_padded_cipher_n_bytes(
            key.as_slice(),
            &AES_128,
            OperatingMode::CBC,
            PaddingStrategy::PKCS7,
            i,
        );
    }
}

#[test]
fn test_aes_256_cbc() {
    let key = from_hex("000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f").unwrap();
    for i in 0..=50 {
        helper_test_padded_cipher_n_bytes(
            key.as_slice(),
            &AES_256,
            OperatingMode::CBC,
            PaddingStrategy::PKCS7,
            i,
        );
    }
}

macro_rules! padded_cipher_kat {
    ($name:ident, $alg:expr, $mode:expr, $padding:expr, $key:literal, $iv: literal, $plaintext:literal, $ciphertext:literal) => {
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

            let encrypting_key = padded_encrypting_key(unbound_key, $mode, $padding).unwrap();

            let mut in_out = input.clone();

            let context = encrypting_key.less_safe_encrypt(&mut in_out, ec).unwrap();

            assert_eq!(expected_ciphertext, in_out);

            let unbound_key2 = UnboundCipherKey::new(alg, &key).unwrap();
            let decrypting_key = padded_decrypting_key(unbound_key2, $mode, $padding).unwrap();

            let plaintext = decrypting_key.decrypt(&mut in_out, context).unwrap();
            assert_eq!(input.as_slice(), plaintext);
        }
    };
}

padded_cipher_kat!(
    test_iv_aes_128_cbc_16_bytes,
    &AES_128,
    OperatingMode::CBC,
    PaddingStrategy::PKCS7,
    "000102030405060708090a0b0c0d0e0f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddeeff",
    "69c4e0d86a7b0430d8cdb78070b4c55a9e978e6d16b086570ef794ef97984232"
);

padded_cipher_kat!(
    test_iv_aes_256_cbc_15_bytes,
    &AES_256,
    OperatingMode::CBC,
    PaddingStrategy::PKCS7,
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddee",
    "2ddfb635a651a43f582997966840ca0c"
);

padded_cipher_kat!(
    test_openssl_aes_128_cbc_15_bytes,
    &AES_128,
    OperatingMode::CBC,
    PaddingStrategy::PKCS7,
    "053304bb3899e1d99db9d29343ea782d",
    "b5313560244a4822c46c2a0c9d0cf7fd",
    "a3e4c990356c01f320043c3d8d6f43",
    "ad96993f248bd6a29760ec7ccda95ee1"
);

padded_cipher_kat!(
    test_openssl_aes_128_cbc_16_bytes,
    &AES_128,
    OperatingMode::CBC,
    PaddingStrategy::PKCS7,
    "95af71f1c63e4a1d0b0b1a27fb978283",
    "89e40797dca70197ff87d3dbb0ef2802",
    "aece7b5e3c3df1ffc9802d2dfe296dc7",
    "301b5dab49fb11e919d0d39970d06739301919743304f23f3cbc67d28564b25b"
);

padded_cipher_kat!(
    test_openssl_aes_256_cbc_15_bytes,
    &AES_256,
    OperatingMode::CBC,
    PaddingStrategy::PKCS7,
    "d369e03e9752784917cc7bac1db7399598d9555e691861d9dd7b3292a693ef57",
    "1399bb66b2f6ad99a7f064140eaaa885",
    "7385f5784b85bf0a97768ddd896d6d",
    "4351082bac9b4593ae8848cc9dfb5a01"
);

padded_cipher_kat!(
    test_openssl_aes_256_cbc_16_bytes,
    &AES_256,
    OperatingMode::CBC,
    PaddingStrategy::PKCS7,
    "d4a8206dcae01242f9db79a4ecfe277d0f7bb8ccbafd8f9809adb39f35aa9b41",
    "24f6076548fb9d93c8f7ed9f6e661ef9",
    "a39c1fdf77ea3e1f18178c0ec237c70a",
    "f1af484830a149ee0387b854d65fe87ca0e62efc1c8e6909d4b9ab8666470453"
);
