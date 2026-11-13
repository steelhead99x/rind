// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::cipher::{
    AES_128, AES_192, AES_256, Algorithm, DecryptingKey, DecryptionContext, EncryptingKey,
    EncryptionContext, OperatingMode, PaddedBlockDecryptingKey, PaddedBlockEncryptingKey,
    UnboundCipherKey,
};
use aws_lc_rs::error::Unspecified;
use aws_lc_rs::iv::{FixedLength, IV_LEN_128_BIT};

use crate::test::from_hex;

// rind-aws-lc-rs: rind offers no streaming cipher contexts, so the streaming
// tests generate nothing.
macro_rules! streaming_cipher_rt {
    ($($args:tt)*) => {};
}

macro_rules! streaming_cipher_kat {
    ($($args:tt)*) => {};
}

macro_rules! padded_cipher_kat {
    ($name:ident, $alg:expr, $mode:expr, $constructor:ident, $key:literal, $iv: literal, $plaintext:literal, $ciphertext:literal) => {
        #[test]
        fn $name() {
            let key = from_hex($key).unwrap();
            let input = from_hex($plaintext).unwrap();
            let expected_ciphertext = from_hex($ciphertext).unwrap();

            let iv = from_hex($iv).unwrap();
            let fixed_iv = FixedLength::try_from(iv.as_slice()).unwrap();
            let context = EncryptionContext::Iv128(fixed_iv);

            let unbound_key = UnboundCipherKey::new($alg, &key).unwrap();

            let encrypting_key = PaddedBlockEncryptingKey::$constructor(unbound_key).unwrap();
            assert_eq!($mode, encrypting_key.mode());
            assert_eq!($alg, encrypting_key.algorithm());
            let mut in_out = input.clone();
            let context = encrypting_key
                .less_safe_encrypt(&mut in_out, context)
                .unwrap();
            assert_eq!(expected_ciphertext.as_slice(), in_out.as_slice());

            let unbound_key2 = UnboundCipherKey::new($alg, &key).unwrap();
            let decrypting_key = PaddedBlockDecryptingKey::$constructor(unbound_key2).unwrap();
            assert_eq!($mode, decrypting_key.mode());
            assert_eq!($alg, decrypting_key.algorithm());
            let plaintext = decrypting_key.decrypt(&mut in_out, context).unwrap();
            assert_eq!(input.as_slice(), plaintext);
        }

        streaming_cipher_kat!(
            $name,
            $alg,
            $mode,
            $constructor,
            $key,
            $iv,
            $plaintext,
            $ciphertext,
            2,
            9
        );
    };
}

macro_rules! cipher_kat {
    ($name:ident, $alg:expr, $mode:expr, $constructor:ident, $key:literal, $iv: literal, $plaintext:literal, $ciphertext:literal) => {
        unpadded_cipher_kat!(
            $name,
            $alg,
            $mode,
            $constructor,
            $key,
            $iv,
            $plaintext,
            $ciphertext
        );

        streaming_cipher_kat!(
            $name,
            $alg,
            $mode,
            $constructor,
            $key,
            $iv,
            $plaintext,
            $ciphertext,
            2,
            9
        );
    };
}

macro_rules! unpadded_cipher_kat {
    ($name:ident, $alg:expr, $mode:expr, $constructor:ident, $key:literal, $iv: literal, $plaintext:literal, $ciphertext:literal) => {
        #[test]
        fn $name() {
            let key = from_hex($key).unwrap();
            let input = from_hex($plaintext).unwrap();
            let expected_ciphertext = from_hex($ciphertext).unwrap();

            let context = if $iv.len() == 0 {
                EncryptionContext::None
            } else {
                let iv = from_hex($iv).unwrap();
                let fixed_iv = FixedLength::try_from(iv.as_slice()).unwrap();
                EncryptionContext::Iv128(fixed_iv)
            };

            let unbound_key = UnboundCipherKey::new($alg, &key).unwrap();

            let encrypting_key = EncryptingKey::$constructor(unbound_key).unwrap();
            assert_eq!($mode, encrypting_key.mode());
            assert_eq!($alg, encrypting_key.algorithm());
            let mut in_out = input.clone();
            let context = encrypting_key
                .less_safe_encrypt(in_out.as_mut_slice(), context)
                .unwrap();
            assert_eq!(expected_ciphertext.as_slice(), in_out);

            let unbound_key2 = UnboundCipherKey::new($alg, &key).unwrap();
            let decrypting_key = DecryptingKey::$constructor(unbound_key2).unwrap();
            assert_eq!($mode, decrypting_key.mode());
            assert_eq!($alg, decrypting_key.algorithm());
            let plaintext = decrypting_key.decrypt(&mut in_out, context).unwrap();
            assert_eq!(input.as_slice(), plaintext);
        }
    };

    ($name:ident, $alg:expr, $mode:expr, $constructor:ident, $key:literal, $iv: literal, $plaintext:literal) => {
        #[test]
        fn $name() {
            let key = from_hex($key).unwrap();
            let input = from_hex($plaintext).unwrap();

            let context = if $iv.len() == 0 {
                EncryptionContext::None
            } else {
                let iv = from_hex($iv).unwrap();
                let fixed_iv = FixedLength::try_from(iv.as_slice()).unwrap();
                EncryptionContext::Iv128(fixed_iv)
            };

            let unbound_key = UnboundCipherKey::new($alg, &key).unwrap();

            let encrypting_key = EncryptingKey::$constructor(unbound_key).unwrap();
            assert_eq!($mode, encrypting_key.mode());
            assert_eq!($alg, encrypting_key.algorithm());
            let mut in_out = input.clone();
            encrypting_key
                .less_safe_encrypt(in_out.as_mut_slice(), context)
                .expect_err("expected encryption failure");
        }
    };
}

macro_rules! padded_cipher_rt {
    ($name:ident, $alg:expr, $mode:expr, $constructor:ident, $key:literal, $plaintext:literal) => {
        #[test]
        fn $name() {
            let key = from_hex($key).unwrap();
            let input = from_hex($plaintext).unwrap();
            let unbound_key = UnboundCipherKey::new($alg, &key).unwrap();

            let encrypting_key = PaddedBlockEncryptingKey::$constructor(unbound_key).unwrap();
            assert_eq!($mode, encrypting_key.mode());
            assert_eq!($alg, encrypting_key.algorithm());
            let mut in_out = input.clone();
            let context = encrypting_key.encrypt(&mut in_out).unwrap();

            let unbound_key2 = UnboundCipherKey::new($alg, &key).unwrap();
            let decrypting_key = PaddedBlockDecryptingKey::$constructor(unbound_key2).unwrap();
            assert_eq!($mode, decrypting_key.mode());
            assert_eq!($alg, decrypting_key.algorithm());
            let plaintext = decrypting_key.decrypt(&mut in_out, context).unwrap();
            assert_eq!(input.as_slice(), plaintext);
        }

        streaming_cipher_rt!($name, $alg, $mode, $constructor, $key, $plaintext, 2, 9);
    };
}

macro_rules! cipher_rt {
    ($name:ident, $alg:expr, $mode:expr, $constructor:ident, $key:literal, $plaintext:literal) => {
        #[test]
        fn $name() {
            let key = from_hex($key).unwrap();
            let input = from_hex($plaintext).unwrap();
            let unbound_key = UnboundCipherKey::new($alg, &key).unwrap();

            let encrypting_key = EncryptingKey::$constructor(unbound_key).unwrap();
            assert_eq!($mode, encrypting_key.mode());
            assert_eq!($alg, encrypting_key.algorithm());
            let mut in_out = input.clone();
            let context = encrypting_key.encrypt(in_out.as_mut_slice()).unwrap();

            let unbound_key2 = UnboundCipherKey::new($alg, &key).unwrap();
            let decrypting_key = DecryptingKey::$constructor(unbound_key2).unwrap();
            assert_eq!($mode, decrypting_key.mode());
            assert_eq!($alg, decrypting_key.algorithm());
            let plaintext = decrypting_key.decrypt(&mut in_out, context).unwrap();
            assert_eq!(input.as_slice(), plaintext);
        }
        streaming_cipher_rt!($name, $alg, $mode, $constructor, $key, $plaintext, 2, 9);
    };
}

padded_cipher_kat!(
    test_kat_aes_128_cbc_16_bytes,
    &AES_128,
    OperatingMode::CBC,
    cbc_pkcs7,
    "000102030405060708090a0b0c0d0e0f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddeeff",
    "69c4e0d86a7b0430d8cdb78070b4c55a9e978e6d16b086570ef794ef97984232"
);

padded_cipher_kat!(
    test_kat_aes_192_cbc_16_bytes,
    &AES_192,
    OperatingMode::CBC,
    cbc_pkcs7,
    "e08c15411774ec4a908b64eadc6ac4199c7cd453f3aaef53",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddeeff",
    "fc7f57e545e92c0a0b364c3086d49bf0f1a1a203743fbd8af828af46edca074d"
);

padded_cipher_kat!(
    test_kat_aes_256_cbc_15_bytes,
    &AES_256,
    OperatingMode::CBC,
    cbc_pkcs7,
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddee",
    "2ddfb635a651a43f582997966840ca0c"
);

cipher_kat!(
    test_kat_aes_128_ctr_16_bytes,
    &AES_128,
    OperatingMode::CTR,
    ctr,
    "000102030405060708090a0b0c0d0e0f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddeeff",
    "c6b01904c3da3df5e7d62bd96d153686"
);

cipher_kat!(
    test_kat_aes_192_ctr_16_bytes,
    &AES_192,
    OperatingMode::CTR,
    ctr,
    "cd62376d5ebb414917f0c78f05266433dc9192a1ec943300",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddeeff",
    "7f7d07cc05d0e31633fb59df5e34d2d6"
);

cipher_kat!(
    test_kat_aes_256_ctr_15_bytes,
    &AES_256,
    OperatingMode::CTR,
    ctr,
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddee",
    "f28122856e1cf9a7216a30d111f399"
);

cipher_kat!(
    test_kat_aes_128_ctr_15_bytes,
    &AES_128,
    OperatingMode::CTR,
    ctr,
    "244828580821c1652582c76e34d299f5",
    "093145d5af233f46072a5eb5adc11aa1",
    "3ee38cec171e6cf466bf0df98aa0e1",
    "bd7d928f60e3422d96b3f8cd614eb2"
);

cipher_kat!(
    test_kat_aes_192_ctr_15_bytes,
    &AES_192,
    OperatingMode::CTR,
    ctr,
    "25a39dbfd8034f71a81f9ceb55026e4037f8f6aa30ab44ce",
    "ffffffffffffffffffffffffffffff80",
    "3ee38cec171e6cf466bf0df98aa0e1",
    "56caf80166f076dfee89adc73b71e5"
);

cipher_kat!(
    test_kat_aes_256_ctr_15_bytes_2,
    &AES_256,
    OperatingMode::CTR,
    ctr,
    "0857db8240ea459bdf660b4cced66d1f2d3734ff2de7b81e92740e65e7cc6a1d",
    "f028ecb053f801102d11fccc9d303a27",
    "eca7285d19f3c20e295378460e8729",
    "b5098e5e788de6ac2f2098eb2fc6f8"
);

padded_cipher_kat!(
    test_kat_aes_128_cbc_15_bytes,
    &AES_128,
    OperatingMode::CBC,
    cbc_pkcs7,
    "053304bb3899e1d99db9d29343ea782d",
    "b5313560244a4822c46c2a0c9d0cf7fd",
    "a3e4c990356c01f320043c3d8d6f43",
    "ad96993f248bd6a29760ec7ccda95ee1"
);

padded_cipher_kat!(
    test_kat_aes_192_cbc_15_bytes,
    &AES_192,
    OperatingMode::CBC,
    cbc_pkcs7,
    "7001c487cc3e572cfc92f4d0e697d982e8856fdcc957da40",
    "b5313560244a4822c46c2a0c9d0cf7fd",
    "a3e4c990356c01f320043c3d8d6f43",
    "33549957df6ff5cf32ca59b42298f4d5"
);

padded_cipher_kat!(
    test_kat_aes_128_cbc_16_bytes_2,
    &AES_128,
    OperatingMode::CBC,
    cbc_pkcs7,
    "95af71f1c63e4a1d0b0b1a27fb978283",
    "89e40797dca70197ff87d3dbb0ef2802",
    "aece7b5e3c3df1ffc9802d2dfe296dc7",
    "301b5dab49fb11e919d0d39970d06739301919743304f23f3cbc67d28564b25b"
);

padded_cipher_kat!(
    test_kat_aes_256_cbc_16_bytes,
    &AES_256,
    OperatingMode::CBC,
    cbc_pkcs7,
    "d4a8206dcae01242f9db79a4ecfe277d0f7bb8ccbafd8f9809adb39f35aa9b41",
    "24f6076548fb9d93c8f7ed9f6e661ef9",
    "a39c1fdf77ea3e1f18178c0ec237c70a",
    "f1af484830a149ee0387b854d65fe87ca0e62efc1c8e6909d4b9ab8666470453"
);

padded_cipher_rt!(
    test_rt_aes_128_cbc_16_bytes,
    &AES_128,
    OperatingMode::CBC,
    cbc_pkcs7,
    "000102030405060708090a0b0c0d0e0f",
    "00112233445566778899aabbccddeeff"
);

padded_cipher_rt!(
    test_rt_aes_192_cbc_16_bytes,
    &AES_192,
    OperatingMode::CBC,
    cbc_pkcs7,
    "d2926527e0aa9f37b45e2ec2ade5853ef807576104c7ace3",
    "00112233445566778899aabbccddeeff"
);

padded_cipher_rt!(
    test_rt_aes_256_cbc_15_bytes,
    &AES_256,
    OperatingMode::CBC,
    cbc_pkcs7,
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
    "00112233445566778899aabbccddee"
);

cipher_rt!(
    test_rt_aes_128_ctr_16_bytes,
    &AES_128,
    OperatingMode::CTR,
    ctr,
    "000102030405060708090a0b0c0d0e0f",
    "00112233445566778899aabbccddeeff"
);

cipher_rt!(
    test_rt_aes_192_ctr_16_bytes,
    &AES_192,
    OperatingMode::CTR,
    ctr,
    "982215f4e173dfa0fcffe5d3da41c4812c7bcc8ed3540f93",
    "00112233445566778899aabbccddeeff"
);

cipher_rt!(
    test_rt_aes_128_ctr_17_bytes,
    &AES_128,
    OperatingMode::CTR,
    ctr,
    "000102030405060708090a0b0c0d0e0f",
    "00112233445566778899aabbccddeeff01"
);

cipher_rt!(
    test_rt_aes_192_ctr_17_bytes,
    &AES_192,
    OperatingMode::CTR,
    ctr,
    "98c6b8e01e379fbd14e61af6af891596583565f2a27d59e9",
    "00112233445566778899aabbccddeeff01"
);

cipher_rt!(
    test_rt_aes_256_ctr_15_bytes,
    &AES_256,
    OperatingMode::CTR,
    ctr,
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
    "00112233445566778899aabbccddee"
);

cipher_rt!(
    test_rt_aes_128_ctr_15_bytes,
    &AES_128,
    OperatingMode::CTR,
    ctr,
    "244828580821c1652582c76e34d299f5",
    "3ee38cec171e6cf466bf0df98aa0e1"
);

cipher_rt!(
    test_rt_aes_192_ctr_15_bytes,
    &AES_192,
    OperatingMode::CTR,
    ctr,
    "b3ad5cea1dddc214ca969ac35f37dae1a9a9d1528f89bb35",
    "3ee38cec171e6cf466bf0df98aa0e1"
);

cipher_rt!(
    test_rt_aes_256_ctr_15_bytes_2,
    &AES_256,
    OperatingMode::CTR,
    ctr,
    "0857db8240ea459bdf660b4cced66d1f2d3734ff2de7b81e92740e65e7cc6a1d",
    "eca7285d19f3c20e295378460e8729"
);

cipher_rt!(
    test_rt_aes_256_ctr_17_bytes,
    &AES_256,
    OperatingMode::CTR,
    ctr,
    "0857db8240ea459bdf660b4cced66d1f2d3734ff2de7b81e92740e65e7cc6a1d",
    "eca7285d19f3c20e295378460e872934"
);

padded_cipher_rt!(
    test_rt_aes_128_cbc_15_bytes,
    &AES_128,
    OperatingMode::CBC,
    cbc_pkcs7,
    "053304bb3899e1d99db9d29343ea782d",
    "a3e4c990356c01f320043c3d8d6f43"
);

padded_cipher_rt!(
    test_rt_aes_192_cbc_15_bytes,
    &AES_192,
    OperatingMode::CBC,
    cbc_pkcs7,
    "45899367c3132849763073c435a9288a766c8b9ec2308516",
    "a3e4c990356c01f320043c3d8d6f43"
);

padded_cipher_rt!(
    test_rt_aes_128_cbc_16_bytes_2,
    &AES_128,
    OperatingMode::CBC,
    cbc_pkcs7,
    "95af71f1c63e4a1d0b0b1a27fb978283",
    "aece7b5e3c3df1ffc9802d2dfe296dc7"
);

padded_cipher_rt!(
    test_rt_128_cbc_17_bytes,
    &AES_128,
    OperatingMode::CBC,
    cbc_pkcs7,
    "95af71f1c63e4a1d0b0b1a27fb978283",
    "aece7b5e3c3df1ffc9802d2dfe296dc734"
);

padded_cipher_rt!(
    test_rt_192_cbc_17_bytes,
    &AES_192,
    OperatingMode::CBC,
    cbc_pkcs7,
    "ec250e04c3903f602647b85a401a1ae7ca2f02f67fa4253e",
    "aece7b5e3c3df1ffc9802d2dfe296dc734"
);

padded_cipher_rt!(
    test_rt_aes_256_cbc_16_bytes,
    &AES_256,
    OperatingMode::CBC,
    cbc_pkcs7,
    "d4a8206dcae01242f9db79a4ecfe277d0f7bb8ccbafd8f9809adb39f35aa9b41",
    "a39c1fdf77ea3e1f18178c0ec237c70a"
);

padded_cipher_rt!(
    test_rt_aes_256_cbc_17_bytes,
    &AES_256,
    OperatingMode::CBC,
    cbc_pkcs7,
    "d4a8206dcae01242f9db79a4ecfe277d0f7bb8ccbafd8f9809adb39f35aa9b41",
    "a39c1fdf77ea3e1f18178c0ec237c70a34"
);

unpadded_cipher_kat!(
    test_kat_aes_128_cbc_16_bytes_raw,
    &AES_128,
    OperatingMode::CBC,
    cbc,
    "000102030405060708090a0b0c0d0e0f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddeeff",
    "69c4e0d86a7b0430d8cdb78070b4c55a"
);

unpadded_cipher_kat!(
    test_kat_aes_192_cbc_16_bytes_raw,
    &AES_192,
    OperatingMode::CBC,
    cbc,
    "e08c15411774ec4a908b64eadc6ac4199c7cd453f3aaef53",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddeeff",
    "fc7f57e545e92c0a0b364c3086d49bf0"
);

unpadded_cipher_kat!(
    test_kat_aes_256_cbc_16_bytes_raw,
    &AES_256,
    OperatingMode::CBC,
    cbc,
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddeeff",
    "8ea2b7ca516745bfeafc49904b496089"
);

unpadded_cipher_kat!(
    test_kat_aes_128_cbc_15_bytes_raw,
    &AES_128,
    OperatingMode::CBC,
    cbc,
    "000102030405060708090a0b0c0d0e0f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddee"
);

unpadded_cipher_kat!(
    test_kat_aes_192_cbc_15_bytes_raw,
    &AES_192,
    OperatingMode::CBC,
    cbc,
    "e08c15411774ec4a908b64eadc6ac4199c7cd453f3aaef53",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddee"
);

unpadded_cipher_kat!(
    test_kat_aes_256_cbc_15_bytes_raw,
    &AES_256,
    OperatingMode::CBC,
    cbc,
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
    "00000000000000000000000000000000",
    "00112233445566778899aabbccddee"
);

type DecryptingKeyConstructor = fn(UnboundCipherKey) -> Result<DecryptingKey, Unspecified>;
type DecryptionContextConstructor = fn() -> DecryptionContext;

/// Asserts that `DecryptingKey::decrypt` returns an error, rather than panicking,
/// for every `DecryptionContext` variant except `valid_context`. The valid
/// variant must be accepted, so the check cannot pass by rejecting everything.
fn assert_decrypt_validates_context(
    algorithm: &'static Algorithm,
    key_bytes: &[u8],
    modes: &[(DecryptingKeyConstructor, &str)],
) {
    let contexts: &[(&str, DecryptionContextConstructor)] = &[
        ("None", || DecryptionContext::None),
        ("Iv128", || {
            DecryptionContext::Iv128(FixedLength::from([0u8; IV_LEN_128_BIT]))
        }),
    ];
    for &(new_key, valid_context) in modes {
        let key = new_key(UnboundCipherKey::new(algorithm, key_bytes).unwrap()).unwrap();
        for &(context_name, new_context) in contexts {
            let mut in_out = vec![0u8; algorithm.block_len()];
            let result = key.decrypt(&mut in_out, new_context());
            assert_eq!(
                result.is_ok(),
                context_name == valid_context,
                "{algorithm:?} {:?} decrypt with {context_name} context",
                key.mode(),
            );
        }
    }
}

#[test]
fn test_decrypt_rejects_mismatched_context() {
    assert_decrypt_validates_context(
        &AES_128,
        &from_hex("000102030405060708090a0b0c0d0e0f").unwrap(),
        &[(DecryptingKey::cbc, "Iv128"), (DecryptingKey::ctr, "Iv128")],
    );
}
