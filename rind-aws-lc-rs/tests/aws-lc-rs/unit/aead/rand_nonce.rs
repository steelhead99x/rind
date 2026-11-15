// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::aead::{AES_128_GCM, AES_256_GCM, Aad, CHACHA20_POLY1305, RandomizedNonceKey};

use crate::test::from_hex;

const TEST_128_BIT_KEY: &[u8] = &[
    0xb0, 0x37, 0x9f, 0xf8, 0xfb, 0x8e, 0xa6, 0x31, 0xf4, 0x1c, 0xe6, 0x3e, 0xb5, 0xc5, 0x20, 0x7c,
];

const TEST_256_BIT_KEY: &[u8] = &[
    0x56, 0xd8, 0x96, 0x68, 0xbd, 0x96, 0xeb, 0xff, 0x5e, 0xa2, 0x0b, 0x34, 0xf2, 0x79, 0x84, 0x6e,
    0x2b, 0x13, 0x01, 0x3d, 0xab, 0x1d, 0xa4, 0x07, 0x5a, 0x16, 0xd5, 0x0b, 0x53, 0xb0, 0xcc, 0x88,
];

macro_rules! test_randnonce {
    ($name:ident, $alg:expr, $key:expr) => {
        #[test]
        fn $name() {
            assert!(RandomizedNonceKey::new($alg, $key).is_err());
        }
    };
    ($name:ident, $alg:expr, $key:expr, $expect_tag_len:expr, $expect_nonce_len:expr) => {
        #[test]
        fn $name() {
            let plaintext = from_hex("00112233445566778899aabbccddeeff").unwrap();
            let rand_nonce_key = RandomizedNonceKey::new($alg, $key).unwrap();

            assert_eq!($alg, rand_nonce_key.algorithm());
            assert_eq!(*$expect_tag_len, $alg.tag_len());
            assert_eq!(*$expect_nonce_len, $alg.nonce_len());

            let mut in_out = Vec::from(plaintext.as_slice());

            let nonce = rand_nonce_key
                .seal_in_place_append_tag(Aad::empty(), &mut in_out)
                .unwrap();

            assert_ne!(plaintext, in_out[..plaintext.len()]);

            rand_nonce_key
                .open_in_place(nonce, Aad::empty(), &mut in_out)
                .unwrap();

            assert_eq!(plaintext, in_out[..plaintext.len()]);

            let mut in_out = Vec::from(plaintext.as_slice());

            let (nonce, tag) = rand_nonce_key
                .seal_in_place_separate_tag(Aad::empty(), &mut in_out)
                .unwrap();

            assert_ne!(plaintext, in_out[..plaintext.len()]);

            in_out.extend(tag.as_ref());

            rand_nonce_key
                .open_in_place(nonce, Aad::empty(), &mut in_out)
                .unwrap();

            assert_eq!(plaintext, in_out[..plaintext.len()]);
        }
    };
}

test_randnonce!(
    test_aes_128_gcm_randnonce,
    &AES_128_GCM,
    TEST_128_BIT_KEY,
    &16,
    &12
);
test_randnonce!(
    test_aes_256_gcm_randnonce,
    &AES_256_GCM,
    TEST_256_BIT_KEY,
    &16,
    &12
);

test_randnonce!(
    test_chacha20_poly1305_randnonce_unsupported,
    &CHACHA20_POLY1305,
    TEST_256_BIT_KEY
);
