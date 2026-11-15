// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::aead::{
    AES_128_GCM, AES_256_GCM, Aad, CHACHA20_POLY1305, Nonce, TlsProtocolId, TlsRecordOpeningKey,
    TlsRecordSealingKey,
};

use crate::test::from_hex;

const TEST_128_BIT_KEY: &[u8] = &[
    0xb0, 0x37, 0x9f, 0xf8, 0xfb, 0x8e, 0xa6, 0x31, 0xf4, 0x1c, 0xe6, 0x3e, 0xb5, 0xc5, 0x20, 0x7c,
];

const TEST_256_BIT_KEY: &[u8] = &[
    0x56, 0xd8, 0x96, 0x68, 0xbd, 0x96, 0xeb, 0xff, 0x5e, 0xa2, 0x0b, 0x34, 0xf2, 0x79, 0x84, 0x6e,
    0x2b, 0x13, 0x01, 0x3d, 0xab, 0x1d, 0xa4, 0x07, 0x5a, 0x16, 0xd5, 0x0b, 0x53, 0xb0, 0xcc, 0x88,
];

struct TlsNonceTestCase {
    nonce: &'static str,
    expect_err: bool,
}

const TLS_NONCE_TEST_CASES: &[TlsNonceTestCase] = &[
    TlsNonceTestCase {
        nonce: "9fab40177c900aad9fc28cc3",
        expect_err: false,
    },
    TlsNonceTestCase {
        nonce: "9fab40177c900aad9fc28cc4",
        expect_err: false,
    },
    TlsNonceTestCase {
        nonce: "9fab40177c900aad9fc28cc2",
        expect_err: true,
    },
];

macro_rules! test_tls_aead {
    ($name:ident, $alg:expr, $proto:expr, $key:expr) => {
        #[test]
        fn $name() {
            assert!(TlsRecordSealingKey::new($alg, $proto, $key).is_err());
            assert!(TlsRecordOpeningKey::new($alg, $proto, $key).is_err());
        }
    };
    ($name:ident, $alg:expr, $proto:expr, $key:expr, $expect_tag_len:expr, $expect_nonce_len:expr) => {
        #[test]
        fn $name() {
            let mut sealing_key = TlsRecordSealingKey::new($alg, $proto, $key).unwrap();

            let opening_key = TlsRecordOpeningKey::new($alg, $proto, $key).unwrap();

            for case in TLS_NONCE_TEST_CASES {
                let plaintext = from_hex("00112233445566778899aabbccddeeff").unwrap();

                assert_eq!($alg, sealing_key.algorithm());
                assert_eq!(*$expect_tag_len, $alg.tag_len());
                assert_eq!(*$expect_nonce_len, $alg.nonce_len());

                let mut in_out = Vec::from(plaintext.as_slice());

                let nonce = from_hex(case.nonce).unwrap();

                let nonce_bytes = nonce.as_slice();

                let result = sealing_key.seal_in_place_append_tag(
                    Nonce::try_assume_unique_for_key(nonce_bytes).unwrap(),
                    Aad::empty(),
                    &mut in_out,
                );

                match (result, case.expect_err) {
                    (Ok(()), true) => panic!("expected error for seal_in_place_append_tag"),
                    (Ok(()), false) => {}
                    (Err(_), true) => return,
                    (Err(e), false) => panic!("{e}"),
                }

                assert_ne!(plaintext, in_out[..plaintext.len()]);

                // copy ciphertext with prefix, to exercise `open_within`
                let mut offset_cipher_text = vec![1, 2, 3, 4];
                offset_cipher_text.extend_from_slice(&in_out);

                opening_key
                    .open_in_place(
                        Nonce::try_assume_unique_for_key(nonce_bytes).unwrap(),
                        Aad::empty(),
                        &mut in_out,
                    )
                    .unwrap();

                assert_eq!(plaintext, in_out[..plaintext.len()]);

                opening_key
                    .open_within(
                        Nonce::try_assume_unique_for_key(nonce_bytes).unwrap(),
                        Aad::empty(),
                        &mut offset_cipher_text,
                        4..,
                    )
                    .unwrap();
                assert_eq!(plaintext, offset_cipher_text[..plaintext.len()]);
            }
        }
    };
}

test_tls_aead!(
    test_aes_128_gcm_tls12,
    &AES_128_GCM,
    TlsProtocolId::TLS12,
    TEST_128_BIT_KEY,
    &16,
    &12
);
test_tls_aead!(
    test_aes_128_gcm_tls13,
    &AES_128_GCM,
    TlsProtocolId::TLS13,
    TEST_128_BIT_KEY,
    &16,
    &12
);
test_tls_aead!(
    test_aes_256_gcm_tls12,
    &AES_256_GCM,
    TlsProtocolId::TLS12,
    TEST_256_BIT_KEY,
    &16,
    &12
);
test_tls_aead!(
    test_aes_256_gcm_tls13,
    &AES_256_GCM,
    TlsProtocolId::TLS13,
    TEST_256_BIT_KEY,
    &16,
    &12
);
test_tls_aead!(
    test_chacha20_poly1305_tls12_tls_aead_unsupported,
    &CHACHA20_POLY1305,
    TlsProtocolId::TLS12,
    TEST_256_BIT_KEY
);
test_tls_aead!(
    test_chacha20_poly1305_tls13_tls_aead_unsupported,
    &CHACHA20_POLY1305,
    TlsProtocolId::TLS13,
    TEST_256_BIT_KEY
);
