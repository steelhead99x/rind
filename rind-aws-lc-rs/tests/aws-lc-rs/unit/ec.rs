// Copyright 2015-2016 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::encoding::{
    AsBigEndian, AsDer, EcPublicKeyCompressedBin, EcPublicKeyUncompressedBin, PublicKeyX509Der,
};
use aws_lc_rs::signature;
use aws_lc_rs::signature::{
    ECDSA_P256_SHA256_FIXED, ECDSA_P256_SHA256_FIXED_SIGNING, EcdsaKeyPair, KeyPair,
    UnparsedPublicKey,
};

use crate::test;
use crate::test::from_dirty_hex;

mod key_pair;

#[test]
fn test_from_pkcs8() {
    let input = from_dirty_hex(
        r"308187020100301306072a8648ce3d020106082a8648ce3d030107046d306b0201010420090460075f15d
        2a256248000fb02d83ad77593dde4ae59fc5e96142dffb2bd07a14403420004cf0d13a3a7577231ea1b66cf4
        021cd54f21f4ac4f5f2fdd28e05bc7d2bd099d1374cd08d2ef654d6f04498db462f73e0282058dd661a4c9b0
        437af3f7af6e724",
    );

    let result = EcdsaKeyPair::from_pkcs8(&ECDSA_P256_SHA256_FIXED_SIGNING, &input);
    assert!(result.is_ok());
    let key_pair = result.unwrap();
    assert_eq!(
        "EcdsaKeyPair { public_key: EcdsaPublicKey(\"04cf0d13a3a7577231ea1b66cf4021cd54f21f4ac4f5f2fdd28e05bc7d2bd099d1374cd08d2ef654d6f04498db462f73e0282058dd661a4c9b0437af3f7af6e724\") }",
        format!("{key_pair:?}")
    );
    assert_eq!(
        "EcdsaPrivateKey(ECDSA_P256)",
        format!("{:?}", key_pair.private_key())
    );
    let pub_key = key_pair.public_key();
    let der_pub_key: PublicKeyX509Der = pub_key.as_der().unwrap();

    assert_eq!(
        from_dirty_hex(
            r"3059301306072a8648ce3d020106082a8648ce3d03010703420004cf0d13a3a7577231ea1b66cf402
            1cd54f21f4ac4f5f2fdd28e05bc7d2bd099d1374cd08d2ef654d6f04498db462f73e0282058dd661a4c9
            b0437af3f7af6e724",
        )
        .as_slice(),
        der_pub_key.as_ref()
    );
}

#[test]
fn test_ecdsa_asn1_verify() {
    /*
            Curve = P-256
    Digest = SHA256
    Msg = ""
    Q = 0430345fd47ea21a11129be651b0884bfac698377611acc9f689458e13b9ed7d4b9d7599a68dcf125e7f31055ccb374cd04f6d6fd2b217438a63f6f667d50ef2f0
    Sig = 30440220341f6779b75e98bb42e01095dd48356cbf9002dc704ac8bd2a8240b88d3796c60220555843b1b4e264fe6ffe6e2b705a376c05c09404303ffe5d2711f3e3b3a010a1
    Result = P (0 )
             */

    let alg = &signature::ECDSA_P256_SHA256_ASN1;
    let msg = "";
    let public_key = from_dirty_hex(
        r"0430345fd47ea21a11129be651b0884bfac698377611acc9f689458e1
    3b9ed7d4b9d7599a68dcf125e7f31055ccb374cd04f6d6fd2b217438a63f6f667d50ef2f0",
    );
    let sig = from_dirty_hex(
        r"30440220341f6779b75e98bb42e01095dd48356cbf9002dc704ac8bd2a8240b8
    8d3796c60220555843b1b4e264fe6ffe6e2b705a376c05c09404303ffe5d2711f3e3b3a010a1",
    );
    let unparsed_pub_key = signature::UnparsedPublicKey::new(alg, &public_key);

    let actual_result = unparsed_pub_key.verify(msg.as_bytes(), &sig);
    assert!(actual_result.is_ok(), "Key: {}", test::to_hex(public_key));
}

#[test]
fn public_key_formats() {
    const MESSAGE: &[u8] = b"message to be signed";

    let key_pair = EcdsaKeyPair::generate(&ECDSA_P256_SHA256_FIXED_SIGNING).unwrap();
    let public_key = key_pair.public_key();
    let as_ref_bytes = public_key.as_ref();
    let compressed = AsBigEndian::<EcPublicKeyCompressedBin>::as_be_bytes(public_key).unwrap();
    let uncompressed = AsBigEndian::<EcPublicKeyUncompressedBin>::as_be_bytes(public_key).unwrap();
    let pub_x509 = AsDer::<PublicKeyX509Der>::as_der(public_key).unwrap();
    assert_eq!(as_ref_bytes, uncompressed.as_ref());
    assert_ne!(compressed.as_ref()[0], 0x04);

    let rng = aws_lc_rs::rand::SystemRandom::new();

    let signature = key_pair.sign(&rng, MESSAGE).unwrap();

    for pub_key_bytes in [
        as_ref_bytes,
        compressed.as_ref(),
        uncompressed.as_ref(),
        pub_x509.as_ref(),
    ] {
        UnparsedPublicKey::new(&ECDSA_P256_SHA256_FIXED, pub_key_bytes)
            .verify(MESSAGE, signature.as_ref())
            .unwrap();
    }
}
