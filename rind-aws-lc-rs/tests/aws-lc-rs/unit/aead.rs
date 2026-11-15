// Copyright 2015-2016 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::aead::nonce_sequence::Counter32Builder;
use aws_lc_rs::aead::{
    AES_128_GCM, Aad, BoundKey, LessSafeKey, NONCE_LEN, Nonce, OpeningKey, SealingKey, UnboundKey,
};

use crate::test::from_hex;

mod nonce;
mod nonce_sequence {
    mod counter32;
    mod counter64;
}
mod quic;
mod rand_nonce;
mod tls;
mod unbound_key;

#[test]
fn test_aes_128() {
    let key = from_hex("000102030405060708090a0b0c0d0e0f").unwrap();
    let og_nonce = from_hex("5bf11a0951f0bfc7ea5c9e58").unwrap();
    let plaintext = from_hex("00112233445566778899aabbccddeeff").unwrap();
    let unbound_key = UnboundKey::new(&AES_128_GCM, &key).unwrap();
    assert_eq!(&AES_128_GCM, unbound_key.algorithm());

    assert_eq!(16, AES_128_GCM.tag_len());
    assert_eq!(12, AES_128_GCM.nonce_len());

    let less_safe_key = LessSafeKey::new(unbound_key);

    let nonce: [u8; NONCE_LEN] = og_nonce.as_slice().try_into().unwrap();
    let mut in_out = Vec::from(plaintext.as_slice());

    // rind-aws-lc-rs: `Nonce`'s field is private, so the nonces here are built
    // with `Nonce::assume_unique_for_key`, which sets it.
    #[allow(deprecated)]
    less_safe_key
        // Test coverage for `seal_in_place`, which calls `seal_in_place_append_tag`.
        .seal_in_place(
            Nonce::assume_unique_for_key(nonce),
            Aad::empty(),
            &mut in_out,
        )
        .unwrap();

    let mut in_out_clone = in_out.clone();
    let nonce: [u8; NONCE_LEN] = og_nonce.as_slice().try_into().unwrap();
    assert!(
        less_safe_key
            .open_in_place(
                Nonce::assume_unique_for_key(nonce),
                Aad::from("test"),
                &mut in_out_clone
            )
            .is_err()
    );

    let mut in_out_clone = in_out.clone();
    let mut nonce: [u8; NONCE_LEN] = og_nonce.as_slice().try_into().unwrap();
    nonce[0] = 0;
    assert!(
        less_safe_key
            .open_in_place(
                Nonce::assume_unique_for_key(nonce),
                Aad::empty(),
                &mut in_out_clone
            )
            .is_err()
    );

    let nonce: [u8; NONCE_LEN] = og_nonce.as_slice().try_into().unwrap();
    less_safe_key
        .open_in_place(
            Nonce::assume_unique_for_key(nonce),
            Aad::empty(),
            &mut in_out,
        )
        .unwrap();

    assert_eq!(plaintext, in_out[..plaintext.len()]);
}

#[test]
fn debug_prepared_nonce() {
    let mut sk = SealingKey::new(
        UnboundKey::new(&AES_128_GCM, &[0u8; 16]).unwrap(),
        Counter32Builder::new().build(),
    );
    let mut ok = OpeningKey::new(
        UnboundKey::new(&AES_128_GCM, &[0u8; 16]).unwrap(),
        Counter32Builder::new().build(),
    );
    let so = sk.prepare_nonce().unwrap();
    let oo = ok.prepare_nonce().unwrap();
    assert_eq!("SealingKeyPreparedNonce { .. }", format!("{so:?}"));
    assert_eq!("OpeningKeyPreparedNonce { .. }", format!("{oo:?}"));
}

#[test]
fn debug_tag() {
    // rind-aws-lc-rs: `Tag`'s fields are private, so the tag comes from sealing.
    let key = LessSafeKey::new(UnboundKey::new(&AES_128_GCM, &[0u8; 16]).unwrap());
    let tag = key
        .seal_in_place_separate_tag(
            Nonce::assume_unique_for_key([0u8; NONCE_LEN]),
            Aad::empty(),
            &mut [],
        )
        .unwrap();
    assert_eq!("Tag", format!("{tag:?}"));
}
