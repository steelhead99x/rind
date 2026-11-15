// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::aead::NonceSequence;
use aws_lc_rs::aead::nonce_sequence::Counter32Builder;

#[test]
fn test_counter32_identifier() {
    let mut cns = Counter32Builder::default()
        .identifier([0xA1, 0xB2, 0xC3, 0xD4, 0xA2, 0xB3, 0xC4, 0xD5])
        .counter(7)
        .build();
    assert_eq!(0, cns.generated());
    let nonce = cns.advance().unwrap();
    let nonce = nonce.as_ref();
    assert_eq!(8, cns.counter());
    assert_eq!(
        [0xA1, 0xB2, 0xC3, 0xD4, 0xA2, 0xB3, 0xC4, 0xD5],
        cns.identifier()
    );
    assert_eq!(u32::MAX, cns.limit());
    assert_eq!(1, cns.generated());
    assert_eq!(
        nonce,
        &[0xA1, 0xB2, 0xC3, 0xD4, 0xA2, 0xB3, 0xC4, 0xD5, 0, 0, 0, 7]
    );
    let nonce = cns.advance().unwrap();
    let nonce = nonce.as_ref();
    assert_eq!(2, cns.generated());
    assert_eq!(9, cns.counter());
    assert_eq!(
        [0xA1, 0xB2, 0xC3, 0xD4, 0xA2, 0xB3, 0xC4, 0xD5],
        cns.identifier()
    );
    assert_eq!(
        nonce,
        &[0xA1, 0xB2, 0xC3, 0xD4, 0xA2, 0xB3, 0xC4, 0xD5, 0, 0, 0, 8]
    );
}

#[test]
fn test_counter32() {
    let mut cns = Counter32Builder::new().counter(0x_4CB0_16EA_u32).build();
    let nonce = cns.advance().unwrap();
    let nonce = nonce.as_ref();
    assert_eq!(nonce, &[0, 0, 0, 0, 0, 0, 0, 0, 0x4C, 0xB0, 0x16, 0xEA]);
    let nonce = cns.advance().unwrap();
    let nonce = nonce.as_ref();
    assert_eq!(nonce, &[0, 0, 0, 0, 0, 0, 0, 0, 0x4C, 0xB0, 0x16, 0xEB]);
}

#[test]
fn test_counter32_int_id() {
    let mut cns = Counter32Builder::new()
        .counter(0x_6A_u32)
        .identifier(0x_7B_u64.to_be_bytes())
        .build();
    let nonce = cns.advance().unwrap();
    let nonce = nonce.as_ref();
    assert_eq!(nonce, &[0, 0, 0, 0, 0, 0, 0, 0x7B, 0, 0, 0, 0x6A]);
    let nonce = cns.advance().unwrap();
    let nonce = nonce.as_ref();
    assert_eq!(nonce, &[0, 0, 0, 0, 0, 0, 0, 0x7B, 0, 0, 0, 0x6B]);
}

#[test]
fn test_counter32_limit() {
    let mut cns = Counter32Builder::new().limit(1).build();
    assert_eq!(1, cns.limit());
    assert_eq!(0, cns.generated());
    let _nonce = cns.advance().unwrap();
    assert_eq!(1, cns.generated());
    assert!(cns.advance().is_err());
}
