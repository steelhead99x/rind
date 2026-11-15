// Copyright 2018 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#[test]
fn test_nonce_from_byte_array() {
    use aws_lc_rs::aead::Nonce;
    // rind-aws-lc-rs: `aead::nonce::IV_LEN` is private.
    const IV_LEN: usize = 16;
    let iv: [u8; IV_LEN] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let nonce = Nonce::from(&iv);

    assert_eq!(&[1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], nonce.as_ref());
}
