// Copyright 2015 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::hkdf::{HKDF_SHA256, HKDF_SHA384, Salt};

#[test]
fn hkdf_coverage() {
    // Something would have gone horribly wrong for this to not pass, but we test this so our
    // coverage reports will look better.
    assert_ne!(HKDF_SHA256, HKDF_SHA384);
    assert_eq!("Algorithm(Algorithm(SHA256))", format!("{HKDF_SHA256:?}"));
}

#[test]
fn test_debug() {
    const SALT: &[u8; 32] = &[
        29, 113, 120, 243, 11, 202, 39, 222, 206, 81, 163, 184, 122, 153, 52, 192, 98, 195, 240,
        32, 34, 19, 160, 128, 178, 111, 97, 232, 113, 101, 221, 143,
    ];
    const SECRET1: &[u8; 32] = &[
        157, 191, 36, 107, 110, 131, 193, 6, 175, 226, 193, 3, 168, 133, 165, 181, 65, 120, 194,
        152, 31, 92, 37, 191, 73, 222, 41, 112, 207, 236, 196, 174,
    ];

    const INFO1: &[&[u8]] = &[
        &[
            2, 130, 61, 83, 192, 248, 63, 60, 211, 73, 169, 66, 101, 160, 196, 212, 250, 113,
        ],
        &[
            80, 46, 248, 123, 78, 204, 171, 178, 67, 204, 96, 27, 131, 24,
        ],
    ];

    let alg = HKDF_SHA256;
    let salt = Salt::new(alg, SALT);
    let prk = salt.extract(SECRET1);
    let okm = prk.expand(INFO1, alg).unwrap();

    assert_eq!(
        "hkdf::Salt { algorithm: Algorithm(SHA256) }",
        format!("{salt:?}")
    );
    assert_eq!(
        "hkdf::Prk { algorithm: Algorithm(SHA256), mode: ExtractExpand { .. } }",
        format!("{prk:?}")
    );
    assert_eq!(
        "hkdf::Okm { prk: hkdf::Prk { algorithm: Algorithm(SHA256), mode: ExtractExpand { .. } } }",
        format!("{okm:?}")
    );
}

#[test]
fn test_salt_none_matches_empty_salt() {
    let none = Salt::none(HKDF_SHA256);
    let empty = Salt::new(HKDF_SHA256, &[]);
    let secret = b"input keying material";
    let info = [b"context".as_slice()];

    let prk_none = none.extract(secret);
    let prk_empty = empty.extract(secret);

    let mut out_none = [0u8; 32];
    let mut out_empty = [0u8; 32];
    prk_none
        .expand(&info, HKDF_SHA256)
        .unwrap()
        .fill(&mut out_none)
        .unwrap();
    prk_empty
        .expand(&info, HKDF_SHA256)
        .unwrap()
        .fill(&mut out_empty)
        .unwrap();

    // RFC 5869: a missing/empty salt is equivalent to HashLen zero bytes;
    // the two constructors must produce identical PRKs (and thus OKMs).
    assert_eq!(out_none, out_empty);
}

#[test]
fn test_long_salt() {
    // Test with a salt longer than the previous 80-byte limit
    let long_salt = vec![0x42u8; 100];

    // This should work now that we removed the MAX_HKDF_SALT_LEN restriction
    let salt = Salt::new(HKDF_SHA256, &long_salt);

    // Test the extract operation still works
    let secret = b"test secret key material";
    let prk = salt.extract(secret);

    // Test expand operation
    let info_data = b"test context info";
    let info = [info_data.as_slice()];
    let okm = prk.expand(&info, HKDF_SHA256).unwrap();

    // Fill output buffer
    let mut output = [0u8; 32];
    okm.fill(&mut output).unwrap();

    // Test with an even longer salt to demonstrate flexibility
    let very_long_salt = vec![0x55u8; 500];
    let very_long_salt_obj = Salt::new(HKDF_SHA256, &very_long_salt);
    let prk2 = very_long_salt_obj.extract(secret);
    let okm2 = prk2.expand(&info, HKDF_SHA256).unwrap();
    let mut output2 = [0u8; 32];
    okm2.fill(&mut output2).unwrap();

    // Verify outputs are different (they should be due to different salts)
    assert_ne!(output, output2);
}
