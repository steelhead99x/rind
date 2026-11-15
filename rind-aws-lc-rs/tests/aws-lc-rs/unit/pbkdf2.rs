// Copyright 2015-2022 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use core::num::NonZeroU32;

use aws_lc_rs::pbkdf2;

#[test]
fn pbkdf2_coverage() {
    // Coverage sanity check.
    assert!(pbkdf2::PBKDF2_HMAC_SHA256 == pbkdf2::PBKDF2_HMAC_SHA256);
    assert!(pbkdf2::PBKDF2_HMAC_SHA256 != pbkdf2::PBKDF2_HMAC_SHA384);

    let iterations = NonZeroU32::new(100_u32).unwrap();
    for &alg in &[
        pbkdf2::PBKDF2_HMAC_SHA1,
        pbkdf2::PBKDF2_HMAC_SHA256,
        pbkdf2::PBKDF2_HMAC_SHA384,
        pbkdf2::PBKDF2_HMAC_SHA512,
    ] {
        let mut out = vec![0u8; 64];
        pbkdf2::derive(alg, iterations, b"salt", b"password", &mut out);

        let alg_clone = alg;
        let mut out2 = vec![0u8; 64];
        pbkdf2::derive(alg_clone, iterations, b"salt", b"password", &mut out2);
        assert_eq!(out, out2);
    }
}
