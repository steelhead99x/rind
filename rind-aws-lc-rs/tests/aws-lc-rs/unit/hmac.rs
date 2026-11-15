// Copyright 2015-2022 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::{hmac, rand};

// rind-aws-lc-rs: HMAC-SHA224 is not offered, and
// `hmac_internal_sign_too_small_buffer` is left out, as it calls aws-lc-rs's
// private `internal_sign`; `hmac_sign_to_buffer_too_small_test` covers it through
// `sign_to_buffer`.

#[test]
fn hmac_algorithm_properties() {
    assert_eq!(hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY.tag_len(), 20);
    assert_eq!(hmac::HMAC_SHA256.tag_len(), 32);
    assert_eq!(hmac::HMAC_SHA384.tag_len(), 48);
    assert_eq!(hmac::HMAC_SHA512.tag_len(), 64);
}

// Make sure that `Key::generate` and `verify_with_own_key` aren't
// completely wacky.
#[test]
pub fn hmac_signing_key_coverage() {
    const HELLO_WORLD_GOOD: &[u8] = b"hello, world";
    const HELLO_WORLD_BAD: &[u8] = b"hello, worle";

    let rng = rand::SystemRandom::new();

    for algorithm in &[
        hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
        hmac::HMAC_SHA256,
        hmac::HMAC_SHA384,
        hmac::HMAC_SHA512,
    ] {
        let key = hmac::Key::generate(*algorithm, &rng).unwrap();
        let tag = hmac::sign(&key, HELLO_WORLD_GOOD);
        println!("{key:?}");
        assert!(hmac::verify(&key, HELLO_WORLD_GOOD, tag.as_ref()).is_ok());
        assert!(hmac::verify(&key, HELLO_WORLD_BAD, tag.as_ref()).is_err());
    }
}

#[test]
fn hmac_coverage() {
    // Something would have gone horribly wrong for this to not pass, but we test this so our
    // coverage reports will look better.
    assert_ne!(hmac::HMAC_SHA256, hmac::HMAC_SHA384);

    for &alg in &[
        hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
        hmac::HMAC_SHA256,
        hmac::HMAC_SHA384,
        hmac::HMAC_SHA512,
    ] {
        // Clone after updating context with message, then check if the final Tag is the same.
        let key = hmac::Key::new(alg, &[0; 32]);
        let mut ctx = hmac::Context::with_key(&key);
        ctx.update(b"hello, world");
        let ctx_clone = ctx.clone();

        let orig_tag = ctx.sign();
        let clone_tag = ctx_clone.sign();
        assert_eq!(orig_tag.as_ref(), clone_tag.as_ref());
        assert_eq!(orig_tag.clone().as_ref(), clone_tag.as_ref());
    }
}

#[test]
fn hmac_sign_to_buffer_test() {
    let rng = rand::SystemRandom::new();

    for &algorithm in &[
        hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
        hmac::HMAC_SHA256,
        hmac::HMAC_SHA384,
        hmac::HMAC_SHA512,
    ] {
        let key = hmac::Key::generate(algorithm, &rng).unwrap();
        let data = b"hello, world";
        let tag_len = algorithm.tag_len();

        // Test with exact size buffer
        let mut output = vec![0u8; tag_len];
        let result = hmac::sign_to_buffer(&key, data, &mut output).unwrap();
        assert_eq!(result.len(), tag_len);

        // Verify the returned tag matches sign() and passes verify()
        let tag = hmac::sign(&key, data);
        assert_eq!(result, tag.as_ref());
        assert!(hmac::verify(&key, data, result).is_ok());

        // Verify the output buffer also matches sign() and passes verify()
        assert_eq!(output.as_slice(), tag.as_ref());
        assert!(hmac::verify(&key, data, output.as_slice()).is_ok());

        // Test with larger buffer
        let mut large_output = vec![0u8; tag_len + 10];
        let result2 = hmac::sign_to_buffer(&key, data, &mut large_output).unwrap();
        assert_eq!(result2.len(), tag_len);
        assert_eq!(result2, tag.as_ref());
        assert!(hmac::verify(&key, data, result2).is_ok());
        assert_eq!(&large_output[0..tag_len], tag.as_ref());
    }
}

#[test]
fn hmac_sign_to_buffer_too_small_test() {
    let key = hmac::Key::new(hmac::HMAC_SHA256, &[0; 32]);
    let data = b"hello";

    // Buffer too small should fail
    let mut small_buffer = vec![0u8; hmac::HMAC_SHA256.tag_len() - 1];
    assert!(hmac::sign_to_buffer(&key, data, &mut small_buffer).is_err());

    // Empty buffer should fail
    let mut empty_buffer = vec![];
    assert!(hmac::sign_to_buffer(&key, data, &mut empty_buffer).is_err());
}
