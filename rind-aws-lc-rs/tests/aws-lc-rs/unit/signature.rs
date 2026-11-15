// Copyright 2015-2017 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::rand::{SystemRandom, generate};
use aws_lc_rs::signature::{ED25519, ParsedPublicKey, UnparsedPublicKey};

use crate::test;

mod parsed_public_key_tests;

#[test]
fn test_unparsed_public_key() {
    let random_pubkey: [u8; 32] = generate(&SystemRandom::new()).unwrap().expose();
    let unparsed_pubkey = UnparsedPublicKey::new(&ED25519, random_pubkey);
    let unparsed_pubkey_debug = format!("{unparsed_pubkey:?}");

    #[allow(clippy::clone_on_copy)]
    let unparsed_pubkey_clone = unparsed_pubkey.clone();
    assert_eq!(unparsed_pubkey_debug, format!("{unparsed_pubkey_clone:?}"));
    // rind-aws-lc-rs: matched without the `regex` crate.
    let pubkey_hex = unparsed_pubkey_debug
        .strip_prefix("UnparsedPublicKey { algorithm: EdDSAParameters, bytes: \"")
        .and_then(|rest| rest.strip_suffix("\" }"));
    assert!(pubkey_hex.is_some_and(|hex| hex.len() == 64 && crate::unit::is_lower_hex(hex)));
}
#[test]
fn test_types() {
    test::compile_time_assert_send::<UnparsedPublicKey<&[u8]>>();
    test::compile_time_assert_sync::<UnparsedPublicKey<&[u8]>>();
    test::compile_time_assert_send::<UnparsedPublicKey<Vec<u8>>>();
    test::compile_time_assert_sync::<UnparsedPublicKey<Vec<u8>>>();
    test::compile_time_assert_clone::<UnparsedPublicKey<&[u8]>>();
    test::compile_time_assert_clone::<UnparsedPublicKey<Vec<u8>>>();
    test::compile_time_assert_send::<ParsedPublicKey>();
    test::compile_time_assert_sync::<ParsedPublicKey>();
    test::compile_time_assert_clone::<ParsedPublicKey>();
}
