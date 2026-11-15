// Copyright 2018 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::aead::quic::{Algorithm, HeaderProtectionKey};

use crate::test;

#[test]
fn test_types() {
    test::compile_time_assert_send::<Algorithm>();
    test::compile_time_assert_sync::<Algorithm>();

    test::compile_time_assert_send::<HeaderProtectionKey>();
    test::compile_time_assert_sync::<HeaderProtectionKey>();
}
