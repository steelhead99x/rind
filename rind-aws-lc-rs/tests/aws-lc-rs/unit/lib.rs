// Copyright 2015-2016 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::init;

// rind-aws-lc-rs: `dump_error` is private, and `awslc_version` and
// `try_fips_self_test` are not offered, so their tests and checks are left out.

#[test]
fn test_init() {
    init();
}

#[test]
fn test_fips() {
    assert!({ aws_lc_rs::try_fips_mode().is_err() });
    // Re-enable with fixed test after upstream has merged RAGDOLL
    //assert!({ aws_lc_rs::try_fips_cpu_jitter_entropy().is_ok() });
}

#[test]
fn test_fips_version() {
    assert_eq!(aws_lc_rs::fips_version(), None);
}
