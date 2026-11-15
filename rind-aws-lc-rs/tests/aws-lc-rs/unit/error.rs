// Copyright 2015-2021 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// These check `Error::description` and `cause`, which are deprecated.
#![allow(deprecated)]

use std::error::Error;

use aws_lc_rs::error::{KeyRejected, Unspecified};

use crate::test;

#[test]
fn display_unspecified() {
    let output = format!("{}", Unspecified);
    assert_eq!("Unspecified", output);
}

#[test]
fn unexpected_error() {
    let key_rejected = KeyRejected::from(());
    assert_eq!("UnexpectedError", key_rejected.description());

    let unspecified = Unspecified::from(key_rejected);
    assert_eq!("Unspecified", unspecified.description());

    #[allow(clippy::redundant_locals)]
    let unspecified = unspecified;
    assert_eq!("Unspecified", unspecified.description());
}

#[test]
fn std_error() {
    // rind-aws-lc-rs: the check of a `KeyRejected::wrong_algorithm()` is left
    // out, as that constructor is private.

    let unspecified = Unspecified;
    assert!(unspecified.cause().is_none());
    assert_eq!("Unspecified", unspecified.description());

    test::compile_time_assert_std_error_error::<KeyRejected>();
}
