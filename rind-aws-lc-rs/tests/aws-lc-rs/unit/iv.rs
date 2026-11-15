// Copyright 2018 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::iv::FixedLength;

#[test]
fn test_size() {
    let fixed = FixedLength::from([0u8; 16]);
    assert_eq!(16, fixed.size());

    let array = [0u8; 12];
    let fixed = FixedLength::<12>::try_from(array.as_slice()).unwrap();
    assert_eq!(12, fixed.size());

    assert!(FixedLength::<16>::try_from(array.as_slice()).is_err());

    assert!(TryInto::<[u8; 12]>::try_into(fixed).is_ok());
}
