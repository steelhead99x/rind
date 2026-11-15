// Copyright 2015-2019 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::digest;

// rind-aws-lc-rs: the `max_input` tests are left out, as they build a
// `digest::Context` from its private fields.

#[test]
fn digest_coverage() {
    for alg in [
        &digest::SHA1_FOR_LEGACY_USE_ONLY,
        &digest::SHA256,
        &digest::SHA384,
        &digest::SHA512,
        &digest::SHA3_384,
        &digest::SHA3_512,
    ] {
        // Clone after updating context with message, then check if the final Digest is the same.
        let mut ctx = digest::Context::new(alg);
        ctx.update(b"hello, world");
        let ctx_clone = ctx.clone();
        assert_eq!(ctx_clone.algorithm(), ctx.algorithm());

        let orig_digest = ctx.finish();
        let clone_digest = ctx_clone.finish();
        assert_eq!(orig_digest.algorithm(), clone_digest.algorithm());
        assert_eq!(orig_digest.as_ref(), clone_digest.as_ref());
        assert_eq!(orig_digest.clone().as_ref(), clone_digest.as_ref());
    }
}
