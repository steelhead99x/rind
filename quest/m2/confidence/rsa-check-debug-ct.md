# [XS] rind-aws-lc-rs's RSA key check runs in constant time in debug builds too

## Goal

`admin/ctgrind`'s debug build of `rind-aws-lc-rs`'s `unbacked_key_consistency` test passes. Today memcheck flags `rsa_check::mul` (`rind-aws-lc-rs/src/rsa_check.rs`, the schoolbook product), where the debug build's overflow check on each `u128` `+` branches on secret RSA limbs. Release builds have no such check and already pass.

## Plan

Found 2026-11-28 by the PR restoring #324's documented gap, whose debug ctgrind run failed here identically on main. Recorded as a quest by the owner rather than fixed in that PR.

- The sum `out[i+j] + aj*bi + carry` cannot overflow a `u128` (at most (2^64−1) + (2^64−1)^2 + (2^64−1) = 2^128 − 1), so write those additions with `wrapping_add`, with a comment saying why it cannot wrap. Check the file's other arithmetic on secrets for the same debug-only branch.
- Verify with the debug and release ctgrind runs of `unbacked_key_consistency` and `unbacked_private_keys`, and `cargo test -p rind-aws-lc-rs`.
