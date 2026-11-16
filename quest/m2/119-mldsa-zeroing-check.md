# One ML-DSA zeroing check for all parameter sets

Difficulty: 2/10 (estimate)


## Goal

A single zeroing check covers every ML-DSA parameter set, and the document allowance is confirmed to fire.

## Plan

Fork PR #119, base `fork/mldsa-aws-lc-rs`, head `1a8e57ed`. Score 9/10, fork only.

- Optional low: assert that the document allowance fired.

## Related

- [ML-DSA parity harness](117-mldsa-parity-harness.md)
