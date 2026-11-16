# [S] Fix the ML-DSA seed-tail parity test

## Goal

https://github.com/steelhead99x/rind/pull/117's `mldsa_seed_tail` parity test passes, and the harness stays in agreement with the reference on that path.

## Plan

The `mldsa_seed_tail` test was already failing before the merge of the signature API change. Reproduce it on the current branch, fix the harness or the mapping that makes it fail, and keep the rest of the parity coverage.

## Related

- [Decide ML-DSA wipe and refusal error mapping, then fix the draft](/quest/local/11-slow-mldsa-wipe-refusal.md) - other open ML-DSA work on the fork
