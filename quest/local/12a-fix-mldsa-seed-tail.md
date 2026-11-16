# [S] Fix the ML-DSA seed-tail parity test

## Goal

https://github.com/steelhead99x/rind/pull/117's `mldsa_seed_tail` parity test passes. The test lives in `rind-aws-lc-rs/tests/parity.rs`. The harness stays in agreement with the reference on that path.

## Plan

The test was already failing before the merge of the signature API change. Reproduce it on the current #117 branch, then fix the harness or the mapping in `rind-aws-lc-rs/tests/parity.rs` and, if needed, `rind-aws-lc-rs/src/pqdsa.rs`. Do not drop the test.

Success check: in a worktree of the #117 branch, `. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && nix develop -c cargo test -p rind-aws-lc-rs --test parity mldsa_seed_tail` exits 0.

## Related

- [Decide ML-DSA wipe and refusal error mapping](/quest/local/11a-decide-mldsa-error-mapping.md) - other open ML-DSA work on the fork
