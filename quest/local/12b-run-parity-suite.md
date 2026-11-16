# [S] Run the full aws-lc-rs parity suite after the seed-tail fix

## Goal

On the branch of https://github.com/steelhead99x/rind/pull/117, the rest of the parity coverage still passes after the `mldsa_seed_tail` fix (e1763c5d).

## Plan

Do not drop tests. Change `rind-aws-lc-rs/tests/parity.rs` only if a failure in the full suite requires it.

Success check: in a worktree of the #117 branch, `. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && nix develop -c cargo test -p rind-aws-lc-rs --test parity` exits 0.
