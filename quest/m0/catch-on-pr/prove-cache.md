# [XS] admin/prove rebuilds after a toolchain bump

## Goal

`admin/prove` works after a nixpkgs or toolchain bump without deleting `target/prove` and `target/prove-portable` by hand.

## Plan

- After kixel-ai/rind#772 bumped nixpkgs, proof runs failed with "can't find crate for `cfg_if`" until `target/prove` and `target/prove-portable` were deleted: the toolchain kept its version string, so Cargo reused the stale build.
- Key the two target directories by the toolchain's store path or `rustc -vV` hash, and remove other keys' directories so the cache does not grow.
