# [XS] cargo-llvm-cov builds with its tests again

## Goal

`devShells.coverage` stops overriding `cargo-llvm-cov` with `doCheck = false` once nixpkgs' pinned rustc no longer crashes its test programs on exit, so it comes from the binary cache again. Check by building `cargo-llvm-cov` from the flake's nixpkgs without the override after each nixpkgs bump. This quest only waits; delete it once the override is gone.

## Plan

Planned with the maintainer on 2026-11-02 from [kixel-ai/rind#236](https://github.com/kixel-ai/rind/pull/236).

## Waiting

- NixOS/nixpkgs: its rustc stops crashing `cargo-llvm-cov`'s test programs on exit, so the binary cache holds the package. On 2026-11-09 cache.nixos.org had no `cargo-llvm-cov` 0.9.0 for the nixpkgs revision `flake.lock` pins (`d3b13ad7`, 2026-10-24), nor for its newer `nixpkgs-bun` pin (`9d3b8db4`, 2026-11-03), which gives the same store path. Check after each nixpkgs bump, without building: `nix eval --raw` the package's `outPath` at the pinned revision, and look up that path's hash as `https://cache.nixos.org/<hash>.narinfo`; a 200 says the tests pass.
