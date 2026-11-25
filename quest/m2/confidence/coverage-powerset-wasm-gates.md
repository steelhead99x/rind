# [M] Gate coverage regressions, test feature powersets, and execute wasm32 tests

## Goal

Nightly CI fails on coverage regressions across every architecture and CPU tier (including branch/monomorphization gaps, `portable`, `armv7`, Linux `aarch64`, and denied x86_64 tiers), checks Cargo feature powersets with `cargo-hack`, and executes the `wasm32-unknown-unknown` test suite rather than only checking compilation.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ turn coverage into a failing gate across missing tiers, add `cargo-hack` feature-powerset CI, and run `wasm32-unknown-unknown` tests (rejected: periodic full-workspace mutation-testing sweep).

- **Failing coverage gate (`admin/coverage`)**:
  - Change `admin/coverage` so it exits non-zero when any non-allowlisted published function is uncovered (matching `TESTING.md`'s explicit exclusion list) or when branch/region coverage regresses past a tracked baseline.
  - Extend nightly coverage collection to cover the currently unmeasured tiers: `rind_portable`, Linux `aarch64`, `armv7` (under QEMU if needed), and x86_64 with `adx`, `avx`, and `ssse3` selectively denied, plus monomorphized generic instantiations.
- **Feature-powerset CI (`cargo-hack`)**: add a CI job (PR or nightly depending on runtime) running `cargo hack check --feature-powerset` (with appropriate `--mutually-exclusive-features` / depth limits) across `rind` and all workspace adapters so no feature combination silently breaks `no_std`, `alloc`, `std`, or upcoming algorithm features.
- **Execute `wasm32-unknown-unknown` tests**: run `wasm-bindgen-test` (headless Node/wasmtime or browser runner available in Nix/CI) on `rind` and the wasm-capable adapters so `wasm32-unknown-unknown` is runtime-tested, not just `cargo check`ed.

## Related

- [Every published function runs under a test](/quest/m2/confidence/uncovered-functions.md)
- [Shrink rustls+rind-rustls binary size with additive Cargo algorithm features and asm deduplication](/quest/m2/speed/binary-size-and-features.md)
