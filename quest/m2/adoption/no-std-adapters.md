# [S] Support no_std + alloc in rind-rustls and rind-aws-lc-rs

## Goal

`rind-rustls` and `rind-aws-lc-rs` compile and pass tests with `--no-default-features --features alloc` (targeting `no_std + alloc` environments such as embedded TLS and WASM without `std`), verified in CI alongside `rind` and `rind-ring`.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ add `no_std + alloc` support to `rind-rustls` and `rind-aws-lc-rs` as a companion to fixing `rind-ring`'s `no_std` bug (rejected: standalone `no_std` `rustls-webpki`, `noq`, or `instant-acme 0.9` adapters).

- **`rind-rustls`**:
  - Add `#![no_std]` with `extern crate alloc;` and `std` default feature forwarding `rustls/std` and `rind/std` (while `--no-default-features` uses `rustls` without `std` + `alloc` and `rind`'s `alloc` + `getrandom` or custom RNG path as `rustls` requires).
  - Replace `std::*` imports with `core::*` / `alloc::*` and gate any `std`-only error/RNG helpers behind `#[cfg(feature = "std")]`.
- **`rind-aws-lc-rs`**:
  - Add `#![no_std]` with `extern crate alloc;` and a default `std` feature (matching `aws-lc-rs` / `rind-ring`'s feature surface where feasible).
  - Replace `std::*` imports with `core::*` / `alloc::*` and verify `alloc`-only compilation on a `no_std` target (such as `thumbv7em-none-eabihf` or `wasm32-unknown-unknown`).
- Add both crates to `sh/dispatch.sh`'s `nostd` module, which builds `rind-ring` on `x86_64-unknown-none`, so future PRs cannot silently re-introduce `std::` imports.

## Related

- [Gate coverage regressions, test feature powersets, and execute wasm32 tests](/quest/m2/confidence/coverage-powerset-wasm-gates.md)
