# [M] The portable backend's SHA-256 and SHA-512 run the fastest permissive source

## Goal

The portable backend's SHA-256 and SHA-512 (and with them SHA-384, SHA-512/256, their HMACs, and HKDF) run the fastest permissively licensed portable source on every 64-bit target, measured at every size, closing the 1.11 to 1.22× gap to aws-lc's C that `benchmarks/gaps.toml`'s portable SHA-2 entry records.

## Plan

Decided 2026-11-18 (maintainer, [kixel-ai/rind#619](https://github.com/kixel-ai/rind/pull/619#issuecomment-6994276361)): ✅ keep this quest (rejected: drop it). Decided 2026-11-20 (owner): ✅ only x86_64 runs aws-lc's ports until aarch64 without NEON, riscv64 and s390x are measured (rejected: every 64-bit portable target).

- x86_64's portable backend runs aws-lc's `sha256_block_data_order_nohw` and `sha512_block_data_order_nohw`, ported to Rust (`low::generic::sha256`, `low::generic::sha512_awslc`), measured on one loaded local core at 0.85 to 0.90× aws-lc's C for SHA-256 and 0.97 to 1.04× for SHA-512. The weekly tier has not confirmed it.
- aarch64 without NEON, riscv64, s390x and powerpc64 still run HACL*'s verified `Hacl_Hash_SHA2` through libcrux-sha2, unmeasured against the ports. The gates are `target_arch = "x86_64"` in `rind/Cargo.toml`, `rind/src/low/mod.rs` and `rind/src/low/portable/sha.rs`.
- Contributor draft [kixel-ai/rind#794](https://github.com/kixel-ai/rind/pull/794) drops libcrux-sha2 and rewrites the same `gaps.toml` entry: whichever lands second merges the other's changes. Decided 2026-11-20 (owner): this work lands first and #794's replacement follows.
- The proof of the ports is [the x86_64 portable SHA-2 Lean quest](/quest/m4/verified/portable-sha2-lean.md).

## Waiting

- kixel-ai/rind: the weekly bench's portable tier (`sha2 hmac hkdf`) runs on x86_64's ports, then close the gap in `benchmarks/gaps.toml` once it shows x86_64's portable SHA-2 within 10% of aws-lc's C at every size. `admin/bench-report render --check` refuses a stale entry.
- Maintainer: measure aarch64 without NEON, riscv64 and s390x on native hardware with the three `target_arch = "x86_64"` gates changed to `target_pointer_width = "64"`, and widen them only where the ports are no slower than HACL* at every size.
- Maintainer: decide the 32-bit hosted targets (i686, wasm32, ARM before ARMv7), which keep HACL*: keep until measured, move to the ports, or move only those with 16 or more registers.
- Maintainer: delete this quest once every 64-bit portable target runs the fastest source or keeps HACL* on a measurement, and the gap is closed.
