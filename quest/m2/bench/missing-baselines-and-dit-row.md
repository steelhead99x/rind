# [S] Add missing Argon2id, SLH-DSA, unheld-DIT, and small-record TLS benchmark baselines

## Goal

The weekly benchmark suite and `BENCHMARKS.md` cover Argon2id and SLH-DSA against `RustCrypto` (`argon2`, `slh-dsa`) and `openssl` baselines, include an explicit unheld-DIT Apple Silicon row alongside the held-DIT row, and include a small-record `rustls` transfer row so wrapper and DIT costs are visible in every report.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ add the missing benchmark baselines and realistic Apple Silicon / small-record TLS rows (rejected: skip).

- **Missing competitor baselines**:
  - Add `argon2` (RustCrypto) and OpenSSL 3.x Argon2id baselines to the Argon2id benchmark group in `rind-bench` and `.github/workflows/bench.yml`.
  - Add SLH-DSA (and protocol benchmarks where a standard RustCrypto/OpenSSL reference exists) to the weekly benchmark matrix so regressions and speedups from AVX2/AVX-512/aarch64 work show up automatically.
- **Unheld-DIT Apple Silicon row**:
  - `rind-bench/benches/criterion/mod.rs:46` currently holds `Dit::hold()` around the benchmark loop, which hides per-call DIT MSR toggle overhead on Apple Silicon (e.g. `msr dit, #1` / `#0` on single small AEAD or signature calls).
  - Keep the existing held-DIT benchmarks for kernel throughput, and add an explicit unheld-DIT row (realistic one-shot caller cost) on Apple Silicon for small AEAD, ECDSA, Ed25519, and X25519 operations.
- **Small-record `rustls` transfer row**:
  - Add a small-record (e.g. 64 B / 256 B / 1 KiB payload) `rustls` encrypted transfer benchmark alongside bulk streaming so per-record AEAD dispatch, allocation, and DIT costs are tracked against `aws-lc-rs` and `ring`.
- Update `BENCHMARKS.md` generator/scripts so the new rows render cleanly.

## Related

- [Polish crates.io, docs.rs, website front door, and benchmark methodology](/quest/m2/trust/front-door-and-bench-methodology.md)
- [Trim Rust wrapper, dispatch, and stack-zeroing overhead on hot paths](/quest/m2/speed/wrapper-and-stack-overhead.md)
