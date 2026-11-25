# [L] Shrink rustls+rind-rustls binary size with additive Cargo algorithm features and asm deduplication

## Goal

A release `rustls + rind-rustls` binary shrinks significantly from the 5.57 MB baseline reported in `BENCHMARKS.md` (currently 35% larger than `aws-lc-rs` at 4.11 MB and 2.87x `ring` at 1.94 MB) toward `aws-lc-rs` parity without breaking existing `rind` callers, and CI tracks binary size so regressions are caught before merge.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ keep `rind`'s `default` feature enabling all algorithms (additive, no breaking change) and have `rind-rustls` opt into `default-features = false` with only what TLS needs (rejected: making legacy/niche algorithms opt-in in a breaking 0.5 release; skipping Cargo algorithm features).

- **Additive Cargo algorithm features on `rind`**:
  - Introduce coarse, well-scoped algorithm family features on `rind` (for example: symmetric/hash core, `rsa`, `ec`, `ed25519`, `x25519`, `ml-kem`, `ml-dsa`, `slh-dsa`, `argon2`, `pbkdf2`, `hkdf`, `hpke`, `oprf`, `frost`, `spake2plus`, `vrf`, `blind-rsa`, `legacy` for MD5/SHA-1/CBC/etc.) with `default` enabling all existing public modules so `rind` remains 100% additive and backwards-compatible.
  - Have `rind-rustls` depend on `rind` with `default-features = false` and enable only the primitives TLS (`default_provider()`) actually uses (no SLH-DSA, ML-DSA, Argon2, FROST, OPRF, SPAKE2+, VRF, blind RSA, HPKE, MD5, etc.), and gate `rind-rustls`'s own optional suites cleanly where appropriate.
  - Check other adapters (`rind-ring`, `rind-aws-lc-rs`, `rind-rustcrypto`) for easy `default-features = false` wins without losing API parity.
- **Assembly and code-size deduplication**:
  - Audit `cargo bloat` / `nm --size-sort` on the `rustls + rind-rustls` binary (on x86_64 and aarch64) to locate the largest `rind` contributors (for example duplicated per-tier assembly tables, unshared Curve/RSA/Keccak/SHA precomputed tables, oversized unrolled routines, or dead dispatch branches).
  - Deduplicate or share read-only tables and cold code paths where doing so does not regress hot-tier benchmarks.
- **CI binary-size gate**:
  - Measure stripped release binary size of the `rustls + rind-rustls` example (and `rind` minimal/full builds) in CI, print the delta on PRs or fail when size jumps unexpectedly above a threshold, and record the new numbers in `BENCHMARKS.md`.

## Related

- [Gate coverage regressions, test feature powersets, and execute wasm32 tests](/quest/m2/confidence/coverage-powerset-wasm-gates.md)
