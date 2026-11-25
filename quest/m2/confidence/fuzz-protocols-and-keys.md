# [M] Fuzz unfuzzed protocols and fix hardcoded-key fuzz targets

## Goal

Every protocol and key parser in `rind` has a libFuzzer target that varies its secret keys and exercises all protocol modes, including `spake2plus`, `frost`, `oprf` base mode, `x25519_pkcs8` differential parsing, and all 12 `slh_dsa` parameter sets, and all new and updated targets run in the nightly fuzz workflow.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ add fuzz targets for unfuzzed protocols and fix hardcoded-key fuzzers (rejected: skip; also rejected: separate fuzzers for the 6 pure-Rust adapters).

- Add `fuzz/fuzz_targets/spake2plus.rs` covering prover/verifier state transitions, malformed share/confirm messages, empty/unusual context and identity inputs, and serialization round-trips.
- Add `fuzz/fuzz_targets/frost.rs` covering DKG / trusted-dealer shares, commitment parsing, nonce/signing-share validation, signature aggregation, and malformed share/package rejection across supported ciphersuites.
- Fix hardcoded-key blind spots in existing targets:
  - `fuzz/fuzz_targets/oprf.rs`: derive server keys from fuzzer input instead of fixed constants, and exercise OPRF base mode alongside VOPRF and POPRF.
  - `fuzz/fuzz_targets/vrf.rs` and `fuzz/fuzz_targets/blind_rsa.rs`: derive keypairs/secrets from fuzzer bytes (or structured `arbitrary` seeds) so edge-case scalars and moduli are reachable.
- Strengthen key-parser targets:
  - `fuzz/fuzz_targets/keys.rs`: cover all 12 `slh_dsa` parameter sets (currently only 2 are covered), plus `x25519_pkcs8` differential checking against a reference parser (or strict ASN.1 round-trip invariants matching `ed25519_pkcs8`).
- Register all new targets in `fuzz/Cargo.toml` and `.github/workflows/fuzz.yml` (and verify each target runs cleanly for a short smoke run with `cargo fuzz`).
