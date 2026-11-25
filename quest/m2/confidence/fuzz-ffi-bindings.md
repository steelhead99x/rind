# [M] Fuzz the FFI boundaries in rind-dart, rind-python, and rind-fips

## Goal

Every `extern "C"` and FFI entry point in `rind-dart`, `rind-python`, and `rind-fips` is covered by fuzz targets that feed arbitrary lengths, null/overlapping/unaligned buffers, invalid handles, and malformed key/tag inputs without triggering undefined behavior, panics across FFI, leaks, or out-of-bounds access.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ fuzz the FFI C ABIs of `rind-dart`, `rind-python`, and `rind-fips` (rejected: skip).

- `rind-dart`: add fuzz target(s) driving the `extern "C"` surface directly (null pointers, zero and huge lengths, invalid algorithm IDs, truncated/corrupted buffers, double-free / invalid-handle guards if exposed, and key/AEAD/signature/KDF entry points).
- `rind-python`: add fuzz target(s) exercising the PyO3/buffer-protocol parsing and `unsafe` slice/buffer entry points (mutating or unusual buffer shapes, mismatched lengths, invalid DER/PEM/SPKI/PKCS#8 inputs, AEAD/RSA/EC/Argon2/KDF calls) without relying on trusted Python callers.
- `rind-fips`: add fuzz target(s) driving the FIPS module boundary entry points (PCT/KAT paths, DRBG/RNG calls, key import/export, symmetric and asymmetric operations, invalid parameter combinations).
- Wire the new targets into the nightly fuzz workflow (under ASan where supported) and document how to run them in `TESTING.md`.

## Related

- pyrind takes rind 0.4's shape, and rind for Dart takes rind 0.4's shape: both done on this fork (commits c4c0b542 and 812fa745), so their quest files are gone here.
