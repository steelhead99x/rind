# [M] Close existing adapter parity gaps across rind-rcgen, rind_cryptography, rind-ring, and rind-aws-lc-rs

## Goal

Close the concrete parity gaps discovered in the 2026-11-21 audit across existing adapters: `rind-rcgen` exposes the `aws_lc_rs` feature subset cleanly, `rind_cryptography` supports non-12-byte AES-GCM nonces and RSA-PSS `Custom(16)` salt length, `rind-ring` and `rind-aws-lc-rs` implement `rsa::KeyPair::from_components` and `ring::io::Positive`/`der`, and `rind-python`/`rind-dart` READMEs accurately match their current implementations.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ close the concrete parity gaps in existing adapters (rejected: skip; also rejected: standalone `no_std` `rustls-webpki`, `noq`, or `instant-acme 0.9` adapters).

- **`rind-rcgen`**:
  - Close the missing `aws_lc_rs` feature subset parity gaps (`rind` already supports P-521, RSA keygen, ML-DSA, and SEC1/PKCS#1 decoding, while `rind-rcgen` currently matches only `rcgen`'s smaller `ring` subset) and add parity tests against upstream `rcgen`.
- **`rind_cryptography` (`rind-dart/cryptography`) & stale Python/Dart READMEs**:
  - Support non-12-byte AES-GCM nonces in `rind_cryptography` (`rind::aead::gcm::Key` already supports variable-length IVs).
  - Support custom RSA-PSS salt lengths (`Custom(16)`, matching Dart `cryptography`'s default 16-byte salt) in `rind_cryptography` so upstream RSA-PSS tests no longer skip.
  - Refresh stale backend claims in `rind-python/README.md:124-125` (claims rind only runs on x86_64/aarch64/arm32) and `rind-dart/README.md:79` (claims rind has no WebAssembly backend).
- **`rind-ring` & `rind-aws-lc-rs`**:
  - Implement `rsa::KeyPair::from_components` (`rsa::KeyPairComponents`) in both `rind-ring` and `rind-aws-lc-rs`, plus `ring::io::Positive` and `ring::io::der` in `rind-ring` (and `io::der` in `rind-aws-lc-rs`) where downstream callers import them directly.
  - Add upstream-style unit tests and update each adapter's `Cargo.toml` API skip list and README missing-surface table.

## Related

- pyrind takes rind 0.4's shape, and rind for Dart takes rind 0.4's shape: both done on this fork (commits c4c0b542 and 812fa745), so their quest files are gone here.
