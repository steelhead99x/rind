# [M] Support previous-major RustCrypto traits (digest 0.10, aead 0.5, signature 2) on a maintenance branch

## Goal

Crates pinned to the previous major RustCrypto trait generation (`digest 0.10`, `aead 0.5`, `signature 2`, which still dominate crates.io dependency trees) can depend on `rind-digest 0.10.x`, `rind-aead 0.5.x`, and `rind-signature 2.x` published from a dedicated maintenance branch, while `main` stays cleanly on the newest trait majors from [kixel-ai/rind#896](https://github.com/kixel-ai/rind/pull/896).

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ publish `rind-digest 0.10.x`, `rind-aead 0.5.x`, and `rind-signature 2.x` from a maintenance branch while keeping `main` on `#896`'s newest majors (rejected: workspace-excluded directories on `main`; waiting on `patch-shims`). This matches the branching pattern settled in [rind-rustls-0.24](/quest/m2/adoption/rind-rustls-0.24.md).

- After [RustCrypto's traits](/quest/m2/rustcrypto/traits.md) ([kixel-ai/rind#896](https://github.com/kixel-ai/rind/pull/896)) lands on `main`, branch a maintenance branch (e.g. `rustcrypto-prev` or `v0.10-traits`) for the previous major trait crates:
  - `rind-digest` (`0.10.x` implementing `digest 0.10`, `FixedOutput`, `Update`, `ExtendableOutput`, `Mac`/`KeyInit` as applicable)
  - `rind-aead` (`0.5.x` implementing `aead 0.5`, `AeadInPlace`, `KeyInit`, `AeadCore`)
  - `rind-signature` (`2.x` implementing `signature 2`, `Signer`, `Verifier`, `RandomizedSigner`, `DigestSigner`, `DigestVerifier`)
- Follow `AGENTS.md`'s adapter rule: upstream's trait APIs and nothing added, backed by published `rind`, with a README clearly documenting the version mapping (`rind-digest 0.10.x` -> `digest 0.10`, `rind-digest 0.11.x` -> `digest 0.11`, etc.) and any algorithms `rind` does not back.
- Verify CI tests (including `no_std + alloc` and test vectors against `sha2`, `aes-gcm`, `chacha20poly1305`, `p256`, `ed25519-dalek` on those trait versions) pass cleanly on the maintenance branch and wire the release workflow / docs link from `main`'s `MIGRATE.md` and `README.md`.

## Required

- [RustCrypto's traits](/quest/m2/rustcrypto/traits.md) - establishes the crate layout and newest-major implementations on `main` first
