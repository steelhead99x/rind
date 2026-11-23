# [S] Close remaining zeroing and heap-scratch test gaps in rind

## Goal

`rind/tests/zeroing.rs` and `rind/tests/heap_scratch.rs` cover every remaining secret-holding type and every heap-allocating protocol and error path in `rind`, failing on any unwiped byte or key-dependent freed heap block.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ close the remaining zeroing and heap-scratch test gaps found in the audit (rejected: skip).

- `rind/tests/zeroing.rs`: add coverage for `blind_rsa::Blinding` (client blinding factor), `hpke::Exporter::sender`, HPKE with `CHACHA20_POLY1305` and `AES_256_GCM`, `hkdf::Okm`, and `HKDF_SHA384` / `HKDF_SHA512` / `HKDF_SHA1`.
- `rind/tests/heap_scratch.rs`: add checks for HPKE, OPRF/VOPRF, FROST, ECVRF, blind RSA, AEADs, ciphers, AES key wrap, HKDF, HMAC, and error/rejection paths (allocations freed after failed parsing, verification, or decryption with secret keys).
- Fix any real wiping omission these tests uncover in the same PR (per `AGENTS.md`'s wipe rule: wipe keys, keyed state, and heap scratch derived from a private key; do not wipe digest contexts, decrypted messages, or stack temporaries).
