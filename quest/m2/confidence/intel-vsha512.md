# [S] SHA-384 and SHA-512 run no instruction Intel leaves off its data-independent list

## Goal

On x86_64, SHA-384, SHA-512, and SHA-512/256, and so HMAC, HKDF, and Ed25519 signing over them, run no `VSHA512` instruction while Intel's "Data Operand Independent Timing Instructions" list omits them, and `admin/ct-vartime` refuses them on x86.

## Plan

Found on 2026-11-13 by the PR that handled Intel's MXCSR-dependent timing: Intel's list (updated 2026-02-23) holds `SHA1RNDS4` and `SHA256RNDS2` but none of `VSHA512RNDS2`, `VSHA512MSG1`, or `VSHA512MSG2`, which `rind/src/low/x86_64/sha512.rs` runs through OpenSSL's routine on every CPU with the SHA512 extension, from Arrow Lake and Lunar Lake on. aws-lc runs its AVX2 routine there. Each instruction `admin/ct-vartime` refuses is absent from its vendor's list, but its x86 `VARTIME` pattern names only division and floating-point arithmetic, so it accepts these today; `PLATFORMS.md` names the gap.

- Recommended: ✅ drop the SHA512-extension path for OpenSSL's AVX2 routine, and add `vsha512\w*` to the x86 `VARTIME` pattern and its samples (rejected: keep it for hashing only, since the digest API cannot tell a secret input from a public one; keep it and document, which leaves HMAC keys and Ed25519 nonces on instructions with no timing guarantee).
- Measure the SHA-512 loss on `desktop`'s Arrow Lake against aws-lc-rs at the bar's hash sizes, and drop `HaveSha512` and its test toggle if nothing else uses them.
- Revisit if Intel adds the instructions to its list.
