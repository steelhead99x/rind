# [L] aarch64's NEON ChaCha20 is proven

## Goal

`Neon` in `proofs/Rind/Aarch64/VgChaCha20.lean` is discharged, so `cipher::ChaCha20` earns the ✓ on every aarch64 CPU at every length.

## Plan

- Runs: Graviola's NEON ChaCha20 (`low/aarch64/chacha20.rs`, from cifra), four blocks at a time and then one at a time in general-purpose registers, at the lengths VG's routines leave to it: below 128 bytes with SVE2, and without it below 192 bytes and from 257 to 447.
- Route: Aeneas over Lean models of the NEON intrinsics it calls, tested against the CPU as `Rind/Aarch64/AesKey.lean`'s are, against `Rind/Spec.lean`'s RFC 8439. It discharges only `Neon`: `chacha20_apply_keystream` still assumes `RunsCipher`, that the entry guard admits the call, the VG state can be made, and the SVE2 check returns.
- [aarch64's ChaCha20 cipher takes Graviola's faster NEON layout](/quest/m2/aarch64-chacha20-neon.md) may replace this code ([kixel-ai/rind#823](https://github.com/kixel-ai/rind/pull/823), a draft), so this proves whatever that quest leaves.

## Required

- [aarch64's ChaCha20 cipher takes Graviola's faster NEON layout](/quest/m2/aarch64-chacha20-neon.md) - settles which NEON code `cipher::ChaCha20` runs
