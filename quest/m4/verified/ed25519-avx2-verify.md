# [L] Ed25519 verification on AVX2 without ADX is proven

## Goal

Ed25519 verification on x86_64 CPUs with AVX2 but without ADX (Haswell, and virtual CPUs that hide ADX) is proven: rind's port of curve25519-dalek's AVX2 backend, which computes the half-size check's four-point multiplication there, is proven to compute `[b]B + [s0]P0 + [s1]P1`, so `ed25519-verify` earns the ✓ on the no-ADX tier.

## Plan

- Runs: `low/x86_64/edwards25519_msm_avx2.rs`, about 1,850 lines of AVX2 intrinsics: dalek's field arithmetic over four lanes of 25.5-bit limbs, its extended-coordinate point formulas, tables of two runtime points' odd multiples, and 10 KiB static tables of `B`'s and `[2^128]B`'s odd multiples, looped over `low::generic::edwards25519_msm`'s non-adjacent forms. It is variable-time over public inputs only. Since [kixel-ai/rind#768](https://github.com/kixel-ai/rind/pull/768) it replaces the two-point `edwards25519_scalarmuldouble_avx2.rs`, measuring 0.77 to 0.83 of aws-lc-rs's time against that routine's 0.86 to 0.88 with ADX denied on an Arrow Lake core, and that routine itself measured 1.08x curve25519-dalek's time against 1.30x for s2n-bignum's proven `edwards25519_scalarmuldouble_alt`, so switching back fails the speed rule.
- Route: Aeneas to Lean, the AVX2 intrinsics modelled as `Rind/X86_64/Simd.lean` models AES-GCM's, against `Rind/Ed25519.lean`'s spec, with a table proof like `Rind/Aarch64/P256Table.lean`. Reuse any published Lean proof of curve25519-dalek's field and point layers where its lemmas fit.
- The draft [kixel-ai/rind#646](https://github.com/kixel-ai/rind/pull/646) proved the two-point routine's group law, table, and NAF. Its field, point, and base table lemmas carry over; the loop now runs four tables, a second static table, and `low::generic::edwards25519_msm::non_adjacent_form`, rind's own, in place of dalek's. [kixel-ai/rind#646](https://github.com/kixel-ai/rind/pull/646) is retargeted at this four-point routine (maintainer, [2026-11-15](https://github.com/kixel-ai/rind/pull/768#issuecomment-6889289395): retarget it ✅, rejected: close it).

## Required

- [Ed25519 verification on x86_64 and aarch64 is proven again](/quest/m4/verified/ed25519-half-scalar.md) - the half-size split and identity test that this tier's verification runs around the multiplication
