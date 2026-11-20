# [M] Constant-time variable-base multiplication on AVX2 without ADX is proven

## Goal

`edwards25519_mul` in `low/x86_64/edwards25519_msm_avx2.rs`, which ristretto255 and edwards25519's constant-time `[s]P` run on x86_64 CPUs with AVX2 but without ADX, is proven to compute `[s]P` from the scalar's signed radix-16 digits, and its table selection is proven to read each entry through masks, so the OPRF, VRF, and FROST paths there earn their proof where they run it.

## Plan

- Runs: dalek's field arithmetic over four lanes of 25.5-bit limbs and its extended-coordinate formulas, as [the Ed25519 AVX2 proof](/quest/m4/verified/ed25519-avx2-verify.md) models them, then the table of `P ..= 8P`, a branch-free `select` over `cmpeq` and `blendv` masks with a masked negation, and sixteen times the sum so far plus the digit's entry, from the top digit down. `Scalar::signed_radix_16` supplies the digits.
- Reuse that quest's field and point lemmas and the `Rind/X86_64/Simd.lean` intrinsic models; the new lemmas are the table's `(i + 1) P` entries, `select` returning `[digit]P` for `-8 <= digit <= 8`, and the loop's invariant that the accumulator is `[sum of the digits so far]P`.
- Constant time is checked by `admin/ctgrind` (`mid::ristretto255_tests::constant_time`) and `admin/ct-vartime`; proving it means the model shows no branch or index reads a digit.

## Required

- [Ed25519 verification on AVX2 without ADX is proven](/quest/m4/verified/ed25519-avx2-verify.md) - the field and point lemmas this reuses
