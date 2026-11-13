# [M] aarch64's RSA Montgomery theorems are imported into Lean

## Goal

The HOL Light theorems for aarch64's `bn_mul_mont`, covering its generic path (`BN_MUL_MONT_GENERIC_SUBROUTINE_CORRECT`, proven), `__bn_mul4x_mont`, and `__bn_sqr8x_mont`, enter `proofs/Rind/Aarch64/` as axioms under the composition rule, so RSA's Montgomery products on aarch64 need no hypothesis and RSA verification and signing earn the ✓ there once their glue is proven.

## Plan

- Route: one axiom on the opaque `low.aarch64.mont.bn_mul_mont` restating the combined HOL Light theorem, as `proofs/Rind/Aarch64/AwsLc.lean` restates `sha256_block_data_order_hw`'s, with `n * n0 + 1 == 0 (mod 2^64)` as a hypothesis so it discharges `MontArgs` from `proofs/Rind/X86_64/RsaMont.lean`; then the aarch64 counterpart of `MontProducts` from it.
- Decided 2026-11-12 (maintainer, /quest-unblock): ✅ gated on all three routines' proofs (rejected: import each routine's theorem as it lands).

## Required

- [4x routine](/quest/m4/verified/rsa-aarch64-mul4x.md) - its theorem for multiples of four
- [8x squaring](/quest/m4/verified/rsa-aarch64-sqr8x.md) - its theorem for squaring at multiples of eight
