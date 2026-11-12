# [XL] armv7's NIST curves are proven

## Goal

P-256, P-384, and P-521 key agreement and ECDSA earn the ✓ on armv7.

## Plan

- Runs: `low/generic/p256.rs`, `p384.rs`, and `p521.rs`, rind's portable Rust running the aarch64 algorithms (point formulas, inversion, scalar multiplications, table select), over fiat-crypto's generated field and scalar arithmetic, except P-256's and P-384's Montgomery multiplication and squaring, which are rind's `umaal`-shaped 64-bit-accumulator Rust (560 instructions to fiat-crypto's 1,375 for P-256). Switching to fiat-crypto's multiplication fails the speed rule.
- Already proven: fiat-crypto's field operations, in Coq; its Rust printing step is unproven, as libcrux's is.
- Route: Aeneas to Lean for rind's Rust, with each fiat-crypto function an axiom citing its Coq theorem at the pinned revision under the composition rule, and rind's multiplication proven directly against the Montgomery spec. Reuse the [x86_64 and aarch64 curve proofs](/quest/m4/verified/p384.md)' group lemmas.

## Required

- [armv7 runs the Rust proofs](/quest/m5/verified-armv7/prove.md) - the armv7 translation
- [P-521 ECDH and ECDSA are proven on x86_64 and aarch64](/quest/m4/verified/p521.md) - the curve lemmas, P-384's included, this reuses
