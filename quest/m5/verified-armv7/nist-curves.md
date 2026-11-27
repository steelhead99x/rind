# [XL] armv7's NIST curves are proven

## Goal

P-256, P-384, and P-521 key agreement and ECDSA earn the ✓ on armv7.

## Plan

- Runs: `low/generic/p256.rs`, `p384.rs`, and `p521.rs` as `low/generic/limb32.rs` builds them, rind's portable Rust running the aarch64 algorithms (point formulas, inversion, scalar multiplications, table select), over fiat-crypto's generated 32-bit field and scalar arithmetic, except P-256's field multiplication, squaring, addition, and subtraction, which are OpenSSL's `ecp_nistz256-armv4` assembly (`low/arm/ecp_nistz256.rs`; 0.71 of the `umaal` Rust's time for the multiplication), and P-384's Montgomery multiplication and squaring, which are rind's `umaal`-shaped 64-bit-accumulator Rust in `p384_mul32.rs`. `p256_mul32.rs` stays as the schedule the other 32-bit targets run and the tests' reference. Switching to fiat-crypto's multiplication fails the speed rule.
- Already proven: fiat-crypto's field operations, in Coq; its Rust printing step is unproven, as libcrux's is.
- Route: Aeneas to Lean for rind's Rust, with each fiat-crypto function an axiom citing its Coq theorem at the pinned revision under the composition rule, and P-384's multiplication proven directly against the Montgomery spec. P-256's four assembly routines are proven on the AArch32 model, as [armv7's assembly is proven](/quest/m5/verified-armv7/assembly.md) plans. Reuse the x86_64 and aarch64 curve proofs' group lemmas (`proofs/Rind/NistGroup.lean`, `P384Multiples.lean`).

## Required

- [P-521 ECDH and ECDSA are proven on x86_64 and aarch64](/quest/m4/verified/p521.md) - the curve lemmas, P-384's included, this reuses
