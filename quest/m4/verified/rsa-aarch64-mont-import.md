# [M] aarch64's RSA Montgomery theorems are imported into Lean

## Goal

The HOL Light theorems for aarch64's `bn_mul_mont`, covering its generic path (`BN_MUL_MONT_GENERIC_SUBROUTINE_CORRECT`), `__bn_mul4x_mont` (`BN_MUL_MONT_MUL4X_SUBROUTINE_CORRECT`), and `__bn_sqr8x_mont` (`BN_MUL_MONT_SQR8X_SUBROUTINE_CORRECT`), all proven and joined as `BN_MUL_MONT_SUBROUTINE_CORRECT`, enter `proofs/Rind/Aarch64/` as axioms under the composition rule, so RSA's Montgomery products on aarch64 need no hypothesis and RSA verification and signing earn the ✓ there once their glue is proven.

## Plan

- Route: one axiom on the opaque wrapper `low.aarch64.mont.mul_mont`, which takes the slices and builds the pointers the naked `bn_mul_mont` reads, restating the combined HOL Light theorem over the wrapper's arguments and result, as `proofs/Rind/Aarch64/Sha256Hw.lean` states its SHA-256 axiom over the wrapper `compress_hw`, with `n * n0 + 1 == 0 (mod 2^64)` as a hypothesis so it discharges `MontArgs` from `proofs/Rind/X86_64/RsaMont.lean`; then the aarch64 counterpart of `MontProducts` from it.
- Decided 2026-11-12 (maintainer, /quest-unblock): ✅ gated on all three routines' proofs (rejected: import each routine's theorem as it lands).
- The combined theorem's frame is the `16k + 128` bytes below the stack pointer, the largest of the three routines'. It covers the Linux build's object only; Apple's lacks the entry's `.align 5`, so the ✓ there needs its own byte check or proof.
- The 4x theorem also assumes `x + 32` and `m + 32` do not wrap past `2^64`, since the routine reads the carry of adding 32 to those pointers. The axiom carries both, or derives them from the Rust caller's slices, which never end at the top of the address space.
