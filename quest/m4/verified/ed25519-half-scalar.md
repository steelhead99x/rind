# [L] Ed25519 verification on aarch64 is proven again

## Goal

`ed25519-verify` earns the ✓ again on aarch64: rind's Lean proof covers the half-size check `mid::ed25519::VerifyingKey::commits` there from the signature API down to s2n-bignum's contracts, as it does on x86_64, and `ed25519_public_key_new` and `ed25519_key_pair_verify` hold on aarch64.

## Plan

- x86_64's half landed upstream in kixel-ai/rind#1112: `Rind/X86_64/Ed25519Msm.lean`'s `msm_spec` proves `low::generic::edwards25519_msm` over s2n-bignum's `edwards25519_epadd`, `edwards25519_epdouble`, and `edwards25519_pdouble` (and their `_alt` twins), with the static tables of `B`'s and `[2^128]B`'s odd multiples checked in the kernel, and `Rind/X86_64/Ed25519Verify.lean` proves `commits`, `verify`, `ed25519_public_key_new`, and `ed25519_key_pair_verify` above it under `Msm.MsmS2n`, over `Rind/Ed25519Group.lean`'s `half_size_iff` and `Rind/X86_64/HalfSize.lean`'s proof of `mid::half_size::split`.
- aarch64 runs the same half-size check since [kixel-ai/rind#824](https://github.com/kixel-ai/rind/pull/824), over the `_alt` point routines, and has had no verification theorem since: its old proof, over s2n-bignum's `edwards25519_scalarmuldouble`, is at `git show d0e8e97f:proofs/Rind/Aarch64/Ed25519Verify.lean`.
- Prove aarch64's multiplication as `Rind/X86_64/Ed25519Msm.lean` proves x86_64's, with the `_alt` routines' contracts as axioms in `Rind/Aarch64/S2nBignum.lean`, as x86_64's `S2nBignum.lean` states them, in place of the opaque declarations in `Rind/Aarch64/FunsExternal.lean`.
- Then move `mid_verify_spec` and the three theorems above it from `Rind/X86_64/Ed25519Verify.lean` into the shared `Rind/X86_64/Ed25519.lean`, with their `#print axioms` checks in each target's `Axioms.lean`, and give `ed25519-verify` back to aarch64's ✓ row in `benchmarks/verified.toml`. Its `ed25519_key_pair_verify` takes the base point's multiples to be points of the group from `edOnCurve_pow`, as both targets' did upstream after kixel-ai/rind#1121, so it assumes no group fact.

## Related

- [Ed25519 verification on AVX2 without ADX is proven](/quest/m4/verified/ed25519-avx2-verify.md) - x86_64's other tier, whose four-point multiplication is rind's port of curve25519-dalek's AVX2 backend
