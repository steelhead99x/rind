# [L] x86_64's other RSA Montgomery products are proven

## Goal

Every RSA Montgomery product x86_64 runs outside s2n-bignum's Karatsuba routines is proven in HOL Light, so RSA-3072, RSA-4096, and every size on CPUs without ADX earn the ✓ once the glue is proven.

## Plan

- Done: `bn_mul_mont_nohw`, the fallback for every width from two words, is proven whole in `proofs/hol-light/x86_64/bn_mul_mont_nohw.ml` (`BN_MUL_MONT_NOHW_SUBROUTINE_CORRECT`), with its stack frame, probes, and callee-saved registers, against s2n-bignum's `bignum_montmul` statement.
- Runs left (`low/x86_64/mont.rs`, `rsaz.rs`): aws-lc's `bn_mul4x_mont`, `bn_mulx4x_mont`, `bn_sqr8x_mont` over `bn_sqr8x_internal` and `bn_sqrx8x_internal`, `bn_power5` and `bn_powerx5` (with rind's two zeroed scratch words), and on CPUs with AVX2 but without ADX, RSAZ AVX2's `rsaz_1024_{mul,sqr,gather5,scatter5,norm2red,red2norm}_avx2` for RSA-2048's primes. They measured 1.1 to 3 times as fast as s2n-bignum's generic routines.
- Route: HOL Light proofs in s2n-bignum's x86_64 model against the same statement as `bn_mul_mont_nohw`'s; the 4x routines share its frame and probe prologue, so its lemmas for those (`FRAME_ALIGN`, `PROBE_SPAN`, the probe loop) carry over. RSAZ AVX2 needs the 29-bit-limb representation's lemmas and any AVX2 instruction the model lacks.
- Import the theorems as axioms, retiring for these paths the `AwsLcMont` hypothesis `proofs/Rind/X86_64/RsaMont.lean`'s `mont_products` takes for RSA verification. `bn_mul_mont_nohw`'s can go in now: an axiom on the opaque `low.x86_64.mont.nohw` drops `AwsLcMont`'s first conjunct, once `MontArgs` bounds the width below `2^32`, which the routine's `mov r9d, r9d` needs and RSA's key-size limit gives.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [VG measured](/quest/m2/verified-garbage/bench.md) - whether pyca/verified-garbage's proven code beats what this would prove; if a switch replaces it, this quest is deleted or rewritten (maintainer, 2026-11-12)
