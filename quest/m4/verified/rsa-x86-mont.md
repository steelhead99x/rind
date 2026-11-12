# [L] x86_64's other RSA Montgomery products are proven

## Goal

Every RSA Montgomery product x86_64 runs outside s2n-bignum's Karatsuba routines is proven in HOL Light, so RSA-3072, RSA-4096, and every size on CPUs without ADX earn the ✓ once the glue is proven.

## Plan

- Runs (`low/x86_64/mont.rs`, `rsaz.rs`): aws-lc's `bn_mul4x_mont`, `bn_mulx4x_mont`, `bn_sqr8x_mont` over `bn_sqr8x_internal` and `bn_sqrx8x_internal`, `bn_mul_mont_nohw`, `bn_power5` and `bn_powerx5` (with rind's two zeroed scratch words), and on CPUs with AVX2 but without ADX, RSAZ AVX2's `rsaz_1024_{mul,sqr,gather5,scatter5,norm2red,red2norm}_avx2` for RSA-2048's primes. They measured 1.1 to 3 times as fast as s2n-bignum's generic routines.
- Route: HOL Light proofs in s2n-bignum's x86_64 model against its Montgomery specification; RSAZ AVX2 needs the 29-bit-limb representation's lemmas and any AVX2 instruction the model lacks.
- Import the theorems as axioms, retiring the products hypothesis [RSA verification](/quest/m4/verified/rsa-verify.md) leaves for these paths.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [moq-dev/rind#448](https://github.com/moq-dev/rind/pull/448)).
