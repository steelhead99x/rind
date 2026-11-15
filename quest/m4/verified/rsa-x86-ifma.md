# [XL] x86_64's dual RSAZ IFMA exponentiation is proven

## Goal

On x86_64 CPUs with AVX-512 IFMA (Ice Lake and later, Zen 4 and later), where both CRT exponentiations run at once by aws-lc's dual RSAZ, RSA signing and decryption for 2048-, 3072-, and 4096-bit keys earn the ✓.

## Plan

- Runs (`low/x86_64/rsaz_avx512.rs`): `rsaz_amm52x{20,30,40}_x2_ifma256`, almost-Montgomery products over 52-bit limbs two moduli at a time, and `extract_multiplier_2x{20,30,40}_win5`, gathering by masking all 32 window entries, under rind's Rust port of aws-lc's driving C.
- Route: add AVX-512F, AVX-512VL, and IFMA (`vpmadd52luq`, `vpmadd52huq`, opmask registers) to s2n-bignum's x86_64 model, prove the routines against an almost-Montgomery specification, and prove the Rust driver with Aeneas.
- Taking the proven Karatsuba path on IFMA hosts instead is not a route unless it measures as fast.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [RSA signing, decryption, and key generation are proven](/quest/m4/verified/rsa-sign.md) - the CRT glue this exponentiation slots into
- [RSA on AVX-512 runs pyca/verified-garbage's code where it is faster](/quest/m2/verified-garbage/rsa-avx512.md) - VG measured 0.96 to 0.99 of the dual RSAZ's time; delete this quest if that switch covers every size the dual RSAZ runs (2048, 3072, and 4096 bits), shrink it to the sizes left otherwise, and drop this link if none switches
