# [L] x86_64's dual RSAZ IFMA exponentiation is proven

## Goal

On x86_64 CPUs with AVX-512 IFMA (Ice Lake and later, Zen 4 and later), where both CRT exponentiations run at once by aws-lc's dual RSAZ, RSA signing and decryption for 3072-bit keys earn the ✓ on CPUs without AVX512_FP16 (AMD's, and Ice Lake), which run it.

## Plan

- Runs (`low/x86_64/rsaz_avx512.rs`): `rsaz_amm52x30_x2_ifma256`, almost-Montgomery products over 52-bit limbs two moduli at a time, and `extract_multiplier_2x30_win5`, gathering by masking all 32 window entries, under rind's Rust port of aws-lc's driving C.
- Its 4096-bit routines (`rsaz_amm52x40_x2_ifma256`, `extract_multiplier_2x40_win5`) also run, for the 3969- to 4032-bit keys VG's CRT does not take. No benchmark row has such a key, so the ✓ does not wait on them.
- 2048- and 4096-bit keys, and 3072-bit ones on CPUs with AVX512_FP16, run pyca/verified-garbage's CRT instead since [kixel-ai/rind#814](https://github.com/kixel-ai/rind/pull/814), which [its proof quest](/quest/m2/verified-garbage/rsa-avx512-proof.md) covers. VG's 3072-bit CRT for other CPUs measured 1.21 to 1.48 times the dual RSAZ's time on Zen 5 (0.99 on Zen 4), so the dual RSAZ stays there; delete this quest only once a later VG measures as fast at 3072 bits on every IFMA CPU and also takes the 3969- to 4032-bit keys below, and rind switches both.
- Route: add AVX-512F, AVX-512VL, and IFMA (`vpmadd52luq`, `vpmadd52huq`, opmask registers) to s2n-bignum's x86_64 model, prove the routines against an almost-Montgomery specification, and prove the Rust driver with Aeneas.
- Taking the proven Karatsuba path on IFMA hosts instead is not a route unless it measures as fast.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [RSA signing, decryption, and key generation are proven](/quest/m4/verified/rsa-sign.md) - the CRT glue this exponentiation slots into
