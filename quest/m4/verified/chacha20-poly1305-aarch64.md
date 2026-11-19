# [XL] ChaCha20-Poly1305 is proven on aarch64

## Goal

ChaCha20-Poly1305 and XChaCha20-Poly1305 earn the ✓ on aarch64 CPUs without SVE2, with and without the crypto extension, and `cipher::ChaCha20`, whose NEON code runs with or without SVE2, earns it on every aarch64 CPU. On SVE2 CPUs the two AEADs' one pass runs pyca/verified-garbage's routines instead, which [their own quest](/quest/m2/verified-garbage/chacha20-poly1305-aarch64-proof.md) proves; the glue around either, HChaCha20 included, is the same code on every CPU, and this quest proves it.

## Plan

- Runs: without SVE2, aws-lc's NEON `chacha20_poly1305_{seal,open}` and `poly_hash_ad_internal` (`low/aarch64/aws_lc/`); on every CPU, rind's AEAD glue and HChaCha20 over HACL*'s rounds, and for `cipher::ChaCha20`, Graviola's NEON ChaCha20 (`low/aarch64/chacha20.rs`, from cifra). VG's NEON ChaCha20-Poly1305 ran up to 1.06 of aws-lc's time at 32 to 512 bytes on Apple's M4 under rind's glue (2026-11-16, [kixel-ai/rind#813](https://github.com/kixel-ai/rind/pull/813)), so only CPUs with SVE2 switched.
- Already proven: HACL*'s rounds. No proof covers aws-lc's aarch64 ChaCha20-Poly1305; VG's covers only its own routines, and the other proven ones (Vale's, libjade's) are x86_64 only.
- Route: HOL Light proofs of aws-lc's routines in s2n-bignum's aarch64 model on `thirdparty/s2n-bignum/common/chacha20poly1305.ml`'s RFC 8439 specs, which `Rind/S2nChaCha20Poly1305.lean` proves are `Rind/Spec.lean`'s; Aeneas for the glue, and for Graviola's NEON ChaCha20 over modelled NEON intrinsics.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [aarch64 cipher::ChaCha20 runs pyca/verified-garbage's code where it is faster](/quest/m2/verified-garbage/chacha20.md) - VG's bare ChaCha20 took 0.52 to 0.65 of rind's time on a Neoverse N2 from 1200 B but 1.22 at 32 B; this quest drops `cipher::ChaCha20` only for the lengths and tiers that switch
