# [XL] ChaCha20-Poly1305 is proven on aarch64

## Goal

ChaCha20-Poly1305, XChaCha20-Poly1305, and `cipher::ChaCha20` earn the ✓ on aarch64, with and without the crypto extension.

## Plan

- Runs: aws-lc's NEON `chacha20_poly1305_{seal,open}` and `poly_hash_ad_internal` (`low/aarch64/aws_lc/`), rind's AEAD glue and HChaCha20 over HACL*'s rounds, and for `cipher::ChaCha20`, Graviola's NEON ChaCha20 (`low/aarch64/chacha20.rs`, from cifra).
- Already proven: HACL*'s rounds. No aarch64 ChaCha20 or Poly1305 assembly proof exists; the proven ones (Vale's, libjade's) are x86_64 only.
- Route: HOL Light proofs of aws-lc's routines in s2n-bignum's aarch64 model on `thirdparty/s2n-bignum/common/chacha20poly1305.ml`'s RFC 8439 specs, which `Rind/S2nChaCha20Poly1305.lean` proves are `Rind/Spec.lean`'s; Aeneas for the glue, and for Graviola's NEON ChaCha20 over modelled NEON intrinsics.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [ChaCha20-Poly1305 on aarch64 runs pyca/verified-garbage's code where it is faster](/quest/m2/verified-garbage/chacha20-poly1305-aarch64.md) - VG's seal and open measured 0.60 to 0.92 of aws-lc's time; on each tier that switches, this quest keeps XChaCha20-Poly1305's glue and HChaCha20, which VG doesn't have, and `cipher::ChaCha20`; tiers that don't switch keep all of it
- [aarch64 cipher::ChaCha20 runs pyca/verified-garbage's code where it is faster](/quest/m2/verified-garbage/chacha20.md) - VG's bare ChaCha20 took 0.52 to 0.65 of rind's time on a Neoverse N2 from 1200 B but 1.22 at 32 B; this quest drops `cipher::ChaCha20` only for the lengths and tiers that switch
