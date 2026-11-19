# [XL] ChaCha20-Poly1305 is proven on aarch64

## Goal

ChaCha20-Poly1305 and XChaCha20-Poly1305 earn the ✓ on every aarch64 CPU, with and without SVE2 and the crypto extension, and `cipher::ChaCha20` earns it on every aarch64 CPU at the lengths its NEON code runs: below 128 bytes with SVE2, and without it below 192 bytes and from 257 to 447. On SVE2 CPUs the two AEADs' one pass runs pyca/verified-garbage's routines instead, whose theorems `proofs/Rind/Aarch64/VgChaCha20Poly1305.lean` already imports; the glue around either, HChaCha20 included, is the same code on every CPU, and this quest proves it.

## Plan

- Runs: without SVE2, aws-lc's NEON `chacha20_poly1305_{seal,open}` and `poly_hash_ad_internal` (`low/aarch64/aws_lc/`); on every CPU, rind's AEAD glue and HChaCha20 over HACL*'s rounds, and for `cipher::ChaCha20` at those lengths, Graviola's NEON ChaCha20 (`low/aarch64/chacha20.rs`, from cifra); VG's routines run the rest ([kixel-ai/rind#882](https://github.com/kixel-ai/rind/pull/882)), which [their own quest](/quest/m2/verified-garbage/chacha20-proof.md) proves. VG's NEON ChaCha20-Poly1305 ran up to 1.06 of aws-lc's time at 32 to 512 bytes on Apple's M4 under rind's glue (2026-11-16, [kixel-ai/rind#813](https://github.com/kixel-ai/rind/pull/813)), so only CPUs with SVE2 switched.
- Already proven on SVE2 CPUs, the one pass: `chacha20_poly1305_seal_sve2_spec` and `chacha20_poly1305_open_sve2_spec` prove `low::aarch64::chacha20poly1305::{seal,open}` compute `Rind/Spec.lean`'s RFC 8439 there, from axioms restating VG's theorems ([kixel-ai/rind#885](https://github.com/kixel-ai/rind/pull/885)). Compose the glue's proof with them, and add the `benchmarks/verified.toml` entries for `chacha20poly1305/*` and `xchacha20poly1305/*` on aarch64 with `cpu = ["sve2"]`, which `rind-cpuid` and `admin/bench-report` know.
- Already proven elsewhere: HACL*'s rounds. No proof covers aws-lc's aarch64 ChaCha20-Poly1305; VG's covers only its own routines, and the other proven ones (Vale's, libjade's) are x86_64 only.
- Route: proofs of aws-lc's routines in Lean on VG's models by default, after [the trial](/quest/m2/lean-assembly-trial.md), or, if the maintainer keeps them in HOL Light, HOL Light proofs in s2n-bignum's aarch64 model on `thirdparty/s2n-bignum/common/chacha20poly1305.ml`'s RFC 8439 specs, which `Rind/S2nChaCha20Poly1305.lean` proves are `Rind/Spec.lean`'s; Aeneas for the glue, and for Graviola's NEON ChaCha20 over modelled NEON intrinsics.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [aarch64 SHA-256 on the SHA-2 instructions is proven in Lean, constant time included](/quest/m2/lean-assembly-trial.md) - recommends this proof's route, Lean on VG's models by default or HOL Light as an exception the maintainer decides
