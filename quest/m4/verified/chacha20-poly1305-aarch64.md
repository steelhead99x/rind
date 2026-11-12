# [XL] ChaCha20-Poly1305 is proven on aarch64

## Goal

ChaCha20-Poly1305, XChaCha20-Poly1305, and `cipher::ChaCha20` earn the ✓ on aarch64, with and without the crypto extension.

## Plan

- Runs: aws-lc's NEON `chacha20_poly1305_{seal,open}` and `poly_hash_ad_internal` (`low/aarch64/aws_lc/`), rind's AEAD glue and HChaCha20 over HACL*'s rounds, and for `cipher::ChaCha20`, Graviola's NEON ChaCha20 (`low/aarch64/chacha20.rs`, from cifra).
- Already proven: HACL*'s rounds. No aarch64 ChaCha20 or Poly1305 assembly proof exists; the proven ones (Vale's, libjade's) are x86_64 only.
- Route: HOL Light proofs of aws-lc's routines in s2n-bignum's aarch64 model on [x86_64's](/quest/m4/verified/chacha20-poly1305-x86/specs.md) RFC 8439 specs; Aeneas for the glue, and for Graviola's NEON ChaCha20 over modelled NEON intrinsics.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [moq-dev/rind#448](https://github.com/moq-dev/rind/pull/448)).

## Required

- [HOL Light specs of ChaCha20-Poly1305 equal the Lean ones](/quest/m4/verified/chacha20-poly1305-x86/specs.md) - the HOL Light ChaCha20 and Poly1305 specs; the Lean specs and the glue's Lean proof above aws-lc's routine have landed
