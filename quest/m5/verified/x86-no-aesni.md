# [XL] x86_64 AES without AES-NI is proven

## Goal

AES-GCM, AES header protection, and the AES modes earn the ✓ on x86_64 CPUs without AES-NI and PCLMULQDQ (Core 2, Nehalem, and SSE2-only virtual CPUs).

## Plan

- Runs: with SSSE3, aws-lc's `vpaes-x86_64` and `ghash-ssse3-x86_64` (`gcm_ghash_ssse3`) assembly, with rind's Rust port of the C that sets up its GHASH table, composed into AES-GCM as aws-lc composes them, taking turns over 3 KB; without SSSE3, rind's Rust ports of aws-lc's `aes_nohw.c` (`low/generic/aes_nohw.rs`, a bitsliced AES with the S-box as a circuit, about 1000 lines, which the portable backend and armv7 run in 64- and 32-bit words) and `gcm_nohw.c` (`low/generic/ghash_nohw.rs`).
- Already proven: nothing. libcrux's portable AES-GCM measured 3-7x slower.
- Route: HOL Light proofs of the vpaes and SSSE3 GHASH routines in s2n-bignum's x86_64 model against `common/fips197.ml` and `common/gcm.ml`; Aeneas to Lean for the two Rust ports, whose S-box circuit and masked-multiply GHASH reduce to finite checks over every input byte and limb pattern.
- The AES and GCM specs: `common/gcm.ml` and `common/fips197.ml` at rind's s2n-bignum pin, `3f01260f`, which has [awslabs/s2n-bignum#490](https://github.com/awslabs/s2n-bignum/pull/490)'s rewrite of both.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
