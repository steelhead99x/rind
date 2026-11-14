# [L] aarch64 without the crypto extension is proven

## Goal

Every operation earns the ✓ on aarch64 cores without the crypto extension (the Raspberry Pi 4's Cortex-A72 among them): AES-GCM and the AES modes over vpaes and NEON GHASH, and SHA-256 and SHA-1 over aws-lc's scalar routines.

## Plan

- Runs: aws-lc's `vpaes-armv8` (key schedule, encrypt, decrypt, CTR, CBC; NEON `tbl` lookups, no secret-indexed memory) and `ghash-neon-armv8` (`gcm_init_neon`, `gcm_ghash_neon`), composed into AES-GCM over each eight blocks by rind's Rust as aws-lc composes them; aws-lc's `sha256_block_data_order_nohw` and `sha1_block_data_order_nohw`. SHA-512's `nohw` is already proven.
- Route: HOL Light proofs in s2n-bignum's aarch64 model, which models NEON's `tbl` and 8-bit `pmull`, against `common/fips197.ml`, `common/gcm.ml`, and [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415)'s SHA-256 spec; Aeneas for rind's composition.
- The AES and GCM specs are moving: [awslabs/s2n-bignum#490](https://github.com/awslabs/s2n-bignum/pull/490), approved but unmerged on 2026-11-12, rewrites `common/gcm.ml` and `common/fips197.ml`. Build on the pin [the in-place quest](/quest/m4/verified/aes-gcm-aarch64-in-place.md) lands once #490 merges, not on today's `b4f17ee`. If #490 closes unmerged, that quest takes its fallback and moves no pin, so this proof is written against `b4f17ee`'s specs.
- Spec pin: build on [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415)'s spec at a pinned commit while it is unmerged, and move to the merged version when it lands; `benchmarks/verified.toml`'s ✓ notes the pin (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [AES-GCM on aarch64 is proven](/quest/m4/verified/aes-gcm-aarch64.md) - the AEAD glue this tier shares
- [aarch64's AES-GCM kernels are proven in place](/quest/m4/verified/aes-gcm-aarch64-in-place.md) - the s2n-bignum pin this proof is written against: #490's `common/gcm.ml` and `common/fips197.ml`, or today's if #490 closes unmerged
