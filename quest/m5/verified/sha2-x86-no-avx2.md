# [L] x86_64 SHA-2 without AVX2 is proven

## Goal

SHA-256, SHA-384, and SHA-512, and the MACs and KDFs over them, earn the ✓ on every x86_64 tier without AVX2 (Sandy Bridge, Westmere, Core 2, and AMD before Zen), where today only Intel's AVX SHA-512 is proven.

## Plan

- Runs: aws-lc's `sha256_block_data_order_avx` on Intel with AVX, `_ssse3` elsewhere, and `_nohw` without SSSE3; aws-lc's `sha512_block_data_order_nohw` on AMD and on Intel without AVX (`low/x86_64/aws_lc/`). They are 2.2x faster than the pure Rust routines and 1.3-1.5x faster than HACL*'s SHA-256.
- Already proven: aws-lc's AVX SHA-512, by SAW.
- Route: HOL Light proofs in s2n-bignum's x86_64 model against [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415)'s and [#420](https://github.com/awslabs/s2n-bignum/pull/420)'s FIPS 180-4 specs. #420 also adds s2n-bignum's own scalar SHA-512 routine; measure it against aws-lc's `nohw`, and take it if it is as fast.
- Spec pin: build on the specs of [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415) and [#420](https://github.com/awslabs/s2n-bignum/pull/420) at pinned commits while they are unmerged, and move to the merged version when it lands; `benchmarks/verified.toml`'s ✓ notes the pin (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [x86_64 SHA-256 on AVX2 without SHA-NI is proven](/quest/m4/verified/sha256-x86-avx2.md) - the SHA-256 spec work and its `ShaBlocks` axiom shape
- [x86_64 SHA-512 on AVX2 is proven](/quest/m4/verified/sha512-x86-avx2.md) - the SHA-512 spec work and the `RunsSha512` widening
