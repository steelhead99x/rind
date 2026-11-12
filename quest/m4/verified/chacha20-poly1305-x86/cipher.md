# [L] cipher::ChaCha20 is proven on x86_64

## Goal

`cipher::ChaCha20` earns the ✓ on x86_64 CPUs with SSE4.1.

## Plan

- Prove rind's AVX2 kernels with Aeneas over modelled intrinsics, and aws-lc's `ChaCha20_ctr32_ssse3_4x` (486 instructions, all decoded under `x86.patch`) in HOL Light on the [specs](/quest/m4/verified/chacha20-poly1305-x86/specs.md), and compose them with the HACL* rounds' proof.

## Required

- [Specs](/quest/m4/verified/chacha20-poly1305-x86/specs.md) - the HOL Light ChaCha20 spec the SSSE3 routine is proven against
