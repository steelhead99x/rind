# [L] cipher::ChaCha20 is proven on x86_64

## Goal

`cipher::ChaCha20` earns the ✓ on x86_64 CPUs with SSE4.1.

## Plan

- Prove rind's AVX2 kernels with Aeneas over modelled intrinsics, and aws-lc's `ChaCha20_ctr32_ssse3_4x` (486 instructions, all decoded under `x86.patch`) in HOL Light against `proofs/hol-light/s2n-bignum/common/chacha20poly1305.ml`'s `chacha20_encrypt`, and compose them with the HACL* rounds' proof.
