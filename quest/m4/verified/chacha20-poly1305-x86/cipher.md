# [L] cipher::ChaCha20 is proven on x86_64

## Goal

`cipher::ChaCha20` earns the ✓ on x86_64 CPUs with SSE4.1.

## Plan

- Runs ([kixel-ai/rind#811](https://github.com/kixel-ai/rind/pull/811)): with AVX2, pyca/verified-garbage (VG)'s AVX2 or AVX-512 VL routine from 256 bytes, which [its proof quest](/quest/m2/verified-garbage/chacha20-proof.md) imports, and rind's two-block AVX2 kernel (`core_2x`, from Graviola) from two blocks below 256 bytes and for a tail of two to four blocks after VG's eight-block loop; and HACL*'s rounds below those and without AVX2. The SSSE3 routine this used to name no longer ships. #811 deleted the eight-block kernel, which no length ran any more.
- Prove the two-block kernel with Aeneas over modelled intrinsics, and compose it with the HACL* rounds' proof and VG's imported theorems.
