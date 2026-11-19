# [L] cipher::ChaCha20 is proven on x86_64

## Goal

`cipher::ChaCha20` earns the ✓ on x86_64 CPUs with SSE4.1.

## Plan

- Runs ([kixel-ai/rind#811](https://github.com/kixel-ai/rind/pull/811)): with AVX2, pyca/verified-garbage (VG)'s AVX2 or AVX-512 VL routine from 256 bytes, which [its proof quest](/quest/m2/verified-garbage/chacha20-proof.md) imports, and rind's two-block AVX2 kernel (`core_2x`, from Graviola) from two blocks below 256 bytes and for a tail of two to four blocks after VG's eight-block loop; without AVX2, aws-lc's `ChaCha20_ctr32_ssse3_4x` above 128 bytes; and HACL*'s rounds below those. #811 deleted the eight-block kernel, which no length ran any more.
- Prove the two-block kernel with Aeneas over modelled intrinsics, and aws-lc's `ChaCha20_ctr32_ssse3_4x` (486 instructions, all decoded under rind's model additions) in HOL Light against `thirdparty/s2n-bignum/common/chacha20poly1305.ml`'s `chacha20_encrypt`, and compose them with the HACL* rounds' proof and VG's imported theorems. The kernel's proof discharges `Kernel`, the hypothesis `chacha20_apply_keystream` in `proofs/Rind/X86_64/VgChaCha20.lean` takes for the kernel's tail ([kixel-ai/rind#853](https://github.com/kixel-ai/rind/pull/853)), which states the contract of its driver, `cipher_avx2`, for any buffer the counter covers: so it covers the driver's chunking into `core_2x` calls and the counter across them, not `core_2x` alone.
- VG lost to the SSSE3 routine (1.15 to 1.28 from 1200 B in [run 43881997679](https://github.com/kixel-ai/rind/actions/runs/43881997679)), so it stays.
