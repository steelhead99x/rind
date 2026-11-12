# [L] ML-KEM's AVX-512 sampler is proven

## Goal

On x86_64 CPUs with AVX-512 F, BW, VBMI, and VBMI2 (Ice Lake and later, Zen 4 and later), ML-KEM-768 earns the ✓: Graviola's 8-way Keccak-f and rejection sampling, which SampleNTT runs there, is proven.

## Plan

- Runs: `low/x86_64/mlkem_sample_poly_ntt_8x.rs`, about 320 lines of AVX-512 intrinsics: eight Keccak-f states at once and a vectorized rejection sampler. rind runs it because it is faster than s2n-bignum's proven 4-way Keccak with the scalar sampler.
- Route: Aeneas to Lean, the AVX-512 intrinsics modelled as `Rind/X86_64/Simd.lean` models AES-GCM's, against FIPS 202's Keccak-f and FIPS 203's SampleNTT. Lane-parallel Keccak reduces to eight copies of the single-state spec.

## Required

- [ML-KEM-768's construction is proven](/quest/m4/verified/mlkem-construction.md) - the SampleNTT contract this slots into
