# [L] ML-KEM-1024's eight-way AVX-512 sampler is proven

## Goal

`mlkem_sample_poly_ntt_8x.rs`, which samples ML-KEM-1024's matrix eight polynomials at a time on x86_64 with AVX-512, is proven to compute FIPS 203's `SampleNTT` for each polynomial, so ML-KEM-1024 with AVX-512 can earn its ✓.

## Plan

Planned with the maintainer on 2026-11-27 (`/quest-run`), from [kixel-ai/rind#1145](https://github.com/kixel-ai/rind/pull/1145).

- [kixel-ai/rind#1122](https://github.com/kixel-ai/rind/pull/1122) proved the eight-way Keccak-f this sampler runs. Its follow-up note wrongly said [mlkem-construction](/quest/m4/verified/mlkem-construction.md) covers the rejection sampling here. That quest is ML-KEM-768 only.
- Reuse `Rind/MlKemSample.lean` from #1145: its link to FIPS 203 and its per-polynomial specs. Carry its `Halts` assumption, which says SHAKE128 eventually yields 256 usable values, the same way.
