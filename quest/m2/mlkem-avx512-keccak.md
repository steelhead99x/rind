# [M] ML-KEM-768 on AVX-512 takes Graviola's Keccak lane sharing

## Goal

On x86_64 CPUs with AVX-512, ML-KEM-768 runs Graviola's late-2026 Keccak work where it measures faster: its PRFs on eight Keccak-f states at once, a two-state AVX-512VL Keccak-f for the leftover states, and the spare lanes filled with other hashing in key generation, encapsulation, and decapsulation. BENCHMARKS.md's ML-KEM-768 rows against aws-lc-rs say what each gained, and what did not gain is left out.

## Plan

Found by the 2026-11-14 [upstream-updates](/quest/m2/upstream-updates.md) run, reading Graviola from 2026-10-29 to 11-05: `ce6fcae2` (PRFs on 8x Keccak-f), `de4c0f2c`, `47575a44`, `879518f5`, and `bd4b464a` (one- and two-state AVX-512VL Keccak-f, and the 8x routine's tail), and `832be239`, `2da72fa2`, and `4e7280a0` (A[2][2] squeezed alongside H(ek) in encapsulation, two blocks of J absorbed alongside other work in decapsulation, and a spare CBD lane for A[2][2] in key generation). Graviola measures about 8% faster encapsulation, 3% faster decapsulation, and 1.4% faster key generation. rind took Graviola's 8-way SampleNTT in July (`low/x86_64/mlkem768_sample_poly_ntt_8x.rs`) and none of this.

- Port each change on its own and keep only those that measure faster on an AVX-512 host; the lane sharing may also help the AVX2 path over s2n-bignum's `keccak4`.
- This adds unproven code beside s2n-bignum's proven Keccak, and grows what [ML-KEM's AVX-512 sampler is proven](/quest/m4/verified/mlkem-avx512-sampler.md) must prove; say in ALGORITHMS.md which ⚡ it adds.
- Every new path gets its `admin/ct-sde` and ctgrind coverage, as the sampler has.

## Related

- [ML-KEM's AVX-512 sampler is proven](/quest/m4/verified/mlkem-avx512-sampler.md) - proves the code this extends
