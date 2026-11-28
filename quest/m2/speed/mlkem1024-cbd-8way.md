# [M] ML-KEM-1024 samples CBD eight PRFs at a time on AVX-512, proven

## Goal

On x86_64 CPUs with ML-KEM's AVX-512 (F, BW, VBMI, VBMI2), ML-KEM-1024's `SamplePolyCBD` with eta 2 hashes up to eight PRF inputs in one eight-way Keccak-f permutation again, and `admin/prove lean` still passes: the Lean proofs of `mid::mlkem::sample_poly_cbd` and its callers cover the eight-way branch, with the eight-way sampler opaque behind a stated contract, as `sample_ntt_8x` is.

## Plan

Removed 2026-11-28 (owner): the fork's eight-way path (`sample_poly_cbd2_8x` and `low/x86_64/mlkem_shake256_8x.rs`, first in 0edafa434) changed `sample_poly_cbd` to three output slices and restructured key generation's and encryption's calls, while upstream's kixel-ai/rind#1111 proves ML-KEM-768's construction over its two-slice, four-at-a-time version. The upstream sync (#349) kept the fork's Rust with upstream's proofs, so `admin/prove lean` failed on `Rind/{X86_64,Aarch64}/MlKemCbd.lean:315`. Main took upstream's `sample_poly_cbd` back so the proofs check.

- What it cost: on an AVX-512 Xeon (Emerald Rapids), 0edafa434 measured key generation 12.40 to 11.72 µs (0.95), encapsulation 12.15 to 11.35 µs (0.93), and decapsulation 10.07 to 9.25 µs (0.92), when the path still ran for ML-KEM-768 too; it was later gated to ML-KEM-1024 (`k == 4`), so ML-KEM-768 loses nothing. No report host has those AVX-512 extensions, so no gap entry records it.
- Bring the path back on top of upstream's proofs: keep the two-slice signature if the eight-way branch can live inside it, and extend `cbd_copy_spec` and `sample_poly_cbd`'s spec with the branch, taking `sample_poly_cbd2_8x` opaque with the contract its outputs are `cbd2 sigma (first + done + t)` for each `t < count`. ML-KEM-768's proofs must not change, since it never takes the branch.
- Re-measure ML-KEM-1024's keygen, encaps, and decaps on an AVX-512 host against main before and after; drop the path if it no longer pays.
- Restore `ct_sde_mlkem_prf_8x` under SDE with the module, and TESTING.md's row.
