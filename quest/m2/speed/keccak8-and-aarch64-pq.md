# [M] Reuse 8-way AVX-512 Keccak in ML-DSA/SLH-DSA and add aarch64 pipelined SHA-256 x8 and NEON ML-KEM codecs

## Goal

Post-quantum signing and encapsulation capture the remaining obvious SIMD wins on x86_64 and aarch64: ML-DSA and SLH-DSA reuse the existing AVX-512 8-way Keccak-f kernel (and keep 4-way states transposed across rounds), `aarch64` gains a pipelined `sha256_finish_x8` path for SLH-DSA SHA2, and `aarch64` gains NEON ML-KEM compress/decompress routines.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ wire existing 8-way AVX-512 Keccak into ML-DSA and SLH-DSA, add pipelined `aarch64` `sha256_x8`, and port NEON ML-KEM compress/decompress (rejected: skip).

- **AVX-512 8-way Keccak reuse (`x86_64`)**:
  - `rind/src/low/x86_64/mlkem_sample_poly_ntt_8x.rs` already ships `_sha3_keccak8_f1600`. Expose and reuse it from `rind/src/mid/mldsa.rs` (matrix/vector expansion and rejection sampling) and SLH-DSA SHAKE paths (coordinating cleanly with [kixel-ai/rind#872](https://github.com/kixel-ai/rind/pull/872) for AVX2 SLH-DSA SHAKE).
  - Also keep 4-way AVX2 Keccak states transposed in `rind/src/mid/sha3.rs` across consecutive squeezes/absorbs instead of transposing back and forth on every block.
- **Pipelined `aarch64` `sha256_finish_x8`**:
  - In `rind/src/low/mod.rs` (around lines 597-605) and `rind/src/low/aarch64/`, replace the sequential 8x loop with a pipelined/interleaved `sha256_finish_x8` (using ARMv8 SHA2 instructions interleaved across independent lanes to hide instruction latency) for SLH-DSA-SHA2.
- **NEON ML-KEM compress/decompress (`aarch64`)**:
  - Port vectorized NEON ML-KEM polynomial compress/decompress (`d = 1, 4, 5, 10, 11`) matching the x86_64 vectorized paths, and verify constant-time behavior under `ctgrind`/`ct-vartime`.
- Benchmark ML-DSA, SLH-DSA (SHAKE and SHA2), and ML-KEM on both x86_64 (AVX2 + AVX-512) and aarch64 before and after, respecting `avoid-zmm` downclocking rules for AVX-512.

## Related

- [Avoid 512-bit kernels on Intel cores that downclock for them](/quest/m2/speed/avoid-zmm.md)
- [Add missing Argon2id, SLH-DSA, unheld-DIT, and small-record TLS benchmark baselines](/quest/m2/bench/missing-baselines-and-dit-row.md)
