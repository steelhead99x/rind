# [L] rind's eight-way AVX-512 Keccak-f is proven

## Goal

`low::x86_64::sha3_keccak8_f1600`'s kernel, which ML-DSA's expansion, ML-KEM-512's noise, and ML-KEM-1024's sampler run on x86_64 with AVX-512, is proven in Lean to compute FIPS 202's Keccak-f on each of its eight states, so x86_64's `RunsSha3` no longer takes it as a hypothesis and `proofs/Rind/X86_64/Axioms.lean` drops its sentence on it.

## Plan

Found by [quest/m2/speed/keccak8-and-aarch64-pq.md](https://github.com/kixel-ai/rind/pull/1073), which runs ML-DSA on the kernel and adds the hypothesis.

- Route: Aeneas to Lean over `Rind/X86_64/Simd.lean`'s models of the AVX-512 intrinsics, as `Rind/X86_64/ChaCha20Avx2.lean` proves rind's own AVX2 ChaCha20 kernel. The kernel uses `_mm512_ternarylogic_epi64` (`0x96`, `0xd2`), `_mm512_rol_epi64`, `_mm512_xor_si512`, `_mm512_set1_epi64`, `_mm512_setr_epi64`, `_mm512_unpacklo_epi64`, `_mm512_unpackhi_epi64`, `_mm512_shuffle_i64x2`, and `_mm512_loadu_si512`/`_mm512_storeu_si512`; add models and `admin/avx512-vectors.rs` vectors for those that lack them.
- Proof: each 64-bit element of the 25 vectors runs `keccak_round` on its own state, so the permutation is `keccak 24` per state; the transposes in and out are an 8x8 transpose and its inverse. Then `RunsSha3`'s last conjunct becomes a theorem, `permute_spec`.
- The ML-KEM-1024 sampler calls the same `keccak8_f1600`, so its rejection sampling is the only unproven part left there.

## Related

- [ML-KEM's construction is proven](/quest/m4/verified/mlkem-construction.md) - ML-KEM-512's noise and ML-KEM-1024's sampler run the kernel
