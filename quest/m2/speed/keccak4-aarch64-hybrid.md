# [M] aarch64 cores other than Apple's run a hybrid four-way Keccak-f

## Goal

On aarch64 cores other than Apple's, ML-KEM's, ML-DSA's, and SLH-DSA's four-way Keccak-f runs a scalar and NEON hybrid, as mlkem-native does there, where it measures faster than four scalar states at every operation, keeping the ✓ its proofs hold.

## Plan

- Kept (maintainer, 2026-11-18).
- Found by [kixel-ai/rind#851](https://github.com/kixel-ai/rind/pull/851): on Neoverse N2, rind's SHA3-instruction kernels lost to its scalar Keccak-f, by 2.1x for SHA-3 and by 1.1x to 1.3x for ML-KEM and ML-DSA, so non-Apple cores now run every state through scalar `sha3_keccak_f1600`. mlkem-native runs `x4_v8a_v84a_scalar` there (with FEAT_SHA3, and `x4_v8a_scalar` without), interleaving one scalar state with NEON pairs, after [Becker and Kannwischer](https://eprint.iacr.org/2022/1243): Arm's cores before Cortex-X4 run the SHA3 instructions on fewer SIMD units, and the scalar pipes sit idle in a NEON-only kernel.
- s2n-bignum proves both: `arm/sha3/sha3_keccak4_f1600.S`, the hybrid with the SHA3 instructions (`.arch armv8.4-a+sha3`), and `sha3_keccak4_f1600_alt.S`, NEON and scalar alone (mlkem-native's `keccak_f1600_x4_v8a_scalar_hybrid`). Transliterate them with `admin/parse-asm`, as rind's other s2n-bignum Keccak routines are, and dispatch them from `sha3_keccak_nof4_f1600` where `HaveSha3::check_keccak` is `None` and `N` is 4: `sha3_keccak4_f1600` only where `HaveSha3::check` holds, `_alt` otherwise. They permute all four states, so `N` of 1 to 3 keeps the scalar loop.
- Measure each on the `bench` workflow's aarch64 tiers (`mlkem mldsa slhdsa`) against today's scalar loop, and take each only where it is faster at every operation; ML-KEM-768's encapsulation runs verified-garbage's own code on aarch64 with FEAT_SHA3, so it does not move.
- Add their `admin/prove bytes` entries and the HOL Light theorems to `proofs/Rind/Aarch64/S2nBignum.lean`, and their branch in `KeccakDispatch.lean`.

## Related

- [SLH-DSA's SHAKE sets on x86_64 match the SPHINCS+ AVX2 C](/quest/m4/pq/slh-dsa-shake-x86.md) - the x86_64 counterpart
