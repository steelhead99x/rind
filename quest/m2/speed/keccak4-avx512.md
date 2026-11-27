# [S] ML-KEM's four-state SHAKE runs the eight-way AVX-512 Keccak-f

## Goal

On x86_64 with AVX-512, ML-KEM-512's and ML-KEM-1024's four-state SHAKE calls, `mid::sha3::shake256_batch` (CBD2 noise) and `SqueezingSponge4xShake128` (ML-KEM-512's matrix, and ML-KEM-1024's where it is not sampled eight at a time), run on `low::x86_64::sha3_keccak8_f1600` wherever that measures faster than s2n-bignum's four-way AVX2 routine, with their Lean proofs kept.

## Plan

Found by [quest/m2/speed/keccak8-and-aarch64-pq.md](https://github.com/kixel-ai/rind/pull/1073): on Zen 5 (`fedora`) eight states took 192 ns on the AVX-512 kernel against 291 ns for four on s2n-bignum's `sha3_keccak4_f1600_alt`, so even a call with four lanes in use costs two thirds as much.

- Route `shake256_batch` and `SqueezingSponge4xShake128` through `low::sha3_keccak_nof8_f1600` as `Shake8x` does, and update `shake256_batch_spec` and the `shake128x4_*` theorems in `proofs/Rind/X86_64/Sha3.lean` over `keccak_nof8_f1600_spec`.
- Measure ML-KEM-512 and ML-KEM-1024 key generation, encapsulation, and decapsulation before and after on `fedora`; ML-KEM-768 runs pyca/verified-garbage's code on AVX-512 and is unaffected.
- SLH-DSA's SHAKE lanes stay [SLH-DSA SHAKE on x86_64](/quest/m4/pq/slh-dsa-shake-x86.md)'s.

## Related

- [Avoid 512-bit kernels on Intel cores that downclock for them](/quest/m2/speed/avoid-zmm.md)
- [rind's eight-way AVX-512 Keccak-f is proven](/quest/m4/verified/keccak8-avx512.md) - the kernel this reuses
