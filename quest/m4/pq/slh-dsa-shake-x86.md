# [M] SLH-DSA's SHAKE sets on x86_64 match the SPHINCS+ AVX2 C

## Goal

SLH-DSA's SHAKE sets sign and verify on x86_64 with AVX2 at least as fast as the SPHINCS+ team's AVX2 build, which they now trail by up to 1.2x.

## Plan

- Cause, measured on [kixel-ai/rind#641](https://github.com/kixel-ai/rind/pull/641): about 85% of SHAKE time is the four-way Keccak-f. s2n-bignum's verified `sha3_keccak4_f1600_alt` transposes its four states in and out on every call (257 ns); XKCP's `KeccakP1600times4`, which SPHINCS+ runs on states it keeps transposed, takes 240 ns.
- Route: port XKCP's AVX2 times4 permutation (CC0) and keep `shake256_x4`'s states in its interleaved layout across calls, so only absorb and squeeze transpose. `AGENTS.md` says to run the fastest source and plan its proof, so this quest also writes the proof plan into `ALGORITHMS.md`, or a quest for it under [verified](/quest/m4/verified/README.md).
- Decision (maintainer, 2026-11-13): ✅ port XKCP's four-way Keccak and plan its proof (rejected: keep s2n-bignum's verified permutation and accept the gap; drop this quest).
- Scope (recommended): SLH-DSA only. ML-KEM and ML-DSA keep s2n-bignum's proven permutation unless the port measures faster for them too, since switching them would cost their ✓.
- Done when `rind-bench/benches/slhdsa.rs` shows SHAKE signing and verification at or below SPHINCS+'s AVX2 times on the same host, and `ALGORITHMS.md`'s SLH-DSA note is updated.

