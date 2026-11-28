# [L] The portable backend's AES bitslices eight blocks a pass

## Goal

The portable backend's AES-GCM, AES-CTR and AES-CBC decryption take no more than aws-lc's time from 1200 B up on the weekly bench's portable row, and at least as little as today's four-block `aes_nohw.c` port on a 64-bit target without AES instructions (riscv64 or s390x under QEMU, and aarch64 with the portable backend forced), closing the 1.10 to 1.35× gap `benchmarks/gaps.toml`'s portable AES entry records.

## Plan

Planned 2026-11-27 (owner: close the top five benchmark gaps).

- Today rind runs aws-lc's `aes_nohw.c` in its 64-bit configuration, four blocks a pass ([kixel-ai/rind#621](https://github.com/kixel-ai/rind/pull/621)). The portable row builds aws-lc's C for x86_64, where it bitslices eight blocks into SSE2 registers. Port that eight-block layout using two `u64` lanes, or `u128`, so it needs no SIMD and still compiles on every portable target.
- The real portable targets' aws-lc runs four blocks too, so a win on the x86_64 row alone is not enough: keep the four-block path on any target where the eight-block one measures slower, and say which in ALGORITHMS.md.
- Constant time is unchanged in kind (bitsliced, no table lookups). Run ctgrind on the new path, and the portable `ct-portable-targets` checks where they run.
- Differential-test against the four-block path and aws-lc for every key size, CTR counter wrap, and partial final block.
- The finishing PR removes the gap's entry, or narrows it to what remains, with the numbers.
