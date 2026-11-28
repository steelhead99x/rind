# [M] The portable backend's AES bitslices eight blocks a pass

## Goal

The portable backend's AES-GCM, AES-CTR and AES-CBC decryption take no more than aws-lc's time from 1200 B up on the weekly bench's portable row, and at least as little as today's four-block `aes_nohw.c` port on a 64-bit target without AES instructions (riscv64 or s390x under QEMU, and aarch64 with the portable backend forced), closing the 1.10 to 1.35× gap `benchmarks/gaps.toml`'s portable AES entry records.

## Plan

Planned 2026-11-27 (owner: close the top five benchmark gaps).

- Today rind runs aws-lc's `aes_nohw.c` in its 64-bit configuration, four blocks a pass ([kixel-ai/rind#621](https://github.com/kixel-ai/rind/pull/621)). The portable row builds aws-lc's C for x86_64, where it bitslices eight blocks into SSE2 registers. Port that eight-block layout using two `u64` lanes, or `u128`, so it needs no SIMD and still compiles on every portable target.
- The real portable targets' aws-lc runs four blocks too, so a win on the x86_64 row alone is not enough: keep the four-block path on any target where the eight-block one measures slower, and say which in ALGORITHMS.md.
- Constant time is unchanged in kind (bitsliced, no table lookups). Run ctgrind on the new path, and the portable `ct-portable-targets` checks where they run.
- Differential-test against the four-block path and aws-lc for every key size, CTR counter wrap, and partial final block.
- The finishing PR removes the gap's entry, or narrows it to what remains, with the numbers.

Measured 2026-11-28 on a shared 2-core x86_64 VM, CTR over 16 KB with an AES-128 key, `aes_nohw.rs` built standalone at `opt-level=3`, one codegen unit:

| Path | Instructions per byte (callgrind) | Time, quietest of three interleaved runs |
|---|---|---|
| Today's four blocks in `u64` | 88.3 | 4.4 ns/B |
| Eight blocks as two four-block batches, step by step | 95.0 | 5.0 ns/B |
| Eight blocks in `[u64; 2]` words, each op on both lanes | 95.5 | 4.9 ns/B |
| Eight blocks in SSE2 words, the x86_64 backend's `word` module | 44.4 | 2.9 ns/B |

- Neither `u64`-lane layout is faster. LLVM's SLP vectorizer puts none of the circuit into SSE2 registers: the disassembly holds only scalar `xor`, `and`, and shifts, plus extra spills from doubling the live words. The state stays in phi nodes across the round loop, so no stores seed it. A `u128` word lowers to the same pairs of `u64` ops. With scalar ops, eight blocks costs the same gates per block as four, so on targets without vectors it can only lose to register pressure.
- Eight blocks pays only in 128-bit vector registers. aws-lc's portable row gets them from `__SSE2__`. Here, half the instructions take 0.67 to 0.86× the time across runs. That matches ALGORITHMS.md's 0.82 to 0.92× aws-lc's time for the x86_64 backend's no-SSSE3 path, which is the same file with SSE2 words.
- So the gap closes only by letting the portable backend use SSE2 intrinsics on x86 and x86_64. Every target of those architectures that rind supports enables SSE2 at compile time, except soft-float `x86_64-unknown-none`, so AGENTS.md's rule (only compile-time CPU features) allows it. The change would select `aes_nohw.rs`'s SSE2 `word` module under `all(any(target_arch = "x86", target_arch = "x86_64"), target_feature = "sse2")`, not only under `rind_backend = "x86_64"`. That makes the schedule 1.9 KiB. Its cost is the portable backend's first SIMD path. The owner rejected that option in this quest's brief, so it waits on the decision below. Other architectures would need `core::arch` NEON, VSX, or simd128 in the same way, or stay on four blocks.

## Waiting

- Maintainer: allow SSE2 intrinsics in the portable backend's AES on x86 and x86_64 (the measured way to close the gap), or close this quest and give the gap a `reason`. Check: a reply on the PR that recorded these measurements.
