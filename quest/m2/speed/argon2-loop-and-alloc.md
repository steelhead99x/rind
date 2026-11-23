# [S] Remove Argon2id per-block dispatch, dead stack zeroing, and upfront 64 MiB zeroing

## Goal

`rind::argon2` eliminates the Rust-side overhead around its compression loop (per-block CPU feature checks, 2 KiB stack re-zeroing on every block, and upfront zero-initialization of the full memory buffer before first-pass overwrite), measurably speeding up Argon2id on both x86_64 and aarch64 while staying orthogonal to SIMD kernel work.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ remove Argon2id hot-loop dispatch/stack overhead and upfront 64 MiB buffer zeroing (rejected: multi-threaded Argon2id `p > 1`).

- Inspect `rind/src/mid/argon2.rs` (around lines 65 and 199) and `rind/src/low/x86_64/argon2.rs` (around lines 24-39), plus any aarch64/portable equivalents:
  - Hoist `HaveAvx2::check()` (and any equivalent tier check) out of the inner per-block compression loop so dispatch happens once per `hash` call.
  - Avoid zero-initializing `state` and `r` (2 KiB on the stack) before every block compression when they are immediately overwritten by `MaybeUninit` / full-block writes, while keeping secret-wiping invariants intact on drop/exit (`rind/tests/zeroing.rs` and `rind/tests/heap_scratch.rs`).
  - Avoid upfront `vec![0; mem_size]` zeroing of the entire 64 MiB+ memory buffer when pass 0 writes every block before reading it (allocate uninitialized memory safely, prove/check that every index read during pass 0 has already been initialized, and still wipe the full buffer before deallocation).
- Note: coordinate with or land cleanly alongside [kixel-ai/rind#822](https://github.com/kixel-ai/rind/pull/822) (Argon2id NEON/AVX-512 kernels), which changes the inner SIMD kernels rather than this Rust harness overhead.
- Benchmark before and after on x86_64 and aarch64, and verify under Miri, ASan, `zeroing.rs`, and `heap_scratch.rs`.

## Related

- [Add missing Argon2id, SLH-DSA, unheld-DIT, and small-record TLS benchmark baselines](/quest/m2/bench/missing-baselines-and-dit-row.md)
