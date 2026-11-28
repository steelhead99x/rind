# [M] The portable backend's AES bitslices eight blocks in wasm simd128

## Goal

On `wasm32` built with `-C target-feature=+simd128`, `aes_nohw.rs` bitslices eight blocks a pass in `v128` words, replacing the 32-bit two-block path wherever that measures faster under wasmtime and in a browser engine. A build without `simd128` keeps two blocks.

## Plan

- Port the SSE2 `word` module with `core::arch::wasm32`'s stable intrinsics: `v128_and`, `v128_or`, `v128_xor`, `v128_not`, `i8x16_shuffle` against zero for the byte shifts, and `u32x4_shr` with `u32x4_shl` for the row rotations. Gate it on `all(target_family = "wasm", target_feature = "simd128")`.
- This reverses the speed epic's 2026-11-12 "no consumer" note for wasm's simd128 in AES's case only, by the owner's 2026-11-28 decision.
- Measure under wasmtime (`just wasm`'s runner) and in one browser engine, against the two-block path: CTR, GCM, and CBC decryption from 1200 B. Native x86_64 numbers say nothing about a wasm engine's code.
- Constant time stays unchecked on wasm, as PLATFORMS.md says: the engine compiles the code again. Bitwise `v128` ops and constant shifts are no worse than the scalar path there.
- CI builds `wasm32-wasip2` without `simd128`; add a `+simd128` build of rind's vector tests under wasmtime, so `configurations_agree` runs on the new words.
