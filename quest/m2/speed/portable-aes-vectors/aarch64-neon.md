# [M] The portable backend's AES bitslices eight blocks in NEON on aarch64

## Goal

Where aarch64 runs the portable backend with NEON enabled at compile time, `aes_nohw.rs` bitslices eight blocks a pass in NEON words. That covers `aarch64-unknown-none` and the little-endian Linux targets under `--cfg rind_portable`; big-endian aarch64 joins only if the ports below hold there. It replaces the four-block `u64` path wherever it measures faster on an aarch64 host, and AES-GCM, AES-CTR, and AES-CBC decryption there take no longer than the four-block path at any length.

## Plan

- Port the SSE2 `word` module with `core::arch::aarch64`'s stable intrinsics: `vandq_u8`, `vorrq_u8`, `veorq_u8`, `vmvnq_u8`, `vextq_u8` against zero for the byte shifts, and `vshrq_n_u32` with `vshlq_n_u32` for the row rotations. Gate it on `all(target_arch = "aarch64", target_feature = "neon")` under the portable backend. Little-endian aarch64 with NEON runs the aarch64 backend's vpaes, which this leaves alone.
- Big-endian aarch64 (`aarch64_be`) has NEON too, but the SSE2 module loads blocks with a little-endian byte order. Either check that `vld1q_u8` keeps byte order there and gate it in, or leave big-endian on four blocks and say so.
- Measure on an aarch64 host with the portable backend forced, `cfg(rind_portable)`, against the four-block path: callgrind and criterion on `aes*-gcm*`, `aes*-ctr/*`, and `aes*-cbc-*` from 1200 B. x86_64 numbers say nothing about this target. Report hosts with aarch64, such as `kixtop`, can run the forced build.
- Constant time: ctgrind runs on aarch64 natively, and NEON bitwise ops and constant shifts take no secret-dependent time.
