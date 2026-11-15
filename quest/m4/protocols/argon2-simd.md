# [S] Argon2id fills memory with the fastest kernel on aarch64 and AVX-512

## Goal

Argon2id's compression function runs the fastest kernel measured on aarch64, on x86_64 CPUs with AVX-512, and on x86_64 CPUs without AVX2, so a defender affords more memory per second than an attacker's GPU gains. Today aarch64 and x86_64 without AVX2 run rind's portable Rust, and x86_64 with AVX2 a port of the reference implementation's AVX2 rounds, which measured 18% faster than RustCrypto's `argon2` and 1.7x faster than OpenSSL's on an Intel Core Ultra 7 270K Plus (`rind-bench`'s `argon2`, RFC 9106's 64 MiB recommendation).

## Plan

- aarch64: write a NEON kernel on the reference's 128-bit (`blamka-round-opt.h` SSE) layout and keep it only if it beats the portable Rust, which LLVM may already vectorize, on an Apple core and a Neoverse core.
- AVX-512: measure libsodium's `argon2-fill-block-avx512f.c` (ISC) layout against the AVX2 port on Zen 4 or 5 and on Sapphire Rapids, keeping it only where it wins on both. `admin/ctgrind` cannot decode AVX-512, so its constant-time test runs under `admin/ct-sde`.
- x86_64 without AVX2: measure the reference's SSSE3 rounds against the portable Rust.
- No host the implementing agent could reach had AVX-512 or aarch64 when [moq-dev/rind#634](https://github.com/moq-dev/rind/pull/634) landed Argon2id; the Mac mini and the bench workflow's arm64 and AVX-512 runners can measure them.
