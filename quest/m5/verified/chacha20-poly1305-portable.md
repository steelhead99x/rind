# [L] ChaCha20-Poly1305 is proven on x86_64 without SSE4.1

## Goal

ChaCha20-Poly1305 and XChaCha20-Poly1305 earn the ✓ on x86_64 CPUs without SSE4.1 (Core 2, Nehalem, and SSE2-only virtual CPUs), where rind runs ChaCha20 and Poly1305 in separate passes.

## Plan

- Runs: HACL*'s ChaCha20 rounds at every length on SSE2, and up to 128 bytes with SSSE3, aws-lc's `ChaCha20_ctr32_ssse3_4x` above; Graviola's scalar Poly1305 (`low/generic/poly1305.rs`, about 370 lines); and the separate-pass glue (`low/generic/chacha20poly1305.rs`).
- Already proven: HACL*'s rounds. libcrux's HACL* ChaCha20-Poly1305 measured 7-14% slower on SSE2, so switching fails the speed rule.
- Route: Aeneas to Lean for Graviola's Poly1305 and the glue against RFC 8439, which gives the SSE2 tier its ✓; the SSSE3 tier also needs aws-lc's SSSE3 ChaCha20, proven in HOL Light by [x86_64's quest](/quest/m4/verified/chacha20-poly1305-x86/cipher.md) for `cipher::ChaCha20`.

## Required

- [cipher::ChaCha20 is proven on x86_64](/quest/m4/verified/chacha20-poly1305-x86/cipher.md) - aws-lc's SSSE3 ChaCha20
