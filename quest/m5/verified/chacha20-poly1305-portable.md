# [L] ChaCha20-Poly1305 is proven on x86_64 without SSE4.1

## Goal

ChaCha20-Poly1305 and XChaCha20-Poly1305 earn the ✓ on x86_64 CPUs without SSE4.1 (Core 2, Nehalem, and SSE2-only virtual CPUs), where rind runs ChaCha20 and Poly1305 in separate passes.

## Plan

- Runs: HACL*'s ChaCha20 rounds at every length without AVX2, Graviola's scalar Poly1305 (`low/generic/poly1305.rs`, about 370 lines), and the separate-pass glue (`low/generic/chacha20poly1305.rs`). The SSSE3 keystream is gone.
- Already proven: HACL*'s rounds. libcrux's HACL* ChaCha20-Poly1305 measured 7-14% slower on SSE2, so switching fails the speed rule.
- Route: Aeneas to Lean for Graviola's Poly1305 and the glue against RFC 8439, which gives this tier its ✓.

## Required

- [cipher::ChaCha20 is proven on x86_64](/quest/m4/verified/chacha20-poly1305-x86/cipher.md) - HACL*'s rounds, which this tier runs at every length
