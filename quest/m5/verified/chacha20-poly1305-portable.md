# [L] ChaCha20-Poly1305 is proven on x86_64 without SSE4.1

## Goal

ChaCha20-Poly1305 and XChaCha20-Poly1305 earn the ✓ on x86_64 CPUs without SSE4.1 (Core 2, Nehalem, and SSE2-only virtual CPUs), where rind runs ChaCha20 and Poly1305 in separate passes, in rind's `x86_64-unknown-linux-gnu` build: the SSSE3 ChaCha20 an x86_64 Mac assembles is Apple's copy, which the proof does not cover and this quest leaves out.

## Plan

- Runs: HACL*'s ChaCha20 rounds at every length on SSE2, and up to 128 bytes with SSSE3, aws-lc's `ChaCha20_ctr32_ssse3_4x` above; Graviola's scalar Poly1305 (`low/generic/poly1305.rs`, about 370 lines); and the separate-pass glue (`low/generic/chacha20poly1305.rs`).
- Already proven: HACL*'s rounds. libcrux's HACL* ChaCha20-Poly1305 measured 7-14% slower on SSE2, so switching fails the speed rule.
- Route: Aeneas to Lean for Graviola's Poly1305 and the glue against RFC 8439, which gives the SSE2 tier its ✓; the SSSE3 tier also runs aws-lc's SSSE3 ChaCha20, which `proofs/hol-light/x86_64/chacha20_ctr32_ssse3_4x.ml` proves, in place, for `cipher::ChaCha20` ([kixel-ai/rind#1048](https://github.com/kixel-ai/rind/pull/1048)), in rind's `x86_64-unknown-linux-gnu` build only, whose object the proof covers (an x86_64 Mac assembles Apple's copy, which no proof covers); `cipher_all_spec` in `proofs/Rind/X86_64/ChaCha20Cipher.lean` proves the `ChaCha20::cipher` the separate-pass glue calls.

