# [L] armv7 runs the Rust proofs

## Goal

`admin/prove` translates and checks rind for armv7, `benchmarks/verified.toml` and `admin/bench-report` accept an `armv7` arch, and armv7's Rust-only paths earn the ✓: ChaCha20 header protection, AES-GCM without it, and ML-KEM's arithmetic.

## Plan

- ChaCha20 header protection runs HACL*'s proven rounds on armv7 too, so its proof carries over once the target is translated.
- AES-GCM without the crypto extension runs rind's ports of aws-lc's `aes_nohw.c` (`low/generic/aes_nohw.rs`, in 32-bit words) and `gcm_nohw.c`: prove both with Aeneas. [x86_64 without AES-NI](/quest/m5/verified/x86-no-aesni.md) proves the same file in SSE2 words, so whichever lands first states the circuit's proof over the word operations both widths share.
- ML-KEM's portable arithmetic is [its own quest](/quest/m4/verified/mlkem-portable.md); its Keccak-f is assembly, in [armv7's assembly](/quest/m5/verified-armv7/assembly.md).
- Poly1305 without NEON is libcrux's HACL\*-compiled Rust, which `benchmarks/verified.toml` counts, under rind's glue.
