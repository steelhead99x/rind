# [L] armv7's Rust AES-GCM is proven

## Goal

AES-GCM without the crypto extension, armv7's remaining Rust-only path, earns the ✓ on armv7.

## Plan

- `admin/prove`'s `extract_armv7` translates armv7 into `proofs/Rind/Armv7/`, so far from the header-protection API alone, whose ChaCha20 already earns the ✓: add the AEAD API's start-froms, and to `Rind/Armv7/{Types,Funs}External.lean` what they leave opaque.
- AES-GCM without the crypto extension runs rind's ports of aws-lc's `aes_nohw.c` (`low/generic/aes_nohw.rs`, in 32-bit words) and `gcm_nohw.c`: prove both with Aeneas. [x86_64 without AES-NI](/quest/m5/verified/x86-no-aesni.md) proves the same file in SSE2 words, so whichever lands first states the circuit's proof over the word operations both widths share.
- ML-KEM's portable arithmetic is [its own quest](/quest/m4/verified/mlkem-portable.md); its Keccak-f is assembly, in [armv7's assembly](/quest/m5/verified-armv7/assembly.md).
- Poly1305 without NEON is libcrux's HACL\*-compiled Rust, which `benchmarks/verified.toml` counts, under rind's glue.
- Decided 2026-11-12 (maintainer, /quest-unblock): ✅ land the armv7 translation and its ChaCha20 header-protection proof first, leaving AES-GCM here (rejected: keep that PR open until AES-GCM is proven; land it and fold armv7's AES-GCM into the x86_64 no-AES-NI quest).
