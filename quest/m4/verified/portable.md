# [L] The portable backend's HACL* paths are proven

## Goal

`admin/prove` translates and checks rind's portable backend, `benchmarks/verified.toml` and the report take an entry for it, and the operations whose core there is HACL*'s verified code earn the ✓: SHA-256, SHA-384, SHA-512, and SHA-512/256, HMAC, HKDF, and PBKDF2 over them, and ChaCha20 header protection. Every other portable operation is listed in `proofs/README.md` against the quest that proves its code.

## Plan

Found by the 2026-11-09 audit: the backend landed in [moq-dev/rind#458](https://github.com/moq-dev/rind/pull/458) hours after the 2026-11-07 audit, so [the epic](/quest/m4/verified/README.md)'s "every backend" had no quest for it beyond [its Keccak-f](/quest/m4/verified/keccak-portable.md).

- Runs: `low/portable/` and `mid/portable/`, pure Rust for every architecture without rind assembly, with rind's shared arithmetic in `low/generic/`. It has no CPU tiers (`low/portable/cpu.rs:4`), so its theorems take no `Runs` hypothesis about dispatch.
- Translation: Charon on x86_64 under `--cfg rind_portable --cfg curve25519_dalek_backend="serial"`, the flags CI's portable jobs build with (`.github/workflows/ctgrind.yml:109`), into `Rind/Portable/`, with the hand models copied as `admin/prove` copies them to `Rind/Aarch64/`. That is the 64-bit configuration. Where the code picks by pointer width (Poly1305 in `low/portable/poly1305.rs`, `gcm_nohw`'s configuration, curve25519-dalek's limbs), the ✓ says which it covers; the 32-bit forms are the code [the armv7 epic](/quest/m5/verified-armv7/README.md) proves.
- `benchmarks/verified.toml`'s `arch` takes x86_64 or aarch64 (`benchmarks/verified.toml:24`), and the report's portable column is x86_64 under the cfg (`admin/bench-report:776`): give an entry a way to name the backend.
- SHA-2: `low/portable/sha.rs` calls libcrux-sha2's `sha256_update_nblocks` and `sha512_update_nblocks`, HACL*'s `Hacl_Hash_SHA2` as KaRaMeL prints it in Rust, in pieces under 2^31 bytes, beneath the padding, digest, HMAC, HKDF, and PBKDF2 glue `proofs/` already proves over `ShaBlocks` and `RunsSha512`. Proving the two functions discharges both hypotheses here with nothing assumed of the CPU. Open, for the PR to settle with the maintainer:
  - translate the two functions with the rest and prove them against FIPS 180-4, as the ChaCha20 rounds were (`proofs/README.md:115`): no axiom, and KaRaMeL's unverified printing leaves the trust base (recommended, if Aeneas translates KaRaMeL's output);
  - or one axiom per function citing HACL*'s F* theorem under the composition rule, as `benchmarks/verified.toml:149` counts libcrux's own entries; libcrux records no HACL* revision to pin it to.
- Either way SHA-512's block function has to be a definition here: `Rind/Sha2.lean:42` keeps cryptol-specs' `processBlock` opaque, which suits an axiom about aws-lc's routine and nothing else. State it as `Rind/HashSpec.lean` states SHA-256's, and keep the x86_64 and aarch64 theorems as they are.
- The compares behind `hmac::verify` and `pbkdf2::Secret::verify` are Rust on this backend (`low/portable/cpu.rs:33`, `:50`), so the `ct_compare_16_spec` and `ct_compare_bytes_spec` axioms the asm backends take from HOL Light need none here: Aeneas translates them, or a hand model stands in where one reads through raw pointers (`:33`).
- ChaCha20 header protection runs the HACL* rounds `Rind/X86_64/ChaCha20.lean` already proves, one block at a time (`low/portable/chacha20.rs`); its proof carries over once the backend is translated.
- Not this quest's, and listed in `proofs/README.md` with the quest that proves the code, each of whose proofs then runs on this translation:
  - SHA-3 and ML-KEM: [the portable Keccak-f](/quest/m4/verified/keccak-portable.md), [the construction](/quest/m4/verified/mlkem-construction.md), and [the portable arithmetic](/quest/m4/verified/mlkem-portable.md);
  - ChaCha20-Poly1305: [Graviola's Poly1305 and the separate-pass glue](/quest/m5/verified/chacha20-poly1305-portable.md);
  - AES and AES-GCM: rind's `aes_nohw.c` and `gcm_nohw.c` ports, in [armv7's Rust proofs](/quest/m5/verified-armv7/prove.md) and [x86_64 without AES-NI](/quest/m5/verified/x86-no-aesni.md), which share one source file across word widths;
  - X25519 and Ed25519: curve25519-dalek's serial backend under rind's glue (`low/portable/curve25519.rs`, `mid/portable/ed25519.rs`), in [armv7's Curve25519](/quest/m5/verified-armv7/curve25519.md), whose source of Lean proofs also covers the 64-bit limbs this translation runs;
  - P-256, P-384, and P-521: [armv7's NIST curves](/quest/m5/verified-armv7/nist-curves.md), over field code [the 64-bit limbs quest](/quest/m3/cold-speed/portable-limbs.md) replaces on 64-bit targets;
  - RSA: [verification](/quest/m4/verified/rsa-verify.md) and [signing](/quest/m4/verified/rsa-sign.md), over `low/generic/bignum.rs`'s Montgomery loop, which the 64-bit limbs quest also replaces;
  - MD5: [its own quest](/quest/m5/verified/md5.md).
- Whatever still lacks a ✓ on this backend after those is [the re-audit](/quest/m4/verified/re-audit.md)'s to plan.

## Related

- [The portable backend's Keccak-f is proven or replaced](/quest/m4/verified/keccak-portable.md) - the one portable routine with a proof quest before this
- [64-bit portable targets use 64-bit limbs](/quest/m3/cold-speed/portable-limbs.md) - moves 64-bit targets to fiat-crypto's 64-bit field code and a `u64` Montgomery loop, changing what the curve and RSA proofs cover here
- [armv7 runs the Rust proofs](/quest/m5/verified-armv7/prove.md) - translates the same Rust for a 32-bit target
