# [M] Portable SHA-256 and SHA-512, and ESP-IDF Xtensa's SHA-256 body, are proven in Lean

## Goal

`generic::sha256::sha256_compress_blocks`, `generic::sha512::sha512_compress_blocks`, and ESP-IDF Xtensa's `sha256_iram` body are translated with the portable backend and proven against FIPS 180-4 in Lean. `Sha256Blocks.sha256` in `proofs/Rind/Portable/ShaBlocks.lean` and the compress conjunct of `RunsSha512` in `proofs/Rind/Portable/Sha512Entry.lean` become theorems, and SHA-256, SHA-384, SHA-512, SHA-512/256, and the HMAC and HKDF over them earn a portable ✓ in `benchmarks/verified.toml`, on ESP-IDF Xtensa too.

## Plan

Decided 2026-11-19 (maintainer): ✅ merge [kixel-ai/rind#793](https://github.com/kixel-ai/rind/pull/793) and plan this proof (rejected: ask for a smaller PR without the layout tooling; close it and keep HACL*'s proven code on ESP). Reason: `AGENTS.md` runs the fastest source and plans its proof.

The portable backend no longer calls libcrux-sha2's HACL* bodies: `low/portable/sha.rs` calls `generic::sha256` on the whole slice, and SHA-384/512 is `generic::sha512`, unrolled on a 64-bit pointer and rolled on a 32-bit one. ESP-IDF Xtensa runs `sha256_iram` instead of `generic::sha256`. armv7 runs aws-lc's assembly, which [armv7's assembly quest](/quest/m5/verified-armv7/assembly.md) proves, so its `generic` copies serve only tests. The Charon stack-depth workaround for libcrux's unrolled bodies is gone from `UPSTREAM.md`.

- What #793 added: `low/generic/sha512.rs`, a rolled 80-round loop over a 16-word window, and `low/portable/sha256_iram.rs`, rind's own FIPS 180-4 compression in `.iram1` with sixteen rounds unrolled, one schedule body run three times, and Xtensa `asm!` for the rotates (`ssai`/`src`) and the block load (`l32i` plus an `extui`/`src` byte swap).
- Today `admin/prove`'s portable pass includes `low::portable::sha` and leaves `crate::low` opaque, so both generic compressors stay opaque in `proofs/Rind/Portable/FunsExternal.lean`. The padding, digest, HMAC, HKDF, and PBKDF2 proofs assume their contracts, and `benchmarks/verified.toml` has no portable SHA-2 row.
- Include `low::generic::sha256::sha256_compress_blocks` and `low::generic::sha512::sha512_compress_blocks` in that pass and drop the two opaque declarations. The SHA-256 body is a loop of 64 rounds with a 16-word schedule window. SHA-512's is 80 rounds, unrolled or rolled by pointer width.
- Prove the SHA-256 body against `Rind/HashSpec.lean`'s `sha256.compress`. State SHA-512's block function as `HashSpec` states SHA-256's, and prove the loop against it: `Rind/Sha2.lean` keeps cryptol-specs' `processBlock` opaque, which suits an axiom about aws-lc's routine. Keep the x86_64 and aarch64 theorems as they are.
- Discharge `Sha256Blocks.sha256` and `RunsSha512`'s compress conjunct from those proofs. Add the `verified.toml` row for the operations the hypotheses cover, naming these functions, and regenerate `BENCHMARKS.md` with `admin/bench-report render`.
- Prove `sha256_iram` against `sha256.compress` as well. Its Xtensa `asm!` blocks are not Rust Aeneas translates: each is a rotate or a byte swap, so state each as a small hand model with the Rust fallback the host tests already run (`sha256_iram.rs` on its fallbacks), and say in the proofs README that the ✓ on ESP-IDF Xtensa trusts those instructions. Cosimulating them needs Xtensa hardware or QEMU, so decide that when starting.
- The proof covers the code, not its placement: `admin/esp32s3-sha256-layout` still checks `.iram1`, linked addresses, and the exact `ssai` sequences.
- `admin/prove`'s portable pass extracts `x86_64-unknown-linux-gnu`, which selects neither the 32-bit rolled SHA-512 nor the Xtensa body. Have it also translate a 32-bit build, such as `armv7a-none-eabi` with `--cfg rind_portable` (`target_os = "none"`), for the rolled SHA-512, and prove the Xtensa-only SHA-256 body through its host Rust fallbacks, which `sha256_iram.rs` exposes by name.
- The ✓ covers the whole operation, so the dispatch that picks each body on each target is proven too, not only the bodies. Translate the `target_os = "espidf"` and `"none"` selections as well: Charon cannot build `xtensa-esp32s3-espidf` without the esp toolchain, so settle at the start whether `admin/prove` gets that toolchain, or a host build with those cfgs forced (`--cfg` overrides on a 32-bit target) extracts the same dispatch, and state which in the ✓'s notes.
- Size M: three block functions of the shape the portable backend already proves, plus the small instruction models.

## Waiting

- kixel-ai/rind: [#794](https://github.com/kixel-ai/rind/pull/794) merges to `main`, so `low/portable/sha.rs` calls `generic::sha256` and `generic::sha512` and `Rind/Portable/Hacl.lean` is gone; this can only start then. Check that `low/portable/sha.rs` has no `libcrux_sha2` call on `main`.

## Related

- [The portable backend's SHA-2 and its HACL* ChaCha20 rounds are proven](/quest/m4/verified/portable.md) - the padding and API proofs these compressors discharge
