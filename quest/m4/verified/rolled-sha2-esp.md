# [M] The rolled SHA-256 and SHA-512 loops on microcontrollers are proven in Lean

## Goal

SHA-256 on ESP-IDF Xtensa and SHA-384/512 on 32-bit microcontrollers (`target_os = "espidf"` or `"none"`), which [kixel-ai/rind#793](https://github.com/kixel-ai/rind/pull/793) moves from HACL*'s proven code to rolled loops, are proven against FIPS 180-4 in Lean, as `proofs/Rind/Portable/` proves the rest of the portable SHA code, so the ✓ returns on those targets.

## Plan

Decided 2026-11-19 (maintainer): ✅ merge #793 and plan this proof (rejected: ask for a smaller PR without the layout tooling; close it and keep HACL*'s proven code on ESP). Reason: `AGENTS.md` runs the fastest source and plans its proof.

- What #793 adds: `low/generic/sha512.rs`, a rolled 80-round loop over a 16-word window, and `low/portable/sha256_iram.rs`, rind's own FIPS 180-4 compression in `.iram1` with sixteen rounds unrolled, one schedule body run three times, and Xtensa `asm!` for the rotates (`ssai`/`src`) and the block load (`l32i` plus an `extui`/`src` byte swap). Every other 32-bit target keeps HACL*.
- Prove both block functions against `Rind/HashSpec.lean`'s `sha256.compress` and `Rind/Sha2.lean`'s `processBlock`, with Aeneas's translation of the Rust, as [the x86_64 portable SHA-2 quest](/quest/m4/verified/portable-sha2-lean.md) plans for the x86_64 bodies, and have `ShaBlocks.lean` and `Sha512Entry.lean` state these targets' contracts too.
- The Xtensa `asm!` blocks are not Rust Aeneas translates: each is a rotate or a byte swap, so state each as a small hand model with the Rust fallback the host tests already run (`sha256_iram.rs` on its fallbacks), and say in the proofs README that the ✓ on ESP-IDF Xtensa trusts those instructions. Cosimulating them needs Xtensa hardware or QEMU, so decide that when starting.
- The proof covers the code, not its placement: `admin/esp32s3-sha256-layout` still checks `.iram1`, linked addresses, and the exact `ssai` sequences.
- `admin/prove`'s portable pass extracts `x86_64-unknown-linux-gnu`, which selects neither rolled path. Have it also translate a 32-bit build, such as `armv7a-none-eabi` with `--cfg rind_portable` (`target_os = "none"`), for the rolled SHA-512, and prove the Xtensa-only SHA-256 body through its host Rust fallbacks, which `sha256_iram.rs` exposes by name.
- The ✓ covers the whole operation, so the dispatch that picks each body on each target is proven too, not only the bodies. Translate the `target_os = "espidf"` and `"none"` selections as well: Charon cannot build `xtensa-esp32s3-espidf` without the esp toolchain, so settle at the start whether `admin/prove` gets that toolchain, or a host build with those cfgs forced (`--cfg` overrides on a 32-bit target) extracts the same dispatch, and state which in the ✓'s notes.
- Size M: two block functions of the shape the portable backend already proves, plus the small instruction models.

## Waiting

- kixel-ai/rind: [#793](https://github.com/kixel-ai/rind/pull/793) merges to `main`; this can only start then. Check that `low/generic/sha512.rs` and `low/portable/sha256_iram.rs` exist on `main`.

## Related

- [The x86_64 portable backend's SHA-256 and SHA-512 block functions are proven in Lean](/quest/m4/verified/portable-sha2-lean.md) - proves the code x86_64's portable backend runs
