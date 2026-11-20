# [M] The portable backend's 64-bit SHA-256 and SHA-512 block functions are proven in Lean

## Goal

The portable backend's SHA-256 and SHA-512 block functions on 64-bit targets, `low::generic::sha256` and `low::generic::sha512_awslc` (aws-lc's `sha256_block_data_order_nohw` and `sha512_block_data_order_nohw`, ported to Rust), are translated with the rest of the portable backend and proven against FIPS 180-4 in Lean, so `Sha256Blocks.sha256` and `RunsSha512`'s block-function field in `proofs/Rind/Portable/` stop being hypotheses and the portable SHA-2 ✓ returns on 64-bit targets.

## Plan

The portable SHA-2 speed quest replaced HACL*'s verified block functions on 64-bit targets with these, which measured faster on one x86_64 core (`ALGORITHMS.md`, "portable, 64-bit targets"), so the portable SHA-2 ✓ went, no theorem covers them, and the portable theorems take their contracts as hypotheses, as SHA-1's do.

- The functions are macro-unrolled rounds over a 16-word window, then three or four passes of sixteen rounds with the working variables renamed by position. They are plain Rust over arrays and rotates, which should translate without the stack-depth panic HACL*'s `unroll_for!` bodies hit; check that first.
- Have `admin/prove`'s portable pass include `crate::low::generic::sha256` and `crate::low::generic::sha512_awslc` instead of leaving them opaque (`Rind/Portable/FunsExternal.lean` declares them opaque today), and prove each against `Rind/HashSpec.lean`'s `sha256.compress` and `Rind/Sha2.lean`'s `processBlock`, as `Rind/X86_64/ChaCha20.lean` proves HACL*'s ChaCha20 rounds. The statements are the fields `ShaBlocks.lean` and `Sha512Entry.lean` already hold, so nothing above them changes.
- One round, then one pass, as lemmas, and let the unrolled bodies reuse them if `step*` is slow on the straight-line code.
- Decide whether the 32-bit hosted targets (i686, wasm32, ARM before ARMv7), which still run HACL*, move to the same code once measured there, so one proof covers every target but the microcontrollers and ESP-IDF Xtensa, [whose rolled loops have their own proof](/quest/m4/verified/rolled-sha2-esp.md). Until then HACL*'s F* proofs cover them and nothing here does.

## Related

- [The rolled SHA-256 and SHA-512 loops on microcontrollers are proven in Lean](/quest/m4/verified/rolled-sha2-esp.md) - proves the code the 32-bit microcontrollers run
