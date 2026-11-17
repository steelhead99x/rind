# [M] Portable SHA-256 and rolled SHA-512 are proven in Lean

## Goal

`generic::sha256::sha256_compress_blocks` and `generic::sha512::sha512_compress_blocks` are translated with the portable backend and proven against FIPS 180-4 in Lean. `Sha256Blocks.sha256` in `proofs/Rind/Portable/ShaBlocks.lean` and the compress conjunct of `RunsSha512` in `proofs/Rind/Portable/Sha512Entry.lean` become theorems, and SHA-256, SHA-384, SHA-512, SHA-512/256, and the HMAC and HKDF over them earn a portable ✓ in `benchmarks/verified.toml`.

## Plan

The previous goal was libcrux-sha2's unrolled `sha256_update_nblocks` and `sha512_update_nblocks`. The portable backend no longer calls them: `low/portable/sha.rs` calls `generic::sha256` on the whole slice (ESP-IDF Xtensa runs `sha256_iram` instead, which this quest leaves alone), and SHA-384/512 is `generic::sha512`, unrolled on a 64-bit pointer and rolled on a 32-bit pointer. The Charon stack-depth workaround for those unrolled bodies is deleted from `UPSTREAM.md`. The 2026-11-12 approval of the HACL* axiom route applied to the code this backend used to run.

- Today `admin/prove`'s portable pass includes `low::portable::sha` and leaves `crate::low` opaque, so both generic compressors stay opaque in `proofs/Rind/Portable/FunsExternal.lean`. The padding, digest, HMAC, HKDF, and PBKDF2 proofs assume their contracts. `benchmarks/verified.toml` has no portable SHA-2 row.
- Include `low::generic::sha256::sha256_compress_blocks` and `low::generic::sha512::sha512_compress_blocks` in that pass and drop the two opaque declarations. SHA-256 is a loop of 64 rounds. SHA-512 is eighty unrolled rounds on the 64-bit pointer this translation uses, and a loop of 80 rounds on a 32-bit pointer, each with a 16-word schedule window. They are the code to translate. The 64-bit unroll is the body whose speed this tree restored; Charon may again refuse its depth, which the rolled loop was there to avoid.
- Prove the SHA-256 body against `Rind/HashSpec.lean`'s `sha256.compress`. State SHA-512's block function as `HashSpec` states SHA-256's, and prove the body this translation emits, the 64-bit unroll, against it: `Rind/Sha2.lean` keeps cryptol-specs' `processBlock` opaque, which suits an axiom about aws-lc's routine. Keep the x86_64 and aarch64 theorems as they are.
- Discharge `Sha256Blocks.sha256` and `RunsSha512`'s compress conjunct from those proofs. Add the `verified.toml` row for the operations the hypotheses cover, naming these two functions, and regenerate `BENCHMARKS.md` with `admin/bench-report render`.
- ESP-IDF Xtensa's `sha256_iram` is a separate body. `low/portable/sha.rs` records that nothing proves it. This quest does not.

## Related

- [The portable backend's SHA-2 and its HACL* ChaCha20 rounds are proven](/quest/m4/verified/portable.md) - the padding and API proofs these compressors discharge
