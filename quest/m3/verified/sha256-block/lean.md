# [M] x86_64 SHA-NI SHA-256's padding and composition are proven in Lean

## Goal

`proofs/Rind/X86_64/` proves the SHA-NI finish's plain-Rust padding, `padded` and `ended` in `rind/src/low/x86_64/sha256.rs`, gives with the tail's whole lanes the last block, and the length block when one follows, of FIPS 180-4's padded message, and composes it, through one axiom per frozen block that restates its HOL Light theorem under the epic's composition rule, into `Sha256Blocks`'s `shaext` and `shaext_finish`, so neither remains a hypothesis.

## Plan

- The theorems to restate are `SHA256_COMPRESS_BLOCKS_SHAEXT_CORRECT` in `proofs/hol-light/x86_64/sha256_compress_blocks_shaext.ml`, which stores `sha256_hash_blocks` of the blocks to the state, and `SHA256_FINISH_SHAEXT_CORRECT` in `proofs/hol-light/x86_64/sha256_finish_shaext.ml`, which leaves the digest's bytes in xmm2 and xmm1 for `sha256_shaext_finish_blocks`, the blocks then the padded block or two built from the lane count in r9 (at most 4), the end lane's words in r10 and r11, and the length's word in r8, given fewer than 2^63 whole blocks and `K` 16-byte aligned.
- Follow aarch64's `Rind/Aarch64/Sha256Hw.lean`, which composes `SHA256_HW_SUBROUTINE_CORRECT` with `Rind.S2nSha256`'s transliterated spec.
- The axioms name the HOL Light proof's file at rind's commit; `Axioms.lean` and `HashAxioms.lean` pin them.
- `admin/prove` keeps `crate::low` opaque; translate `padded` and `ended` with `--include`, as it does `low::x86_64::sha512::sha512_compress_blocks`.
