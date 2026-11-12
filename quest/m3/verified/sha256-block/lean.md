# [M] x86_64 SHA-NI SHA-256's padding and composition are proven in Lean

## Goal

`proofs/Rind/X86_64/` proves the SHA-NI finish's plain-Rust padding, `padded` and `ended` in `rind/src/low/x86_64/sha256.rs`, gives with the tail's whole lanes the last block, and the length block when one follows, of FIPS 180-4's padded message, and composes it, through one axiom per frozen block that restates its HOL Light theorem under the epic's composition rule, into `Sha256Blocks`'s `shaext` and `shaext_finish`, so neither remains a hypothesis.

## Plan

- Follow aarch64's `Rind/Aarch64/Sha256Hw.lean`, which composes `SHA256_HW_SUBROUTINE_CORRECT` with `Rind.S2nSha256`'s transliterated spec.
- The axioms name the HOL Light proof's file at rind's commit; `Axioms.lean` and `HashAxioms.lean` pin them.
- `admin/prove` keeps `crate::low` opaque; translate `padded` and `ended` with `--include`, as it does `low::x86_64::sha512::sha512_compress_blocks`.

## Required

- [HOL Light proof](/quest/m3/verified/sha256-block/hol-light.md) - the theorems the axioms restate
