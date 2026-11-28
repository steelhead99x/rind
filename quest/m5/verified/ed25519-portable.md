# [M] The portable backend's Ed25519 is proven

## Goal

Ed25519 on rind's portable backend earns the ✓, from the signature API down to curve25519-dalek, reusing armv7's proof as [the portable X25519 quest](/quest/m5/verified/x25519-portable.md) reuses armv7's X25519.

## Plan

Planned with the maintainer on 2026-11-27 (`/quest-run`), from [kixel-ai/rind#1132](https://github.com/kixel-ai/rind/pull/1132).

- `Rind/Armv7/Ed25519.lean` proves armv7's six Ed25519 theorems over BAIF's dalek theorems. The portable backend runs the same glue over dalek's serial backend. Carry the proof over with the target renamed, as x25519-portable plans for X25519.
- `admin/dalek-closure` must also compare the definitions reached in `64bit-tables`, since the portable backend builds that configuration on 64-bit targets. Share that extension with x25519-portable, whichever lands first.
- The portable backend's SHA-512 is Rust that has to be proven, or already is. The proof doesn't take armv7's `sha512-armv4` assumption.

## Related

- [armv7's Curve25519](/quest/m5/verified-armv7/curve25519.md) - the armv7 Ed25519 proof this reuses
- [The portable backend's X25519](/quest/m5/verified/x25519-portable.md) - the same reuse for X25519
