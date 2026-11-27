# [M] The portable backend's X25519 is proven

## Goal

X25519 on rind's portable backend earns the ✓, from the agreement API down to curve25519-dalek, as armv7's does on a CPU without NEON.

## Plan

- The portable backend runs the same `low::portable::curve25519` glue over dalek's serial backend, 64-bit on 64-bit targets and 32-bit on 32-bit ones, so armv7's proof applies with the target renamed: extend `admin/prove`'s portable translation to the agreement API as `extract_armv7` does, write `Rind/Portable/{Dispatch,X25519Bytes,X25519}.lean` from x86_64's, and give the portable backend a `Curve25519.lean` like armv7's without the NEON check.
- Restate BAIF's `mul_clamped` and `mul_base_clamped` theorems for the portable translation as `Rind/Armv7/Dalek.lean` does: they hold in every configuration BAIF translates. Extend `admin/prove dalek` to compare the definitions reached in `64bit-tables` as well as `32bit-tables`, since the portable backend builds both.
- Add the portable `x25519-ecdh` entry to `benchmarks/verified.toml`.

## Related

- [armv7's Curve25519](/quest/m5/verified-armv7/curve25519.md) - armv7's X25519 proof this reuses
