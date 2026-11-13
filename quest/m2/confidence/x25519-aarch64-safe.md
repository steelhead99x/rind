# [S] aarch64 X25519 runs routines proven constant time, if as fast

## Goal

On aarch64, X25519 runs s2n-bignum's `curve25519_x25519_byte` (or `_byte_alt`) and `curve25519_x25519base_byte` (or `_byte_alt`), whose `_SAFE` theorems prove them constant time for every input, if they measure as fast as the `curve25519_x25519_alt` and `curve25519_x25519base_alt` it runs now, which have none. Otherwise the measurement is recorded and only `admin/ct-binsec`'s `ct_binsec_x25519` harness checks them.

## Plan

- Benchmark each candidate against the current routines on the arm64 runners and an Apple M chip, at agreement and key generation, as AGENTS.md's rule for verified sources asks: switch only where a candidate is as fast at every size.
- The `_byte` routines take and return little-endian bytes rather than words, which may let `mid::x25519` drop its conversions.
- On a switch, import through `admin/parse-asm`, and ALGORITHMS.md's table then names the `_SAFE` theorem; TESTING.md's X25519 cell cites it on aarch64 as it does on x86_64.

## Related

- [ALGORITHMS.md's constant-time theorems](/ALGORITHMS.md#s2n-bignums-constant-time-theorems) - which routines run without one
