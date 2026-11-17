# [M] Reuse cache without compare-and-swap

## Goal

On targets without compare-and-swap, such as `thumbv6m-none-eabi` (the RP2040) and `riscv32imc-unknown-none-elf` (the ESP32-C3), a key used more than once keeps its public tables, as hosted targets do. Today `rind/src/low/generic/reuse_cache_without_cas.rs` keeps nothing, so each ECDSA verify rebuilds its odd multiples and each ML-DSA verify re-expands its matrix. The fix must stay sound when two cores, or a core and an interrupt handler, use one key at once, and must not require the program to supply a critical section.

## Plan

Difficulty: 6/10 (estimate). Found while fixing [fork PR #84](https://github.com/steelhead99x/rind/pull/84).

These targets have atomic loads and stores but no read-modify-write. The current cache relies on a compare-and-swap to elect one writer, so it cannot be reused there.

Recommended approach:

- Store `Copy` values (`[AffineMontPoint; 8]`, `[AffinePoint; 8]`, `EncodedPoint`) as atomic words plus a ready flag. Racing builders compute the same public value, so they store the same words, and a store racing another identical store is not a data race on atomics.
- Return the value by copy, never `&T`: a reference read while a late builder stores identical words would still be a data race on a non-atomic `T`. That changes `get_or_build` on these targets, or on every target to keep one API; decide which by measuring the hosted copy cost.
- ML-DSA's `Option<Box<[Poly]>>` needs its own scheme: publish a pointer with an atomic store. Two racing builders can each publish one, and only one pointer can be kept, so the other build leaks or is freed only once no reader holds it. Leaking at most one build per race is the simplest sound option; measure whether it is acceptable or keep ML-DSA uncached there.
- Prove it under Miri with threads, and in `reuse_cache_without_cas.rs`'s tests, on a host build that forces this implementation (the module already builds under `test`).
- Benchmark an ECDSA P-256 verify loop on one of these targets, or under qemu, before and after.

## Related

- [Bare-metal no-std backends](/quest/m2/84-bare-metal-no-std.md) - the PR that added the keep-nothing fallback
