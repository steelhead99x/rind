# [M] Reuse cache without compare-and-swap

## Goal

On targets without compare-and-swap, such as `thumbv6m-none-eabi` (the RP2040) and `riscv32imc-unknown-none-elf` (the ESP32-C3), a key used more than once keeps its public tables, as hosted targets do. Today `rind/src/low/generic/reuse_cache_without_cas.rs` keeps nothing, so each ECDSA verify rebuilds its odd multiples and each ML-DSA verify re-expands its matrix. The fix must stay sound when two cores, or a core and an interrupt handler, use one key at once, and must not require the program to supply a critical section.

## Plan

Difficulty: 6/10 (estimate). Found while fixing [fork PR #84](https://github.com/steelhead99x/rind/pull/84), which [fork PR #154](https://github.com/steelhead99x/rind/pull/154) replaces.

These targets have atomic loads and stores but no read-modify-write. The current cache relies on a compare-and-swap to elect one writer, so it cannot be reused there.

Recommended approach:

- Start with the ECDSA tables for P-256, P-384, and P-521. Encode their coordinate limbs into 32-bit atomic words and publish with a release store to the ready flag. Readers acquire the flag and copy the words into a local table. Builders for one key must produce identical words, including when an interrupt preempts another builder. Keep the hosted cache API and code path on targets with compare-and-swap.
- Use the coordinate arrays directly rather than converting arbitrary `Copy` values to bytes, so the cache never reads padding or depends on a generic type's layout. Rust 1.90 and 1.100 both compile `core::sync::atomic::AtomicU32` acquire/load and release/store for `thumbv6m-none-eabi`; the emitted code uses loads, stores, and memory barriers. Confirm the same on `riscv32imc-unknown-none-elf` before enabling it there.
- Keep ML-DSA's heap-backed expansion uncached on these targets until a bounded ownership scheme exists. A racing publisher can otherwise lose a pointer or free a table a verifier still reads.
- Prove it under Miri with threads, and in `reuse_cache_without_cas.rs`'s tests, on a host build that forces this implementation (the module already builds under `test`).
- Benchmark an ECDSA P-256 verify loop on one of these targets, or under qemu, before and after.

## Related

- [Fork PR #154](https://github.com/steelhead99x/rind/pull/154) - the PR that carries the keep-nothing fallback, replacing fork PR #84, which is closed unmerged
