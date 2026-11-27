# [M] Reuse cache without compare-and-swap

## Goal

On targets without compare-and-swap, such as `thumbv6m-none-eabi` (the RP2040) and `riscv32imc-unknown-none-elf` (the ESP32-C3), an ML-DSA public key used more than once keeps its expanded matrix, as hosted targets do. ECDSA's verification table already can, with the opt-in `no-cas-ecdsa-cache` feature (`rind/src/low/generic/verification_table.rs`), but `rind/src/low/generic/reuse_cache_without_cas.rs` still keeps nothing for ML-DSA, so each verify re-expands. The fix must stay sound when two cores, or a core and an interrupt handler, use one key at once, and must not require the program to supply a critical section.

## Plan

Difficulty: 6/10 (estimate). Found while fixing [fork PR #84](https://github.com/steelhead99x/rind/pull/84), which [fork PR #154](https://github.com/steelhead99x/rind/pull/154) replaces. [Fork PR #338](https://github.com/steelhead99x/rind/pull/338) cached ECDSA's table, opt-in by the maintainer's decision, since it costs every key memory whether or not the key is reused.

These targets have atomic loads and stores but no read-modify-write, so neither the compare-and-swap cache nor ECDSA's copy-out table fits ML-DSA's heap-backed `Option<Box<[Poly]>>`: a racing publisher can lose a pointer or free a table a verifier still reads.

Recommended approach:

- Publish the expansion's pointer with an atomic store after a release fence, and let a build that finds a pointer already published drop its own. Two racing builders can each publish one, and only one pointer can be kept, so leak at most one build per race, or keep it uncached; measure which, against the expansion's size per parameter set.
- Opt in through the same `no-cas-ecdsa-cache` feature, renamed for both, or a feature of its own, since the expansion is far larger than ECDSA's table.
- Prove it under Miri with threads, on a host build that forces this implementation as `sh/portable.sh` forces ECDSA's.
- Compare an ML-DSA-65 verify loop on one of these targets, or under QEMU, before and after, and record timing, heap and stack high-water marks in the PR.

## Related

- [Fork PR #154](https://github.com/steelhead99x/rind/pull/154) - the PR that carries the keep-nothing fallback, replacing fork PR #84, which is closed unmerged
