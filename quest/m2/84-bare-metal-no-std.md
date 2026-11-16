# Bare-metal no-std backends

Difficulty: 8/10 (estimate)


## Goal

The bare-metal backends are safe on unaligned targets and their CPU and cache handling is correct. This is the bottom of the bare-metal stack.

## Plan

Fork PR #84 (fork only), head `95f3c6dc`. Score 6/10. A partial diff is saved.

Highs:
- The asm backends do unaligned accesses on `aarch64-unknown-none` and `armv7a`/`r-none`.
- `PLATFORMS.md` leaves Cortex-M3 off the slow-multiplier list.

Mediums:
- CPUID leaf-7 subleaf 1 is read without checking the highest subleaf.
- The `cached()` constructors skip the CPU check.
- Targets without compare-and-swap rebuild the cache on every call.

Finish this before [#85](85-xtensa-lint.md).
