# [XS] verified-garbage's ChaCha20-Poly1305 holds on Zen 4

## Goal

Zen 4 runs whichever of verified-garbage's AVX-512 IFMA ChaCha20-Poly1305 and aws-lc's AVX-512 code is faster there, by a measurement at every AEAD size the speed bar sets.

## Plan

Decided 2026-11-21 (maintainer, /quest-plan): ✅ measure now (rejected: rely on the weekly bench's 10% gap check, which misses a smaller loss).

- [kixel-ai/rind#953](https://github.com/kixel-ai/rind/pull/953) switched ChaCha20-Poly1305 on every CPU with AVX-512 IFMA to verified-garbage's routine without measuring Zen 4, where verified-garbage lost at an older pin.
- Dispatch the `bench` workflow naming `chacha20_poly1305` on the weekly bench's Zen 4 runner, at every AEAD size the speed bar sets, seal and open, against aws-lc's AVX-512 code (which #953's dispatch ran before).
- If verified-garbage loses at any size, dispatch Zen 4 (CPUID family 0x19, which among AVX-512 IFMA CPUs is Zen 4 alone) back to aws-lc's code at those sizes, and record why in the dispatch's comment. If it holds, record the numbers in this quest's PR and finish.
