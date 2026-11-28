# Portable AES bitslices eight blocks in each architecture's 128-bit vectors

## Goal

On each portable-backend architecture whose target enables 128-bit vectors at compile time, `low/generic/aes_nohw.rs` bitslices eight blocks a pass in those vectors, as it already does in SSE2 words on x86 and x86_64, wherever that measures faster than the four-block `u64` path on that target. Targets where it does not keep four blocks, and ALGORITHMS.md says which.

## Plan

Planned 2026-11-28 (owner: SSE2 on x86 now, plus a quest for each other architecture's vectors).

- The SSE2 `word` module is the template: a 128-bit word, with byte shifts across the whole register, 32-bit lane shifts for the row rotations, and the bitwise ops. Each child adds a `word` module for its architecture, gated on the target feature the target enables at compile time, since AGENTS.md lets a backend require only those.
- Eight blocks in two `u64` lanes without intrinsics was measured and refused (2026-11-28, [steelhead99x/rind#352](https://github.com/steelhead99x/rind/pull/352)). LLVM vectorizes none of the circuit, so it ran 95 instructions per byte against the four-block path's 88. Don't retry it without new evidence.
- Each child's correctness check is `aes_nohw::tests::configurations_agree`, a digest of CTR and CBC outputs that every word configuration must reproduce, plus the crosschecks against aws-lc-rs where aws-lc builds for the target. Its constant-time check is ctgrind where valgrind runs the target, and otherwise the reason it can't.
