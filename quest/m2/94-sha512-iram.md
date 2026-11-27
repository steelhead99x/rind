# [M] SHA-512 in IRAM

## Goal

The IRAM SHA-512 path is tested end to end on QEMU, sized deliberately, and free of duplicated code.

## Plan

Difficulty: 6/10 (estimate).

Fork PR #94, head `48132d02`, on #69. Score 6/10.

- Add a QEMU run of the full compressor against a FIPS vector.
- Use a cfg that cargo-mutants treats as test-only.
- Measure the 16x unroll's size, or limit it to S3.
- Pick the IRAM default, with a size limit if it stays on.
- Limit the unaligned `l32i` load to the ESP-IDF cores.
- Fix the three lows: the asm duplicates `sha256_iram`, the docs describe the old body, and the layout script is duplicated.
