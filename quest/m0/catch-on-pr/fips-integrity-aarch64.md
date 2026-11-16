# [S] rind-fips's integrity test passes on aarch64

## Goal

`tampering_fails_the_integrity_test` in `rind-fips/tests/integrity.rs` passes on `ubuntu-24.04-arm` in main's nightly, by fixing the module or the test, whichever is wrong.

## Plan

- It fails at `rind-fips/tests/integrity.rs:89` on `ubuntu-24.04-arm` in main's nightly, run 43645517003 (kixel-ai/rind Actions). Find the PR that started it from the last green nightly and name it under `## Caused by`.
- If tampering goes undetected on aarch64, the self-test is broken and this is a module fix; if the test tampers with bytes the integrity check rightly does not cover on aarch64, fix the test.
