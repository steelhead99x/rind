# [L] Narrow multiplier schedules on aarch64

## Goal

The narrow multiplier path is limited and benchmarked before it ships, and test hooks stay out of release FIPS builds. This is the bottom of the aarch64 stack.

## Plan

Difficulty: 7/10 (estimate).

Fork PR #82, head `81a1bc14`. Score 6/10. A partial diff is saved.

- [x] Keep the test hooks out of the release FIPS build: `RIND_CPU_FORCE_*` and `RIND_TEST_MIDR` compile out under `rind_fips`; the denial stays, as for AES and SHA.
- [x] Limit the narrow path to 16 words until it is benchmarked. The 32-word Karatsuba routines compile only for tests, which call them directly.
- [x] Skip the ctgrind narrow rerun on portable builds.
- Leave the one-time detection out of the ct-qemu traces.
- [x] `wide_multiplier()` is `#[doc(hidden)]`: rind-cpuid reports it with each benchmark, so it cannot be crate-private.
- Expect a file conflict with upstream #813.

Next: [#118](/quest/m2/118-narrow-vs-generic-tests.md).
