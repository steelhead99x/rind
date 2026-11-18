# [L] Narrow multiplier schedules on aarch64

## Goal

The narrow multiplier path is limited and benchmarked before it ships, and test hooks stay out of release FIPS builds. This is the bottom of the aarch64 stack.

## Plan

Difficulty: 7/10 (estimate).

Fork PR #82, head `81a1bc14`. Score 6/10. A partial diff is saved.

- [x] Keep the test hooks out of the release FIPS build: `RIND_CPU_FORCE_*` and `RIND_TEST_MIDR` compile out under `rind_fips`; the denial stays, as for AES and SHA.
- [x] Limit the narrow path to widths that are benchmarked: 16 words, and 32 words once measured on a Cortex-A76 (RSA-2048 verification at 0.57x and RSA-4096 signing at 0.52x of `bn_mul_mont`'s time).
- [x] Skip the ctgrind narrow rerun on portable builds.
- Leave the one-time detection out of the ct-qemu traces.
- [x] `wide_multiplier()` is `#[doc(hidden)]`: rind-cpuid reports it with each benchmark, so it cannot be crate-private.
- The conflict with upstream's ChaCha20-Poly1305 SVE2 detection is resolved in this change.
- The generic-backend comparison is in `low::aarch64::schedules::agree`.
