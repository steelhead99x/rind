# [L] Narrow multiplier schedules on aarch64

## Goal

The narrow multiplier path is limited and benchmarked before it ships, and test hooks stay out of release FIPS builds. This is the bottom of the aarch64 stack.

## Plan

Difficulty: 7/10 (estimate).

Fork PR #82. Its body records the latest head and review score.

- [x] Keep the test hooks out of the release FIPS build: `RIND_CPU_FORCE_*` and `RIND_TEST_MIDR` compile out under `rind_fips`; the denial stays, as for AES and SHA.
- [x] Limit the narrow path to widths that are benchmarked: 16 words, and 32 words once measured on a Cortex-A76 (RSA-2048 verification at 0.57x and RSA-4096 signing at 0.52x of `bn_mul_mont`'s time).
- [x] Skip the ctgrind narrow rerun on portable builds.
- [x] Leave the one-time detection out of the ct-qemu traces: every `ct_qemu` test in `low::aarch64::schedules` calls `wide_multiplier()` before `ct_qemu::traced`.
- [x] Keep `wide_multiplier()` crate-private, as AGENTS.md's "one way to do each job" and upstream's lone hidden public item (`rind::fips`, FIPS-build only) suggest; rind-cpuid reads `AT_HWCAP` and `MIDR_EL1` itself, as its x86_64 build reads `cpuid`.
- [x] Expect a file conflict with upstream #813: resolved in `ea45d793`.

Next: [#118](/quest/m2/118-narrow-vs-generic-tests.md).
