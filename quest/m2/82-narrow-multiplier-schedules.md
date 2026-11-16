# Narrow multiplier schedules on aarch64

Difficulty: 7/10 (estimate)


## Goal

The narrow multiplier path is limited and benchmarked before it ships, and test hooks stay out of release FIPS builds. This is the bottom of the aarch64 stack.

## Plan

Fork PR #82, head `81a1bc14`. Score 6/10. A partial diff is saved.

- Keep the test hooks out of the release FIPS build.
- Limit the narrow path to 16 words until it is benchmarked.
- Skip the ctgrind narrow rerun on portable builds.
- Leave the one-time detection out of the ct-qemu traces.
- Decide whether `wide_multiplier()` is public, `#[doc(hidden)]`, or crate-private.
- Expect a file conflict with upstream #813.

Next: [#118](118-narrow-vs-generic-tests.md).
