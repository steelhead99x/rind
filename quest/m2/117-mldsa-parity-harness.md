# ML-DSA parity harness refusal kinds

Difficulty: 5/10 (estimate)


## Goal

ML-DSA refuses malformed keys with the same error kinds as aws-lc-rs, with a clear choice between exact kinds and cheap length checks.

## Plan

Fork PR #117, base `cursor/mldsa-error-kinds-71e2`, head `4f0c90fe`. Score 9/10, fork only. No findings left; the approach needs a decision.

- Option A: keep the exact aws-lc-rs refusal kinds. A wrong-set key is fully expanded first, and ctgrind covers that path.
- Option B: refuse by length up front. This is cheaper, but an inconsistent wrong-set key then returns `Unspecified` instead of `InvalidEncoding`.

## Decision needed

Pick A or B before merging.

## Related

- [ML-DSA zeroing check](119-mldsa-zeroing-check.md)
- [Close #109](../README.md) - superseded by this branch plus #117
