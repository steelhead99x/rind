# [M] ML-DSA parity harness refusal kinds

## Goal

ML-DSA refuses malformed keys with the same error kinds as aws-lc-rs, with a clear choice between exact kinds and cheap length checks.

## Plan

Difficulty: 5/10 (estimate).

Fork PR #117, base `cursor/mldsa-error-kinds-71e2`, head `4f0c90fe`. Score 9/10, fork only. No findings left; the approach needs a decision.

- Option A: keep the exact aws-lc-rs refusal kinds. A wrong-set key is fully expanded first, and ctgrind covers that path.
- Option B: refuse by length up front. This is cheaper, but an inconsistent wrong-set key then returns `Unspecified` instead of `InvalidEncoding`.

## Waiting

- Maintainer: pick option A or B before merging, then say which here

## Related

- [Close #109](/quest/review-followups/README.md) - superseded by this branch plus #117
