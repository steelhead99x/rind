# [M] Ed25519 CCTV and wipe canaries

## Goal

The Ed25519 checks run in the right CI lanes with the right coverage, and the ML-DSA wasm part is trimmed to avoid overlap.

## Plan

Difficulty: 5/10 (estimate).

Fork PR #64, head `4f74eebb`. Score 7/10. Upstream twin #797. Base `fork/mldsa-aws-lc-rs`. Grok's full fix for all nine findings is saved as `forkpr-64-partial-grok.diff`, but no one has reviewed it.

Mediums:
- The getrandom check belongs in `check:wasm`, not the cross lane.
- Remove the promised nightly `build.yml` run of just wasm.
- The 32-bit RSA keygen run skips the debug and overflow checks.

Also:
- Commit it without the "fork has no build.yml" wording.
- Trim the ML-DSA wasm part that upstream #708 already covers.
- Merge after upstream #609.
