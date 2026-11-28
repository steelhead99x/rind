# [S] The nightly coverage gate passes, and stops failing on drift alone

## Goal

Main's nightly `coverage` run passes. Each file that fell below the baseline has its coverage restored by tests, or a baseline lowered for a reason recorded in the PR. Coverage lost in a merge then shows up where it can be fixed, not as an unowned red nightly.

## Plan

Planned with the maintainer on 2026-11-27 (`/quest-run`, found by [kixel-ai/rind#1137](https://github.com/kixel-ai/rind/pull/1137)).

- The `gate` job has failed since 2026-11-26 ([run 45923288147](https://github.com/kixel-ai/rind/actions/runs/45923288147)), against the baseline:
  - `rind/src/high/kem.rs`: 13 uncovered regions, against 1.
  - `rind/src/mid/mlkem.rs`: 12 regions and 6 branches, against 11 and 4.
  - `rind/src/low/ct.rs`: 2 unrun copies, against 0.
  - `rind-aws-lc-rs/src/buffer.rs`: 12 unrun copies, against 11.
- Find the PR behind each regression with blame, and list it under `## Caused by`. Add tests where the uncovered code is reachable, and lower the baseline only for code no test can reach.
- Recommended: so coverage lost in a merge doesn't strand the nightly, have it fail the PR that loses it. That fits [merge-gate-batching](/quest/m0/ci-speed/merge-gate-batching.md)'s rule that a post-merge failure files a quest. Settle how in this quest's PR.
