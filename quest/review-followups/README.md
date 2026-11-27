# Review follow-ups for steelhead99x/rind fork PRs

## Goal

Land each fork PR the review notes cover, one quest per PR or small group, in the order below. Nothing goes to upstream until the maintainer says so.

## Plan

Finish bottom to top within each stack:

- bare-metal and ESP32: #84, #85, #87, #69, #94, #102
- aarch64: #82, then #118
- arithmetic and protocols: #76, #39, #64, #23 can go in any order

Independent PRs: #117, #79, #798, #799, #800, #106, #107. #119 is closed: fork `main` already has its fix.

Many PRs sit on a stacked base such as `fork/bench-report`; check a PR's base before retargeting it, because that pulls in the whole stack.

Rules from the review notes:

- Work only on the fork PR branch. Do not push to `up/*` branches.
- Merge upstream changes; never rebase or force-push.
- Merge upstream main only after a clean second review.
- Commit author and committer: steelhead99x.
- Leave the core zeroing ml_dsa Mac failure to upstream #803.

## Waiting

- Maintainer: close #109 and give its error-kinds work its own fork PR onto `fork/mldsa-aws-lc-rs`
