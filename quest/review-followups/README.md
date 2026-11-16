# Review follow-ups for steelhead99x/rind fork PRs

Draft quests written by hand from the review notes (not yet validated with the `quest` CLI). Each file maps to one fork PR or a small group of PRs. Milestones follow rind's quest plan: m0 holds urgent fixes (broken CI, data-loss risks), m2 holds the rest of the follow-up work.

## Order

Finish bottom to top within each stack:

- bare-metal and ESP32: #84, #85, #87, #69, #94, #102
- aarch64: #82, then #118
- arithmetic and protocols: #76, #39, #64, #23 can go in any order

Independent PRs: #117, #119, #79, #798, #799, #800, #106, #107.

## Rules (from the review notes)

- Work only on the fork PR branch. Do not push to `up/*` branches.
- Merge upstream changes; never rebase or force-push.
- Merge upstream main only after a clean second review.
- Commit author and committer: steelhead99x.
- Leave the core zeroing ml_dsa Mac failure to upstream #803.

## Status of this workspace

- GitHub access for this session is read-only (public clone only). Nothing here can be pushed until push access is granted.
- Closing #109: close it, and give error-kinds its own fork PR onto `fork/mldsa-aws-lc-rs`.

## Files

m0: 107-bench-report-host-slugs.md, 106-alert-on-cancel.md
m2: all others
