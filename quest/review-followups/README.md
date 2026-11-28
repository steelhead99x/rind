# Review follow-ups for steelhead99x/rind fork PRs

## Goal

Land each fork PR the review notes cover, one quest per PR or small group, in the order below. Nothing goes to upstream until the maintainer says so.

## Plan

Finish bottom to top within each stack:

- bare-metal and ESP32: #87, now steelhead99x/rind#340, is what remains
- arithmetic and protocols: #23 ([its quest](/quest/m2/23-adapter-mutants.md)) is what remains

Closed 2026-11-28, their quests deleted: #118, #82, #69, #94, and #85 (by #181) landed; #84 (fork #154 and upstream kixel-ai/rind#856), #79 (the maintainer rejected its twin, kixel-ai/rind#790, for under 1%), and #102 (closed for upstream kixel-ai/rind#794) were superseded. #76, #39, #64, #117, #106, and #107 merged. #119 is closed: fork `main` already has its fix.

Many PRs sit on a stacked base such as `fork/bench-report`; check a PR's base before retargeting it, because that pulls in the whole stack.

Rules from the review notes:

- Work only on the fork PR branch. Do not push to `up/*` branches.
- Merge upstream changes; never rebase or force-push.
- Merge upstream main only after a clean second review.
- Commit author and committer: steelhead99x.
- Leave the core zeroing ml_dsa Mac failure to upstream #803.
