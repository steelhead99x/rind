# [M] PR checks stop running for results no one reads

## Goal

Every heavy pull-request workflow either gates the merge or returns its result before the PR usually moves on, and the rest run nightly. A check is then rarely cancelled by a newer push, and never still running after its PR merged. The PR records each workflow's choice with its measured cancelled and post-merge hours before and after.

## Plan

The maintainer's decision, 2026-11-19:

> figure out how to avoid canceling. Like these should be required checks if we're cancelling because of a merge. If we're cancelling because of a review, whatever I guess speed up the checks or move them to nightly.

The orchestrator's reading, ✅ confirmed by the maintainer on 2026-11-19 (rejected: another meaning): a check whose PR merged while it ran never gated anything, so it becomes a gating check, required or run in the merge queue. A check that newer pushes, such as review fixes, keep cancelling is made faster or moved to nightly. Since no PR run was cancelled because its PR merged, the merge case is the checks still running when their PR merged, also confirmed by the maintainer. Measure each workflow's causes before choosing for it.

Measured on 2026-11-18 from the Actions REST API, hosted job-hours only:

- No PR run was cancelled because its PR merged. Merges waste time another way: 43 hosted hours were still running after their PR had merged, so their results gated nothing: prove 21, x86-cpu 18, ctgrind 4.
- A newer push to the same branch cancelled 197 hours in 142 runs: x86-cpu 71, prove 66, ctgrind 29, Site 8, PR check 7, regenerate 6, lints 4. 19 of those pushes merged `main` into the branch; the rest were other commits, mostly review fixes. The newer push came a median 28 minutes after the cancelled run started (p25 13, p75 58).
- 72 of the day's 198 cancelled PR hours were on drafts. Since [kixel-ai/rind#906](https://github.com/kixel-ai/rind/pull/906), drafts no longer run the seven heavy workflows, only Site, PR check, regenerate, and lints, so the re-measure shows how much of those 72 hours is left. Hand-cancelled `bench` dispatches (21 hours) and the armv7 debug rows at their 6-hour limit (14 hours, fixed since by [kixel-ai/rind#843](https://github.com/kixel-ai/rind/pull/843)) are out of scope.

Recommendations:

- Re-measure after the cuts this quest requires land, then choose per remaining workflow; many of the cancelled hours go with them.
- Gate through the merge queue rather than a required context: a path-filtered workflow cannot be a required check, and [kixel-ai/rind#881](https://github.com/kixel-ai/rind/pull/881) runs a workflow's check inside the queue's self-hosted build when the group's diff touches its `pull_request` paths (`CHECK_QUEUE` in `sh/dispatch.sh`), since hosted runners' queue waits would run into the group's timeout. Reuse it. [kixel-ai/rind#911](https://github.com/kixel-ai/rind/pull/911) already runs every SDE path set in the queue that way. A check moved into the queue slows the gate, so the PR says by how much and why it is worth it. `main`'s ruleset comes from dotfiles' `repo-settings`, so change it there if a required context changes.
