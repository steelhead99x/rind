# [M] Landing a PR costs one short build

## Goal

Landing a PR costs one short build. The merge queue batches several PRs into each group and gates only on fast checks. Everything else (aarch64, macOS, the slow modules) runs batched on `main` after the merge, coalesced, and files a quest when it fails. The PR records the compute spent per merged PR, before and after.

## Plan

Planned with the maintainer on 2026-11-27 (`/quest-run`), who asked for less compute to merge and for batched tests, such as nightly runs, instead.

- Measured 2026-11-27, before [kixel-ai/rind#1150](https://github.com/kixel-ai/rind/pull/1150) removed the macOS queue job:
  - Ruleset 26261478 builds one PR per group (`max_entries_to_build` 1, `max_entries_to_merge` 1, `ALLGREEN`).
  - `Queue build / Build` (x86_64 `just ci` with `CHECK_QUEUE`) takes about 5 min on `nixos-rind-ci`, up from the 1–2 min [the epic](/quest/m0/ci-speed/README.md) set on 2026-11-21.
  - `Build aarch64 Linux` (the `rs` module) takes about 4 min on the Mac mini's Linux VM.
  - Every PR push also runs `PR check` (about 12 min, hosted, `just ci` over the diff) and `PR macOS` (hosted).
- ✅ A child of the ci-speed epic, in m0 (rejected: keeping aarch64 gating as the only change; dropping it now that #1150 removed macOS). The gate blocks every PR.
- Measure first, then cut. Recommended:
  - Group several PRs per merge group, with a short `min_entries_to_merge_wait_minutes`, so one build covers several PRs. Check how GitHub bisects a failed group, and how quest's queue watcher and land fixer handle a group of several PRs.
  - Bring the queue build back to the epic's 1–2 min (`mbx`-warm `rs` plus quick lints, as [queue-warm-target](/quest/m0/queue-warm-target.md) plans).
  - Trim `PR check` to what a push needs.
- The maintainer decided on 2026-11-26 that aarch64 gates merges ("x86 and aarch can block merges. Optional CI is dumb."). Today's ask, to rely on batched tests, may reverse that. Measure what aarch64 gating costs per merged PR once groups batch, then put the choice under `## Waiting` with the numbers. Don't remove it without that answer.
- A check that moves off the gate runs on each push to `main`, coalesced, plus nightly. Its failure files a quest through the existing nightly path. Nothing is optional and unread.
