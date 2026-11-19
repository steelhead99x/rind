# [S] Draft PRs skip the heavy checks until marked ready

## Goal

A draft PR runs none of the heavy path-filtered checks, and marking it ready for review starts them on its head. Converting a ready PR back to draft stops further heavy runs until it is ready again.

## Plan

- ✅ Drafts skip the heavy jobs until marked ready, and a `ready_for_review` event triggers them (rejected: run them on drafts). The maintainer, 2026-11-19.
- Why: on 2026-11-18, 243 of the 793 hosted job-hours pull requests spent ran while the PR was a draft: x86-cpu 81, prove 94, ctgrind 37. Agents open PRs as drafts and push review fixes there, so 72 of the day's 198 cancelled PR job-hours were drafts' superseded runs.
- Skip on drafts: `x86-cpu`, `prove`, `ctgrind`, `build`, `timing`, `fuzz`, and `esp32s3-sha256-layout`. Keep `PR check`, `quality lints`, `regenerate`, and `Site` running on drafts: each takes minutes and is an agent's early signal. Re-check the list against the workflows on `main` when starting, since [kixel-ai/rind#881](https://github.com/kixel-ai/rind/pull/881) and [kixel-ai/rind#859](https://github.com/kixel-ai/rind/pull/859) are changing them.
- `pull_request`'s default types omit `ready_for_review`: list `opened`, `synchronize`, `reopened`, and `ready_for_review`, and skip on `github.event.pull_request.draft` at the job that every other job `needs`, such as x86-cpu's `scope`, so a draft shows one skipped job, not a matrix of them.
- A PR turned back into a draft keeps its earlier ready run, whose event still says `draft=false`. Add `converted_to_draft` to the types, so that event's run joins the PR's concurrency group, cancels the ready run, and then skips. Scheduled and dispatched runs keep their own groups.
- A heavy check that skips on drafts reads as skipped, not failed, so `/quest-review` and the merge flow see nothing red; say in CONTRIBUTING.md's sentence on advisory runs that drafts skip them.
