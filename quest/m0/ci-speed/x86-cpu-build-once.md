# [S] x86-cpu builds its tests once and runs them under every SDE model

## Goal

`x86-cpu.yml` builds the release test binaries in one job, and each SDE model's job runs those binaries instead of rebuilding them. Every model runs the same tests it runs today.

## Plan

- ✅ Build once, run under every model: a cut with no loss of coverage (rejected: keep a build per model). The maintainer, 2026-11-19.
- Why: on 2026-11-18, 874 successful model jobs had a median 13.4 minutes, of which the build step took 6.2 and the tests 5.8; builds were 39% of their job time, and x86-cpu was the largest hosted workflow that day at 324 hosted hours.
- Recommended: `cargo nextest archive` in the build job, with the archive passed as an artifact, and `cargo nextest run --archive-file` with SDE as the target runner in each model's job. The `.#sde` shell the model jobs use lacks `cargo-nextest`, which only the `default` and `miri` shells carry, so add it there. It skips doc tests, which `cargo test` runs today: run the doc tests natively once, or keep them per model only if one exercises a CPU path, and say which in the PR.
- The model jobs still need the checkout, for the vector files the tests read, but no Rust cache or build.
- [kixel-ai/rind#893](https://github.com/kixel-ai/rind/pull/893) plans `sde-pr-models.md`, which cuts pull requests to three models; the two compose, and whichever lands second merges the other's matrix changes.
- Give the workflow's hosted minutes per run before and after in the PR.
