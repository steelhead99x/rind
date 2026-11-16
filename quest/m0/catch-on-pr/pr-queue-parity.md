# [S] PR checks run the queue's cheap modules

## Goal

Every module `just ci` runs in the merge queue that a PR's diff reaches and that takes minutes, not hours, also runs on that PR, so a PR that passes its checks does not fail the queue on a check it never ran.

## Plan

- PRs never run `just ci`: `check.yml` runs it on pushes to main, and `queue-build.yml` runs `quest gate just ci "$BASE"` on merge groups only. So `sh/dispatch.sh`'s `check:mutants` (`admin/mutants --pins`) and `check:rs`'s second `cargo fmt` pass with `.rustfmt.unstable.toml` first see a change in the queue. kixel-ai/rind#748 failed the queue on the unstable rustfmt import order, and kixel-ai/rind#758 on stale mutants pins, after passing every PR check.
- Run `just ci` with the PR's base on pull requests, through the same `ci-select` scoping `check.yml` uses, on a GitHub-hosted runner with `check.yml`'s Rust cache. Leave out only the modules too slow for a PR, and say in the workflow which ones and why. Keep [the hosted-runner trim](/quest/m0/ci-speed/hosted-trim.md)'s budget in mind: state the job's hosted minutes per PR in the PR body.
- Make the PR job a required check only if the ruleset already requires a job it can replace; otherwise leave it advisory and say so in the PR.
