# [S] Apple-silicon nightlies run on the Mac mini

## Goal

The scheduled jobs that need Apple silicon run on the maintainer's Mac mini instead of GitHub's `macos-latest` runners, wherever that is faster or lets a job run more often or more completely.

## Plan

Planned with the maintainer on 2026-11-10 ([the runner quest](/quest/m0/mac-mini-runner.md) holds the shared decisions).

- Survey the workflows' macOS jobs (`build.yml`'s macOS and iOS rows, `dart` rows; [the mutants slim-down](/quest/m0/ci-speed/mutants-slim.md) drops `mutants.yml`'s macOS campaign) and move each one that gains from the machine; leave hosted runners where a clean VM matters, such as release builds.
- Keep each moved job under `quest gate` so it shares the machine with the queue and agents.

## Required

- [The merge queue runs rind's tests natively on aarch64](/quest/m0/mac-mini-runner.md) - the machine, set up as a self-hosted runner
