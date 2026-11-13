# [S] The Mac mini joins the benchmark report

## Goal

The maintainer's Mac mini is a host in BENCHMARKS.md, measured by `admin/bench-report collect` like the others, so the report has a desktop Apple-silicon host beside `kixtop`'s M4 laptop.

## Plan

Planned with the maintainer on 2026-11-10 ([the runner quest](/quest/m0/mac-mini-runner.md) holds the shared decisions).

- ✅ Accept the noise: the machine also runs the merge queue and agents, so it benchmarks under plain `quest gate` like every other host, and its section says so (rejected: a nightly window that pauses the runner and agents; a benchmark-only machine).
- Add it as `kixtop` was added in [kixel-ai/rind#435](https://github.com/kixel-ai/rind/pull/435), and include its first run in the next report refresh.

## Required

- [The merge queue runs rind's tests natively on aarch64](/quest/m0/mac-mini-runner.md) - the machine, set up and reachable
