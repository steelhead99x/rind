# [S] The Mac mini joins the benchmark report

## Goal

The maintainer's Mac mini is a host in BENCHMARKS.md, measured by `admin/bench-report collect` like the others, so the report has a desktop Apple-silicon host beside `kixtop`'s M4 laptop.

## Plan

Planned with the maintainer on 2026-11-10. The Mac mini (Apple M5 Pro, `ssh mini`, admin account `kixelated`, Nix installed, `sudo` needs a password) also runs the merge queue's aarch64 Linux runner as a tart VM (`admin/mac-mini-runners`, landed in [kixel-ai/rind#1022](https://github.com/kixel-ai/rind/pull/1022)), benchmarks, and agents.

- ✅ Accept the noise: the machine also runs the merge queue and agents, so it benchmarks under plain `quest gate` like every other host, and its section says so (rejected: a nightly window that pauses the runner and agents; a benchmark-only machine).
- Add it as `kixtop` was added in [kixel-ai/rind#435](https://github.com/kixel-ai/rind/pull/435), and include its first run in the next report refresh.
