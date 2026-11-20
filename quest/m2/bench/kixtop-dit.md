# [S] kixtop is remeasured with DIT held for every rind row

## Goal

Every `rind` time in `kixtop`'s table is timed with `rind::cpu::Dit::hold()` held, as the report's one rind column says, so its host note, the README, and `benchmarks/gaps.toml` drop their exception for rows timed with rind's per-call DIT.

## Plan

Kept by the maintainer on 2026-11-18 ([comment](https://github.com/kixel-ai/rind/pull/619#issuecomment-6996473088)).

[kixel-ai/rind#619](https://github.com/kixel-ai/rind/pull/619) made the bench hold DIT for every rind row, but `kixtop` was offline, so the report kept its 2026-11-12 run on [`0d2e74b4`](https://github.com/kixel-ai/rind/commit/0d2e74b489c1067beeab373f9de75d24574b4bc5). That run held DIT for 28 of rind's 68 rows; the other 40 paid the per-call toggle, which cost 20 to 120 ns a call in the run before.

- Run `admin/bench-report collect --host kixtop`, and go on only if it records `kixtop` with status `ok`; a busy, unreachable, or failed host is skipped and the old data stays.
- Recheck the `kixtop` SHA3-256/512 at 64 B entry in `benchmarks/gaps.toml`, which blames the toggle, and triage any gap the new rows show that nobody decided, before the first `render --from`: `load_gaps` refuses a decision that covers no gap, and a gap with none.
- Remove the per-call sentences from `kixtop`'s note in `admin/bench-report`'s `HOSTS` and the exception from the README's sentence on Apple silicon, then `render --from` the collection's directory, which imports its `kixtop.json` and writes that note into the host page, and those decisions into `BENCHMARKS.md`'s gap table and the site.
- The rustls rows now also run rustls' own code with DIT on. Say in the PR how they moved against the per-call run.

## Hosts

- macos - `kixtop` is the report's Apple M4

## Waiting

- Maintainer: bring `kixtop` online and idle (a laptop in daily use, offline on 2026-11-18); check with `ssh kixtop true`, and `collect` refuses it while it is busy
