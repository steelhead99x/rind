# [S] The benchmark report gets a quiet run on desktop

## Goal

`desktop`'s data in `benchmarks/data/` comes from a quiet, successful `admin/bench-report collect` at a commit on `main` that has rind 0.4's breaking changes, rendered into `BENCHMARKS.md` with its gaps triaged as a report refresh does. The bench epic's README records a dependable way to get a quiet window on a host that CI runners and agent sessions share.

## Plan

Decided 2026-11-24 (maintainer): ✅ refresh with the quiet hosts and re-measure nixos, desktop, and fedora in a follow-up quest (rejected: hold 0.4 until every host runs quiet; pause the runners and sessions now). The maintainer asked for this quest, so it is kept.

- The 0.4 refresh ([kixel-ai/rind#991](https://github.com/kixel-ai/rind/pull/991)) got quiet runs on `nixos` and `fedora` after about ten hours of retries, so only `desktop` remains. Its data is from 2026-11-07 at `9e7f6a5a`.
- Over 21 hours (2026-11-24, 02:14 to 23:35 UTC), that PR tried `desktop` 91 times, about every ten minutes, with `admin/bench-report`'s own busy and noise checks unchanged:
  - 89 tries found 2.4 to 23.8 of its 24 CPUs busy before the build, against the limit of 2.4.
  - The 2 runs that started were noisy, with 14.4 and 14.7 other CPUs busy.
  - Its load average stayed around 25 to 32, from agents' Rust builds, Lean, HOL Light, and qemu jobs.
- Retrying alone did not work within a day, so first find a way to get the window. The options:
  - a hold that `quest gate` honors, so no new gated work starts on the host while `collect` runs and the work already running drains. This needs a `quest` change.
  - running `collect` at an hour when the fleet is idle.
  - the maintainer pausing the host's runners and sessions for 45 minutes.
- Then run `admin/bench-report collect --host desktop` and `render --from`.
  - Triage new gaps into speed quests or reasons in `benchmarks/gaps.toml`.
  - Read its every-logical-CPU handshake rows against its last run and against aws-lc-rs.
- The refresh's collections predate [kixel-ai/rind#964](https://github.com/kixel-ai/rind/pull/964), so no host times its SLH-DSA, one-record rustls, and DIT-per-call rows yet. Once the window works, collect every host the same way, so those rows get host data, triaging their gaps like any other.
- Record what got the window in [the bench epic's README](/quest/m2/bench/README.md), so the next minor release's refresh can use it on every shared host.
