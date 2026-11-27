# [S] The weekly bench counts instructions with rust2's Valgrind runner, not CodSpeed

## Goal

The `codspeed` job in `.github/workflows/bench.yml` runs the bench targets under stock Valgrind through kixel-ai/rust2's runner instead of the CodSpeed Action and cargo-codspeed. It uploads each benchmark's instruction count as a `kixel-metrics` artifact for Kixel Quest, and it needs no `id-token: write`.
A `benchmarks` input on its `workflow_dispatch` trigger takes the newline-separated benchmark IDs a Kixel Quest bisect step passes, and the job then measures only those.

Non-goals: changing the weekly cadence, and the wall-clock rows against aws-lc-rs and ring, which stay as they are.

## Plan

Decided 2026-11-23 (maintainer, `/quest-plan` in kixel-ai/kixel.quest, [kixel-ai/kixel.quest#113](https://github.com/kixel-ai/kixel.quest/pull/113)):

- ✅ Replace CodSpeed with stock Valgrind through our own runner, reporting only to Kixel Quest, in moq-dev/moq, kixel-ai/rust2, and kixel-ai/rind (rejected: moq only for now; keep CodSpeed). No third-party service stays in the loop, and an agent gets the same count locally that CI reports.
- ✅ Our own parallel Valgrind runner in kixel-ai/rust2, reading the per-benchmark markers `codspeed-criterion-compat` already emits, so `rind-bench`'s benchmarks run unchanged (rejected: rewriting them to Gungraun; writing our own harness first). A Criterion replacement is planned in rust2 too; moving `rind-bench` to it is a later quest, once it ships.
- ✅ No benchmark runs on PRs, since benchmarks never gate; agents compare locally (rejected: per-PR job-summary tables).
- ✅ Scheduled runs, with Kixel Quest bisecting a regression to its PR, one step per commit, measuring only the regressed benchmarks (rejected: a run on each landing). rind's weekly schedule stays.
- ✅ GitHub-hosted runners (rejected: self-hosted).

Recommendations for the implementer:

- The three shards exist only because CodSpeed refuses an upload with too many benchmarks. Without the upload, run one job and let the runner spread benchmarks over the runner's cores. Split again only if one job's time measures too long, and say why.
- Take Valgrind and the runner from Nix: Valgrind from the flake's pinned nixpkgs, as `devShells.ctgrind` already does, and the runner as a pinned kixel-ai/rust2 flake input, or `cargo install --git` at a pinned rust2 rev. A Valgrind or runner upgrade can shift counts, so it should land as a visible pin bump, not a runner image change.
- Keep the `__bench_codspeed` feature: it switches `rind-bench` to `codspeed-criterion-compat`, whose markers the runner reads. Rename it only if the runner's docs name a better one.
- Valgrind hides AVX-512, VAES, VPCLMULQDQ, and SHA on x86_64, and SHA3 and SVE2 on aarch64 (see `ctgrind.yml`), so the counts measure whatever backend the job's target compiles, as under CodSpeed today. Say in `TESTING.md` which one that is.
- Keep the existing `benches` input for bench targets beside the new `benchmarks` input for benchmark IDs, and have Kixel Quest's bisects pass only `benchmarks`.
- The Kixel Quest App is installed on every kixel-ai repository (checked 2026-11-23), so the artifact is read once this lands.

Public API: none.

## Waiting

- kixel-ai/rust2: its Valgrind runner, `quest/m1/bench-runner.md` in its quest tree; check that the file is gone from rust2's `main`.
