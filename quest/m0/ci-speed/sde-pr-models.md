# [S] Pull requests run three SDE models; the merge queue and the weekly run run them all

## Goal

On a pull request whose diff reaches x86_64, `x86-cpu.yml` runs three Intel SDE models: Prescott, which takes every slowest path; one AVX2 tier; and Diamond Rapids, the newest. The merge queue and the weekly run keep every model.

## Plan

Decided with the maintainer on 2026-11-18 (/quest-plan): ✅ three models on pull requests, every model in the merge queue and weekly (rejected: keep every model on pull requests). Why: after [kixel-ai/rind#743](https://github.com/kixel-ai/rind/pull/743) and [#808](https://github.com/kixel-ai/rind/pull/808), pull requests still spent about 434 hosted machine-hours on x86-cpu in the 30 hours from 2026-11-17 12:00 UTC (165 runs). Nearly every change to `rind/src` reaches x86_64, so the epic's "only the tiers the diff can reach" ran all of them.

- This refines [the epic](/quest/m0/ci-speed/README.md)'s SDE decision. Every tier must still run before code lands, in the merge queue, so a tier-specific fault is caught there, not a week later. Today it does not: `x86-cpu.yml` has no `merge_group` trigger, and main's ruleset requires only `Queue build / Build`. Add every model to the queue, as `merge_group` jobs the ruleset requires or inside the queue build. A required check must report on every pull request or GitHub never admits it to the queue, so follow `queue-build.yml`'s pattern: one gate job that skips, and so passes, on a pull request, and runs or waits on every model in the merge group. The rollout PR's own merge group runs main's `queue-build.yml`, and pull-request runs are not required, so land the queue gate in its own PR first, and drop models from pull requests only once main's queue runs them all.
- `x86-cpu.yml`'s `pull_request` paths miss paths `sh/backends.sh` counts as reaching every backend, such as `rind/build.rs`, which picks the backend, and `rind/tests/**`; add every such path.
- Pick the AVX2 model from `admin/x86-cpus` as the one whose dispatch set covers the most hot paths (Skylake server or Haswell), and say why in the workflow comment.
- The merge queue must not slow down noticeably: run the models as parallel jobs, as `x86-cpu.yml` already does, and give the queue's wall time before and after in the PR, as `quest context` requires for anything that slows the gate. If the slowest model dominates, say so and propose a split. Every model must also finish inside the queue's 90-minute window, hosted-runner wait included (p90 84 minutes on 2026-11-18, per [the epic](/quest/m0/ci-speed/README.md)); if they cannot, run them in the queue build on the self-hosted runner.
