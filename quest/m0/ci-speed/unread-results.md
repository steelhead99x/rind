# [S] PR checks stop running for results no one reads

## Goal

Every heavy pull-request workflow either gates the merge or returns its result before the PR usually moves on, and the rest run nightly. A check is then rarely cancelled by a newer push, and never still running after its PR merged. The PR records each workflow's choice with its measured cancelled and post-merge hours before and after.

## Plan

The maintainer's decision, 2026-11-19:

> figure out how to avoid canceling. Like these should be required checks if we're cancelling because of a merge. If we're cancelling because of a review, whatever I guess speed up the checks or move them to nightly.

The orchestrator's reading, ✅ confirmed by the maintainer on 2026-11-19 (rejected: another meaning): a check whose PR merged while it ran never gated anything, so it becomes a gating check, required or run in the merge queue. A check that newer pushes, such as review fixes, keep cancelling is made faster or moved to nightly. Since no PR run was cancelled because its PR merged, the merge case is the checks still running when their PR merged, also confirmed by the maintainer. Measure each workflow's causes before choosing for it.

Hosted job-hours per day of `pull_request` runs, from the Actions REST API: cancelled, then still running when their PR merged (whole runs). "Before" is 2026-11-18; "after cuts" is 2026-11-20 06:03 UTC, when [kixel-ai/rind#911](https://github.com/kixel-ai/rind/pull/911) landed after [kixel-ai/rind#906](https://github.com/kixel-ai/rind/pull/906), [kixel-ai/rind#881](https://github.com/kixel-ai/rind/pull/881), and [kixel-ai/rind#843](https://github.com/kixel-ai/rind/pull/843), to 2026-11-22 05:46 UTC.

| workflow | cancelled before | after cuts | post-merge before | after cuts |
| --- | --- | --- | --- | --- |
| prove | 91.0 | 43.0 | 22.9 | 16.0 |
| x86-cpu | 75.7 | 1.1 | 26.3 | 1.2 |
| ctgrind | 32.7 | 2.3 | 6.7 | 3.6 |
| PR check, Site, regenerate, lints, timing, build, fuzz, ESP32 | 29.0 | 1.9 | 0.4 | 1.1 |

[kixel-ai/rind#958](https://github.com/kixel-ai/rind/pull/958) made `prove`'s HOL Light keys change only with the code: 64 of its 79 ready runs had re-run HOL Light aarch64 (58 minutes each), because `asm_function`'s objects kept names that a version bump, a lockfile change, or an unrelated edit changes.

The maintainer's decisions, 2026-11-22, on #958:

- ✅ Gate in the merge queue only the HOL Light targets whose cache key `main` hasn't already passed, once `lean` has a cache key of its own (rejected: leave `prove` advisory; gate all of `prove`).
- ✅ "A lot of these non blocking PR checks should be nightly or weekly runs": a PR check that doesn't gate the merge moves off pull requests to a nightly or weekly run, and only gating checks stay on PRs (rejected: keeping advisory checks on PRs). This supersedes keeping `ctgrind` advisory on PRs, and the 2026-11-18 decisions in the [epic](/quest/m0/ci-speed/README.md) on what pull requests run.

✅ The same day the maintainer picked how the HOL Light gate works (rejected: running the proofs in the queue's build, whose 60-minute limit the aarch64 proofs alone fill; gating only x86_64 and armv7), that `lean` gates the same way (rejected: nightly only), and that PR check becomes a required check, which dotfiles' `repo-settings` sets for kixel-ai's rulesets (rejected: dropping it).

The maintainer's decisions, 2026-11-24, on #958 ([first](https://github.com/kixel-ai/rind/pull/958#issuecomment-7136993777), [refining it](https://github.com/kixel-ai/rind/pull/958#issuecomment-7137035248)), which supersede the proof gate above, following the direction on [kixel-ai/rind#962](https://github.com/kixel-ai/rind/pull/962#issuecomment-7124239070) not to gate merging on slow or expensive tests:

- ✅ The proofs gate no merge: they run batched after merge, on each push to main for the keys main lacks and nightly in full, and a failure alerts (rejected: keeping the merge-queue gate and fixing how it picked main's last `prove` run).
- ✅ The proofs gate releases: a release publishes only once they passed on the commit it releases (release-plz's PR or the publish job, whichever is the right choke point).

#958 put the release gate in `release.yml`'s publish path (`sh/release-proved.sh`), its implementer's choice for review: that job is the only step that publishes and the only one that knows the exact commit, while release-plz's PR is tested at a head its squash commit can differ from.

The maintainer's decision, 2026-11-24, at the review's design checkpoint ([comment](https://github.com/kixel-ai/rind/pull/958#issuecomment-7138298450)): ✅ drop `prove.yml`'s per-key job concurrency groups, so no run on main is cancelled and the release gate reads how a run ended, with no reruns and no `actions: write` (rejected: gate on saved per-key results; wait only for the runs unfinished when a cancellation is seen; merge with the reruns). Two overlapping pushes that both lack a key now both check it.

What #958 did with each pull-request check:

| check | now | why that cadence |
| --- | --- | --- |
| `ctgrind` (x86_64 release row, BINSEC) | weekly | already weekly in full |
| `build` (armv7, portable, Dart, openmls) | nightly | already nightly |
| `fuzz` (target builds) | weekly | the weekly fuzz builds them first |
| `timing` (smoke build) | dropped | the weekly Marvin run builds the same crate |
| `lints` (aarch64 clippy) | nightly | the queue already clippies `rind` for aarch64 |
| ESP32-S3 SHA-256 layout | weekly (new) | one 30-minute job on code that rarely moves |
| `x86-cpu` (three SDE models, ACVP on Diamond Rapids) | weekly | the queue runs every path set |
| `regenerate` | nightly | the queue runs it on its inputs |
| `prove` HOL Light, `lean`, `cosim`, bytes | on a push to main, each but the bytes only for a key main lacks; nightly in full | gates a release, not a merge (`sh/release-proved.sh`) |
| `prove` `vg`, `neon`, `spec-tests` | nightly | the queue runs x86_64's `vg`; the rest gate nothing |
| Site | dropped | PR check and the queue run the same `sh/site.sh` |
| PR check | kept, to be required | a group the queue ejects costs a slot in a one-group-at-a-time queue |

Left: re-measure cancelled and post-merge hosted hours over the week after #958 lands, the same way (the script is in #958's Validation), and record them in the table above; then delete this quest.

## Scheduled

- 2026-11-30 - a week of runs after #958 lands

## Related

- [The merge queue runs rind's tests natively on aarch64](/quest/m0/mac-mini-runner.md) - a second queue runner, which a queue module must not slow
