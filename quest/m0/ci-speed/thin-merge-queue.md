# [M] Thin the self-hosted merge queue to host rs and fast lints

## Goal

`queue-build.yml` on the self-hosted `rind-queue` runner runs only host `rs` checks and sub-second repository lints, dropping `sde`, `vg`, `regenerate`, `cross`, `wasm`, `msrv`, `adapters`, `vartime`, and `site` from the merge queue so a merge group completes in ~1–2 minutes (once warm under `mbx`) instead of 15 minutes and 5.5 CPU-hours. Nightly/weekly workflows (`check.yml`, `x86-cpu.yml`, `prove.yml`, `regenerate.yml`) and `just release-check` continue to run the full unscoped suite asynchronously.

## Plan

Measured across the 15 merge-queue runs ending 2026-11-22: median 15.0 min wall (max 17.7 min) and 5.5 CPU-hours per run. `check sde` (added in [kixel-ai/rind#911](https://github.com/kixel-ai/rind/pull/911)) consumed 72.7% of all runner CPU (14.1m median wall), followed by `check cross` (11.4m), `check rs` (11.1m), `check vg` (5.9m, added in [kixel-ai/rind#881](https://github.com/kixel-ai/rind/pull/881)), `check wasm` (4.7m), `check adapters` (4.6m), `check msrv` (4.0m), `check vartime` (2.8m), `check regenerate` (2.2m, `#881`), and `check site` (1.0m on every run). Hosted runner waits have since dropped back to 2–5s.

- ✅ Keep `rind-queue` strictly minimal (`mbx`-warmed host `rs` + sub-second repo lints) and move `sde`, `vg`, `regenerate`, `cross`, `wasm`, `msrv`, `adapters`, `vartime`, and `site` off the merge queue into nightly/weekly batching (maintainer, 2026-11-21; rejected: retiring `rind-queue` completely onto hosted runners; removing only `sde`/`vg`/`regenerate`).
- ✅ Rare two-PR merge interactions in the offloaded checks are caught asynchronously by nightly/weekly runs and fixed in `m0` rather than gated in `merge_group` (maintainer, 2026-11-21; rejected: parallel hosted `merge_group` jobs; gating `cross`/`msrv`/`wasm`/`adapters`/`vartime` in `merge_group`).
- ✅ `py`, `dart`, `openssl`, and `patch` leave the queue and gate no merge, so changes to `rind-python`, `rind-dart`, `rind-openssl`, or `patch/` get no check before merge: they run batched after merge, nightly `check.yml` (maintainer, 2026-11-24, [kixel-ai/rind#962](https://github.com/kixel-ai/rind/pull/962#issuecomment-7124239070); rejected: keeping them in `pr-check.yml`, path-scoped). Merging waits on no slow or expensive test; such tests batch after merge instead. GitHub-hosted runners are exhausted and the maintainer is moving CI off them, so these batched runs may move to self-hosted runners; either way, make them fast (`sh/python.sh` builds a release wheel and runs its suites).
- Remove the `vg`, `regenerate`, and `sde` queue modules from `sh/dispatch.sh`, and select only host `rs` and the fast lint modules (`deny`, `versions`, `license`, `testing`, `audit`, `compat`, `bench`, `quest`, `gh`, `shell`, `nix`, plus `structure`/`mutants`/`fixtures` only if kept under a few seconds—measure and drop slow ones to nightly `check.yml`). Keep `just ci --all` (`check.yml`) running every module nightly.
- The queue gates no proofs: [kixel-ai/rind#958](https://github.com/kixel-ai/rind/pull/958) landed without a `proved` queue module, since the maintainer decided on 2026-11-24 that proofs gate releases, not merges. With `vg`, `regenerate`, and `sde` gone, `CHECK_QUEUE` selects nothing, so remove it, its block and the queue lanes in `sh/dispatch.sh`, its setting in `queue-build.yml`, and the comments and CONTRIBUTING.md text that name it. With `sde` and `regenerate` out of the queue, `x86-cpu` and `regenerate` run only on their weekly and nightly schedules, as decided above.
- `pr-check.yml` runs the same selection as the queue, so a group's failure shows on its PR first: give it the same module set plus the path-scoped `site` module that [site-scope](/quest/m0/ci-speed/site-scope.md) keeps on pull requests, leaving `cross`, `msrv`, `wasm`, `adapters`, `vartime`, `py`, `dart`, `openssl`, and `patch` to nightly `check.yml` and `just release-check` (maintainer, 2026-11-21; rejected: keeping them in `pr-check.yml`).
- Upload `target/cargo-timings/cargo-timing-*.html` from `queue-build.yml` (like `moq-dev/moq`'s `.github/workflows/queue.yml`) so future compile regressions show up without manual profiling.
- Note that `queue-build.yml` runs main's copy, so edits to `queue-build.yml` take effect on the merge group after this PR lands, and `queue-build.yml` must use no local actions (`sh/dispatch.sh`'s `check:gh` enforces this).
- Update [CONTRIBUTING.md](/CONTRIBUTING.md) where it documents what the merge queue runs.

## Required

- [Scope check:site to site inputs and drop its duplicate PR run](/quest/m0/ci-speed/site-scope.md) - gives release-plz's release PRs a site check in `pr-check.yml`, which skips them today, so dropping `site` from the queue leaves them checked before merge

## Related

- [The merge queue builds through mbx, warm across groups](/quest/m0/queue-warm-target.md) - eliminates the cold-build penalty on `rind-queue`
- [The merge queue runs rind's tests natively on aarch64](/quest/m0/mac-mini-runner.md) - benefits directly from the thinner queue gate
- [PR checks stop running for results no one reads](/quest/m0/ci-speed/unread-results.md) - [kixel-ai/rind#958](https://github.com/kixel-ai/rind/pull/958) moved the heavy PR workflows to their schedules and made the proofs gate releases instead of merges
