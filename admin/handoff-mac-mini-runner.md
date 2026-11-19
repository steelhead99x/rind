# Handoff: the merge queue runs rind's tests natively on aarch64

Delete this file before the claim lands. It is notes for the next agent.

Quest: [`quest/m0/mac-mini-runner.md`](https://github.com/kixel-ai/rind/blob/main/quest/m0/mac-mini-runner.md). Claim: [kixel-ai/rind#895](https://github.com/kixel-ai/rind/pull/895), draft, head `steelhead99x:quest/m0/mac-mini-runner`, one empty claim commit on upstream `main` `96404e2f`. Implement on `claude/m0-mac-mini-runner` and merge into `quest/m0/mac-mini-runner` only when the work is ready, so #895 fast-forwards; squash if fork `main` history has been merged in. Never merge fork `main` into the quest branch.

## Why it is parked

The quest's only `## Waiting` item is physical: the Mac mini must be on the network and reachable over SSH with an account that can install Nix and register a runner. As of 2026-11-19 no Mac mini is in the owner's SSH config or on the 192.168.90.0/24 subnet, and the fork has no registered self-hosted runners. The Mac mini validation is outstanding by the owner's decision; until it exists the native aarch64 Linux check runs by hand on the Pi 5 and the Jetson (section 6). The workflow jobs below cannot be verified until a runner exists.

## What this branch has

- `.github/workflows/queue-build.yml`: two draft jobs, `Build (macOS)` on `[self-hosted, rind-queue-arm64, macOS]` and `Build (aarch64 Linux)` on `[self-hosted, rind-queue-arm64, Linux]`, each the same group build the x86_64 job runs (`nix develop --command quest gate just ci "$BASE"`). `.github/actionlint.yaml` declares the one custom label. `actionlint`, `sh/pins.sh` and `sh/alert.sh check` pass. A separate commit, so it can be dropped.
- This note.

## What it cannot show yet, and what to decide

1. **The runner.** Needs the Mac mini's host name and an SSH account (owner). Validation on the Mac mini is the last item; until then the native aarch64 lane is run locally over SSH on the owner's Raspberry Pi 5 and Jetson (no runner is registered on either).
2. **Labels.** GitHub adds each runner's OS and architecture labels (`macOS`, `Linux`, `ARM64`, `X64`) itself, so the only custom label is `rind-queue-arm64`, put on every aarch64 queue runner; `macOS` or `Linux` picks between them. `rind-queue` stays the x86_64 host's alone: a job that asks for `[self-hosted, rind-queue]` never matches an arm64 runner, so the existing job needs no change. Register the runners with `--labels rind-queue-arm64`. **Runner groups are out of scope** (owner, 2026-11-19); the quest's own line about a group that admits only `queue-build.yml` is still the maintainer's to settle where the runners are registered.
3. **Landing order, so a group never waits on a runner that is not there.** Register the runners, then land this workflow, let each job pass a group, then add its context (`Queue build / Build (macOS)`, `Queue build / Build (aarch64 Linux)`) to main's ruleset in dotfiles' `repo-settings`, which owns it. Requiring a context before its runner exists would hang every group.
4. **The aarch64 Linux VM.** Lima or the nix-darwin Linux builder: pick whichever keeps the queue's added time smallest, and record it (the quest asks for this). Not measurable without the machine.
5. **Queue time.** If the Mac mini's build adds more than a few minutes to landing, the PR says so and proposes trimming it to what catches aarch64-only breakage.
6. **Native aarch64 boards that exist today (measured 2026-11-19).** A Raspberry Pi 5 (4 Cortex-A76 cores, 8 GB) and a Jetson Orin Nano (6 Cortex-A78AE cores, 8 GB), neither with Nix. Ran the rind-only subset natively (library tests in debug and release, Wycheproof and crosschecks, and both aarch64 CPU-feature tiers from `build.yml`, `detects_the_expected_cpu` included): about 39 minutes cold on each (24 of them compiling), 0 failures, so no aarch64-only breakage at this commit. Peak RAM of the largest process 1.3 GB, `target/` 2.4 GB. Not run: the rest of the workspace, `SLOW_TESTS=1`, the million-vector ML-KEM test, `just ci` (needs Nix), ctgrind (`crabgrind` needs libclang). Details and tables: https://github.com/steelhead99x/rind/pull/159#issuecomment-6997682697. Verdict: not permanent queue runners (they are the owner's working machines, no Nix, a cold group would add about 39 minutes against a 7 minute build); fine for a manual or nightly native check. With a warm cache and the lane trimmed to what a diff reaches, about 3 to 4 minutes of test time per board.
7. **Agent workstation role and `quest gate`** are configured in the owner's machine configuration, not here.
8. **Warm builds.** [`quest/m0/queue-warm-target.md`](https://github.com/kixel-ai/rind/blob/main/quest/m0/queue-warm-target.md) (claimed upstream by the maintainer) changes `queue-build.yml` too; expect a merge conflict in the build job and resolve it by taking its steps into these jobs.

## Done when

Per the quest: every merge group builds and runs the tests natively on aarch64, on both new runners, and fails the group if they fail; the quest file and its links are deleted in the finishing PR.
