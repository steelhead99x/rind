# Handoff: the merge queue runs rind's tests natively on aarch64

Delete this file before the claim lands. It is notes for the next agent.

Quest: [`quest/m0/mac-mini-runner.md`](https://github.com/kixel-ai/rind/blob/main/quest/m0/mac-mini-runner.md). Claim: [kixel-ai/rind#895](https://github.com/kixel-ai/rind/pull/895), draft, head `steelhead99x:quest/m0/mac-mini-runner`, one empty claim commit on upstream `main` `96404e2f`. Implement on `claude/m0-mac-mini-runner` and merge into `quest/m0/mac-mini-runner` only when the work is ready, so #895 fast-forwards; squash if fork `main` history has been merged in. Never merge fork `main` into the quest branch.

## Why it is parked

The quest's only `## Waiting` item is physical: the Mac mini must be on the network and reachable over SSH with an account that can install Nix and register a runner. As of 2026-11-19 no Mac mini is in the owner's SSH config or on the 192.168.90.0/24 subnet, and the fork has no registered self-hosted runners. Nothing below can be verified until a runner exists.

## What this branch has

- `.github/workflows/queue-build.yml`: two draft jobs, `Build (macOS)` on `[self-hosted, rind-queue-arm64, macOS]` and `Build (aarch64 Linux)` on `[self-hosted, rind-queue-arm64, Linux]`, each the same group build the x86_64 job runs (`nix develop --command quest gate just ci "$BASE"`). `.github/actionlint.yaml` declares the one custom label. `actionlint`, `sh/pins.sh` and `sh/alert.sh check` pass. A separate commit, so it can be dropped.
- This note.

## What it cannot show yet, and what to decide

1. **The runner.** Needs the Mac mini's host name and an SSH account (owner). Validation on the Mac mini is the last item; until then the native aarch64 lane is run locally over SSH on the owner's Raspberry Pi 5 and Jetson (no runner is registered on either).
2. **Labels.** GitHub adds each runner's OS and architecture labels (`macOS`, `Linux`, `ARM64`, `X64`) itself, so the only custom label is `rind-queue-arm64`, put on every aarch64 queue runner; `macOS` or `Linux` picks between them. `rind-queue` stays the x86_64 host's alone: a job that asks for `[self-hosted, rind-queue]` never matches an arm64 runner, so the existing job needs no change. Register the runners with `--labels rind-queue-arm64`. **Runner groups are out of scope** (owner, 2026-11-19); the quest's own line about a group that admits only `queue-build.yml` is still the maintainer's to settle where the runners are registered.
3. **Landing order, so a group never waits on a runner that is not there.** Register the runners, then land this workflow, let each job pass a group, then add its context (`Queue build / Build (macOS)`, `Queue build / Build (aarch64 Linux)`) to main's ruleset in dotfiles' `repo-settings`, which owns it. Requiring a context before its runner exists would hang every group.
4. **The aarch64 Linux VM.** Lima or the nix-darwin Linux builder: pick whichever keeps the queue's added time smallest, and record it (the quest asks for this). Not measurable without the machine.
5. **Queue time.** If the Mac mini's build adds more than a few minutes to landing, the PR says so and proposes trimming it to what catches aarch64-only breakage.
6. **Native aarch64 boards that exist today** (owner's network): a Jetson Orin Nano (6 Cortex-A78AE cores, 8 GB, on a USB link to one laptop, no Nix) and a Raspberry Pi 5 (4 Cortex-A76 cores, 8 GB, about 27 GB free disk, no Nix). Either could stand in for the aarch64 Linux half, but the queue's `just ci` builds an 11 GB `target/` and compiles AWS-LC, within a 60 minute job limit: unmeasured, and both are likely too small. The Mac mini is the planned machine; I would not register these as queue runners without measuring a full `just ci` on one first.
7. **Agent workstation role and `quest gate`** are configured in the owner's machine configuration, not here.
8. **Warm builds.** [`quest/m0/queue-warm-target.md`](https://github.com/kixel-ai/rind/blob/main/quest/m0/queue-warm-target.md) (claimed upstream by the maintainer) changes `queue-build.yml` too; expect a merge conflict in the build job and resolve it by taking its steps into these jobs.

## Done when

Per the quest: every merge group builds and runs the tests natively on aarch64, on both new runners, and fails the group if they fail; the quest file and its links are deleted in the finishing PR.
