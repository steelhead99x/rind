# Handoff: Apple-silicon host for the aarch64 merge-queue runner

Status: not started. No Mac mini is in the owner's SSH config or on the
owner's network, and the fork has no registered self-hosted runner. Fill in
"Access" before starting. An earlier parked attempt is described under "What
already exists".

Quest: [`quest/m0/mac-mini-runner.md`](/quest/m0/mac-mini-runner.md) (M,
unclaimed upstream).

## Why this host

The quest's goal is that every merge group builds and runs rind's tests
natively on aarch64, on the maintainer's Mac mini as a second self-hosted
runner beside the x86_64 one, covering macOS on Apple silicon and aarch64
Linux in a VM on the same machine. Nothing else gives both:

- Hosted `macos-latest` is aarch64 but is not in the queue and cannot be put
  under `quest gate`.
- The owner's Raspberry Pi 5 and Jetson Orin Nano run aarch64 Linux natively
  (about 39 minutes cold, 0 failures; see fork PR #159's comment
  https://github.com/steelhead99x/rind/pull/159#issuecomment-6997682697) but
  have no Nix, are working machines, and have no macOS.
- Apple silicon has no AArch32, so armv7 stays out; `check:cross` covers its
  compilation.

Only an agent with SSH to an Apple-silicon Mac (an account that can install
Nix and register a runner) can finish the quest. Physical setup and network
access are the owner's.

## What already exists

- Fork base branch `base/m0-mac-mini-runner` at fork `a09f6e4c`, with
  `admin/handoff-mac-mini-runner.md` and a draft `queue-build.yml` change:
  `Build (macOS)` on `[self-hosted, rind-queue-arm64, macOS]` and
  `Build (aarch64 Linux)` on `[self-hosted, rind-queue-arm64, Linux]`, each
  running `nix develop --command quest gate just ci "$BASE"`, plus a
  `.github/actionlint.yaml` for the one custom label. Fork PR #159 holds the
  parked draft. It is based on an older upstream `main`; rebase by cherry-pick
  onto a fresh branch from `upstream/main`, not by rebasing the old one.
- Its decisions (owner, 2026-11-19): the only custom label is
  `rind-queue-arm64`; GitHub adds `macOS`, `Linux`, `ARM64`; `rind-queue` stays
  the x86_64 host's alone; runner groups are the maintainer's to settle; the
  aarch64 Linux side stays a VM on the Mac mini, not a hosted
  `ubuntu-24.04-arm` job.
- `quest/m0/queue-warm-target.md` (claimed upstream) also edits
  `queue-build.yml`; expect a conflict in the build job and take its steps into
  these jobs.

## Access (fill in)

| Item | Value |
| --- | --- |
| Host name or address (kept out of the repo, supplied with the job) | |
| SSH user and key path (same) | |
| macOS version, chip, cores, RAM, free disk | |
| Can the account install Nix (multi-user, sudo)? | |
| Can it register a GitHub runner for the fork? Token supplied by the owner | |
| Lima or nix-darwin Linux builder available? Which is chosen | |
| Is the machine shared with agents (needs `quest gate`)? | |

Confirm the host first and put the output in the first PR comment:

    uname -m; sw_vers; sysctl -n machdep.cpu.brand_string   # expect arm64, Apple M-series
    nix --version; git --version

## Commands

Work only inside your own directory on the host. Register runners against the
fork (`steelhead99x/rind`) for every trial; the upstream runner registration
is the maintainer's.

1. Natively, before any runner exists (what the queue job will run):

       git clone https://github.com/steelhead99x/rind && cd rind
       git fetch https://github.com/kixel-ai/rind main:refs/remotes/upstream/main
       nix develop --command just ci upstream/main      # the diff against main
       nix develop --command just gate                  # every crate, unscoped
       sh/dispatch.sh ci --all --query                  # what CI would select

   Record wall time cold and warm. `just ci` fails if a tool is missing.
2. The zeroing test, which the same host closes in
   [`handoff-mldsa-zeroing-macos.md`](/admin/handoff-mldsa-zeroing-macos.md):

       cargo test --release -p rind --test zeroing ml_dsa
3. aarch64 Linux VM, one of: Lima (`limactl start template://default`,
   then the same `nix develop --command just ci` inside) or the nix-darwin
   Linux builder. Time both; keep the one with the smaller added queue time and
   record why. Check inside the VM: `uname -m` prints `aarch64`, and
   `just armv7` is not applicable.
4. Runner: register with `--labels rind-queue-arm64` (GitHub adds `macOS` or
   `Linux`, and `ARM64`), `--work` under a directory run through `quest gate`.
   Validate the workflow with `actionlint`, `sh/pins.sh` and
   `sh/alert.sh check`, then run it once by `workflow_dispatch` on the fork
   before proposing it as a merge-group job.
5. Land order, so a group never waits on a runner that does not exist: register
   runners, land the workflow, let each job pass a group, then add its context
   (`Queue build / Build (macOS)`, `Queue build / Build (aarch64 Linux)`) to
   main's ruleset (dotfiles' `repo-settings` owns it; that is the maintainer's
   action).

Cheap checks for the doc-only parts: `quest check`, `admin/scan-license`.

## What closes the quest

Per the quest: every merge group builds and runs the tests natively on
aarch64 on both new runners and fails the group if they fail; the machine
setup is reproducible (nix-darwin or the flake's shells) and recorded; the VM
choice and the added queue time are recorded; and if the build adds more than
a few minutes to landing, the PR says so and proposes trimming. The quest file
and its links are deleted in the finishing PR. An agent can prepare the
workflow, the setup notes and the timings; the runner registration and the
ruleset change need the maintainer.

## Rules for every job

- Fork only. Always `gh --repo steelhead99x/rind`, never bare `gh`. Post
  nothing to kixel-ai or any other org, and publish nothing. Do not run
  `quest start` (it claims upstream); read-only `quest context` and
  `quest check` are fine.
- Read `AGENTS.md` and run `quest context` first. No em dashes. End GitHub
  posts and PR bodies with `(Written by <model>)`. PR bodies need
  `## Validation`, `## Models` (Size S first, Implementer last) and
  `## Waiting`.
- Fork PRs are draft, against a fork base branch at upstream `main`
  (fetch `kixel-ai/rind` main as `upstream/main`; the fork's `origin/main`
  has diverged and is not a base). No force-push, no rebase, never merge.
- Work in your own git worktree and CARGO_TARGET_DIR under `~/.cache`, never
  the shared clone and never `/tmp`. Commits are authored as the fork owner
  (`steelhead99x <224322244+steelhead99x@users.noreply.github.com>`) with a
  `Co-Authored-By: <model> <noreply@anthropic.com>` trailer. That is for fork
  PR commits only: anything bound for an upstream PR is restacked by the
  owner with no AI trailer, so do not open upstream PRs yourself.
- Report losses and failures as plainly as wins. Do not hide a failure with a
  retry or a looser check.

## Tracking

| Step | State | PR or link | Notes |
| --- | --- | --- | --- |
| Host reachable, access table filled | not started | | |
| `just ci` and `just gate` timed natively on macOS | not started | | |
| aarch64 Linux VM chosen and timed | not started | | |
| Workflow rebased onto upstream main, actionlint clean | not started | | |
| Runner registered on the fork, dispatch run green | not started | | |
| Maintainer: runner group and ruleset contexts | not started | | |

## Also unblocked by this host

- [`quest/m0/catch-on-pr/mldsa-zeroing-macos.md`](/quest/m0/catch-on-pr/mldsa-zeroing-macos.md):
  the macOS/aarch64 zeroing failure (its handoff is
  `admin/handoff-mldsa-zeroing-macos.md`).
- [`quest/m2/bench/mac-mini.md`](/quest/m2/bench/mac-mini.md) (S): the Mac mini
  as a `BENCHMARKS.md` host via `admin/bench-report collect`; requires this
  quest.
- [`quest/m2/confidence/apple-nightlies.md`](/quest/m2/confidence/apple-nightlies.md)
  (S): move the macOS and iOS nightlies to the machine; requires this quest.
- Any change in `build.yml`'s macOS and iOS rows that needs Apple silicon
  beyond hosted `macos-latest`, including a local reproduction of the
  `dart-ios` simulator job (see `admin/handoff-dart-ios-stable.md`).

## Report back

Host, macOS and chip, Nix version, native `just ci` and `just gate` times cold
and warm with pass counts, the VM option chosen with its added time, the
runner labels and workflow results, anything that could not run, and each
decision the owner or maintainer must make.
