# Handoff: Flutter stable on the iOS simulator

Status: waiting on Flutter, not on hardware. Fill in "Access" only if a Mac is
used for a local reproduction.

Quest: [`quest/m3/dart-ios-stable.md`](/quest/m3/dart-ios-stable.md) (XS,
unclaimed upstream).

## Why this host

`build.yml`'s `dart-ios` job runs `channel: beta` because stable 3.50.0's
`flutter test` sometimes hangs on the iOS simulator when `log stream` attaches
after the app logs its VM service URL
([flutter/flutter#181771](https://github.com/flutter/flutter/issues/181771));
beta's 3.51.0-0.1.pre has the fix
([flutter/flutter#193142](https://github.com/flutter/flutter/pull/193142)).
The quest returns the job to `stable` once stable carries the fix.

The job runs on a hosted `macos-latest` runner, so closing the quest needs
**no hardware of ours**: the blocker is a Flutter stable release. A macOS host
is useful only to reproduce the hang locally before trusting a stable release
(the hang hit about one `dart-ios` run in four, so a single green run proves
little), and for that an Apple-silicon Mac with Xcode and a simulator is
needed. An agent on a Linux box can still do the check below and prepare the
change; the many-run verification can use the fork's hosted macOS runs
(`workflow_dispatch` or repeated pushes on the fork, which costs minutes on a
public repo only).

## Access (fill in only for a local run)

| Item | Value |
| --- | --- |
| Host (kept out of the repo) and SSH user | |
| macOS, Xcode and simulator runtimes (`xcrun simctl list runtimes`) | |
| Flutter stable installed (`flutter --version`, channel stable) | |

## Commands

1. The gate, from any host (non-zero means stable has the fix):

       curl -s https://raw.githubusercontent.com/flutter/flutter/stable/packages/flutter_tools/lib/src/ios/simulators.dart | grep -c _ready || true

   Also `flutter --version` on the stable channel for the release number.
   Until it is non-zero, change nothing and report "still waiting".
2. When it is non-zero, in the PR:
   - `.github/workflows/build.yml`, `dart-ios`: set `channel: stable` (as the
     other Flutter jobs use) and delete the comment above it.
   - `UPSTREAM.md`: delete the "Flutter's iOS simulator test run hangs when
     its log stream attaches late" entry.
   - `quest/m3/dart-ios-stable.md`: delete it.
3. Verify the hang is gone with enough runs to see a one-in-four failure: on
   the fork, run the `dart-ios` job at least 20 times (or locally, loop
   `flutter test integration_test -d <udid> -v` in `rind-dart/integration`
   with `xcrun simctl spawn <udid> log stream` running beside it, as
   UPSTREAM.md's Reproduce lines say). A run that ends at `Waiting for VM
   Service port to be available...` is the hang; one is enough to keep the
   quest open and to report back.
4. Cheap checks: `actionlint`, `sh/pins.sh`, `quest check`,
   `admin/scan-license`, and markdown sanity on `UPSTREAM.md`.

## What closes the quest

A stable Flutter that has `_ready` (check above), the job back on `stable`
with no beta comment, the `UPSTREAM.md` entry gone, 20 or more clean
`dart-ios` runs recorded in the PR, and the quest file deleted.

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
| Gate check (`grep -c _ready` on stable) | waiting | | date and count |
| Stable release number that carries it | waiting | | |
| Workflow, UPSTREAM.md and quest edits | not started | | |
| 20 clean `dart-ios` runs on the fork | not started | | |

## Also unblocked by this host

- [`quest/m2/confidence/apple-nightlies.md`](/quest/m2/confidence/apple-nightlies.md)
  and [`quest/m0/mac-mini-runner.md`](/quest/m0/mac-mini-runner.md): an
  Apple-silicon Mac with Xcode also runs the `ios` and `dart-ios` rows
  natively (`sh/ios-simulator.sh` is the cargo runner for
  `aarch64-apple-ios-sim`). See `admin/handoff-mac-mini-runner.md`.
- Other entries in `UPSTREAM.md` whose "Goes when" is a Flutter release (check
  each; the Android emulator JIT entry is one).

## Report back

The gate count with the date, the Flutter stable release number, the PR, the
run count and results, and anything left in `UPSTREAM.md`.
