# [M] PR checks stop burning hosted runners

## Goal

The jobs a pull request triggers on GitHub-hosted runners are the fast, high-signal ones, and they rebuild only what changed, so a PR's checks start without queueing behind other work for the org's 60 concurrent hosted jobs.

## Plan

Measured 2026-11-12 over 14 days; see [the epic](/quest/m0/ci-speed/README.md) for the decisions it shares.

- `miri` runs on path-filtered PRs and never finished: 0 of 34 runs, each cut at the 6 h timeout, about 240 h. Take it off PRs; [the weekly quest](/quest/m0/ci-speed/weekly.md) makes its scheduled run finish.
- `x86-cpu` runs every SDE model on 304 PRs (median 61 min). On a PR, run only the models whose dispatch paths its diff can reach (`admin/x86-cpu`'s scans already group models by path set), and only the tests for the primitives it changed, from [ci-scope](/quest/m0/ci-speed/ci-scope.md)'s map; the weekly run keeps all of them.
- `build`, `ctgrind`, `x86-cpu`, and `prove` compile from scratch on every run (`build` median about 11 min of compile). Give them a build cache, as `check.yml`'s `Swatinem/rust-cache` step does, keyed so a PR restores main's (`fuzz.yml` caches only its corpus).
- Dispatched `bench` was 1,123 h from 195 runs off quest branches. A dispatch measures only the benchmark groups for the primitives the branch changed, unless asked for all.
- `check.yml` runs the unscoped `just ci --all` on all 621 pushes to main, 27% cancelled by the next push. It is the backstop for the queue's diff-scoped selection, so keep it, but run it once a day on main's head instead of per push.
- armv7 jobs that run under qemu on x86 move to `ubuntu-24.04-arm`, which runs armv7 natively (as `fuzz.yml`'s `replay-armv7` does). Changing `runs-on` is not enough: the flake sets `CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_RUNNER = "qemu-arm"` and `sh/armv7.sh` picks `QEMU_CPU` per run, so drop the runner where the host runs armv7. Only the `QEMU_CPU=max` (crypto extension) runs go native: the `cortex-a15` runs, with and without NEON, stay under qemu, because a fault on an instruction that CPU lacks is what they check, as SDE's tiers do. ctgrind's `armv7-qemu` stays too: Valgrind hides the crypto extension it traces.
- Pullfrog review jobs failed 40% of 364 runs; check whether their failures need a fix once [moq-dev/rind#684](https://github.com/moq-dev/rind/pull/684) lands.
- State each workflow's hosted-hour change in the PR.

## Required

- [just ci runs only what a change can break, concurrently](/quest/m0/ci-speed/ci-scope.md) - the path-to-primitive map that scopes a PR's SDE tests and bench dispatch
