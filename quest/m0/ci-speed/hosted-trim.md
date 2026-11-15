# [M] PR checks stop burning hosted runners

## Goal

The jobs a pull request triggers on GitHub-hosted runners are the fast, high-signal ones, and they rebuild only what changed, so a PR's checks start without queueing behind other work for the org's 60 concurrent hosted jobs.

## Plan

Measured 2026-11-12 over 14 days; see [the epic](/quest/m0/ci-speed/README.md) for the decisions it shares.

- `x86-cpu` runs every SDE model on 304 PRs (median 61 min). On a PR, run only the models whose dispatch paths its diff can reach (`admin/x86-cpu`'s scans already group models by path set), and none when `sh/backends.sh` says the diff reaches no x86_64 code (as `RIND_SCOPE` does for PRs' ctgrind job), except that a change to `.github/workflows/x86-cpu.yml` or `admin/x86-cpu` runs every model, so add `admin/x86-cpu` to the workflow's `pull_request` path filter; the weekly run keeps all of them. Tests are not narrowed by primitive: a hand-written path-to-test map missed consumers in every review round of [kixel-ai/rind#736](https://github.com/kixel-ai/rind/pull/736), so the maintainer chose backend reach alone.
- `build`, `ctgrind`, `x86-cpu`, and `prove` compile from scratch on every run (`build` median about 11 min of compile). Give them a build cache, as `check.yml`'s `Swatinem/rust-cache` step does, keyed so a PR restores main's.
- Dispatched `bench` was 1,123 h from 195 runs off quest branches. A dispatch takes the benchmark groups to measure as an input, defaulting to all; nothing maps changed paths to bench targets, for the same reason as the SDE tests.
- `check.yml` runs the unscoped `just ci --all` on all 621 pushes to main, 27% cancelled by the next push. It is the backstop for the queue's diff-scoped selection, so keep it, but run it once a day on main's head instead of per push.
- armv7 jobs that run under qemu on x86 move to `ubuntu-24.04-arm`, which runs armv7 natively (as `fuzz.yml`'s `replay-armv7` does). Changing `runs-on` is not enough: the flake sets `CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_RUNNER = "qemu-arm"` and `sh/armv7.sh` picks `QEMU_CPU` per run, so drop the runner where the host runs armv7. Only the `QEMU_CPU=max` (crypto extension) runs go native: the `cortex-a15` runs, with and without NEON, stay under qemu, because a fault on an instruction that CPU lacks is what they check, as SDE's tiers do. ctgrind's `armv7-qemu` stays too: Valgrind hides the crypto extension it traces.
- Pullfrog review jobs failed 40% of 364 runs; check whether their failures need a fix once [moq-dev/rind#684](https://github.com/moq-dev/rind/pull/684) lands.
- State each workflow's hosted-hour change in the PR.
