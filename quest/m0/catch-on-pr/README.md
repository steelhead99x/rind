# [L] Failures show up on the PR that causes them

## Goal

A change that breaks a check fails on its own pull request, not first in the merge queue or on main's nightly, and main's nightly runs green, so a red result names the PR that caused it.

## Plan

Planned with the maintainer on 2026-11-15 from the `/quest-run` of 2026-11-14 and 2026-11-15, in which kixel-ai/rind#748 and kixel-ai/rind#758 passed every PR check and then failed only in the queue, and main's mutants check broke twice on stale line pins.

- ✅ These quests sit in m0: a check that fails only after review blocks every PR behind it in the queue, and a failing main is m0 work (rejected: m1, m2).
- ✅ The `admin/prove` cache fix joins this epic in m0 although it is a local tool: it cost several proof agents a failed run in one night and is tiny (rejected: m2; dropping it and relying on agents knowing to delete `target/prove`).
- ✅ The armv7 `heap_scratch::detects_a_leak` failure seen once is not planned: one failure, not reproduced (rejected: a flake quest).
- ✅ The portable BINSEC ML-KEM timeout, seen twice, gets a quest that finds its cause (maintainer, 2026-11-17; rejected: not planning it; raising the timeout).
- ✅ The macOS ML-DSA zeroing failure, seen once on main's coverage nightly, gets a quest, since a missed wipe would break AGENTS.md's zeroing requirement (maintainer, 2026-11-18, on kixel-ai/rind#862).
- ✅ The rind-fips fork test hang, seen once on the same nightly, is not planned: it meets the single-failure bar above (maintainer, 2026-11-18; rejected: a quest).
- The macOS ML-DSA zeroing failure was already fixed by [kixel-ai/rind#803](https://github.com/kixel-ai/rind/pull/803), which merged hours after the failing nightly: restoring its old `expanded: Polys` field fails macOS's coverage-built `zeroing` test 600 times in 600, and the fixed tree passes 2400 in 2400 ([kixel-ai/rind#957](https://github.com/kixel-ai/rind/pull/957)). PRs run no macOS job, so a regression there surfaces a day late, on the nightly.

What remains: main's nightly is red on four workflows no quest owns, each seen on 2026-11-21's schedule, and macOS-only regressions reach no PR check. Find each cause, fix it or split it into a quest of its own, so a red nightly again names the PR that caused it:

- `python`'s `sdist` job: `cargo metadata` fails while pip builds the sdist ([run 44962192128](https://github.com/kixel-ai/rind/actions/runs/44962192128)).
- `dart-libraries`, every platform: the bindings import `rind::ecdsa`, `rind::ed25519`, and `rind::rsa::KeyPair`, which no longer resolve ([run 44962598859](https://github.com/kixel-ai/rind/actions/runs/44962598859)).
- `ctgrind`'s `build (ubuntu-24.04-arm, release)` and `aarch64-portable` jobs ([run 44919091128](https://github.com/kixel-ai/rind/actions/runs/44919091128)).
- `asan`'s `build (ubuntu-latest)`: LeakSanitizer reports leaks ([run 44958835698](https://github.com/kixel-ai/rind/actions/runs/44958835698)).
- macOS: no PR or queue job runs on it, so a macOS-only regression such as #767's passes its PR and fails a day later on the nightly. Recommended: run rind's debug tests on a macOS runner on each pull request that touches `rind/` or the root `Cargo.toml` or `Cargo.lock`, which `sh/dispatch.sh` already counts as rind's inputs, path-filtered like the other platforms' PR runs in CONTRIBUTING.md, so the break shows on its own PR as the Goal requires; also run it in the merge queue through `CHECK_QUEUE` in `sh/dispatch.sh`, as [the PR-checks quest](/quest/m0/ci-speed/unread-results.md) suggests for other checks, so two PRs cannot break it together, and state how much it slows the gate.
