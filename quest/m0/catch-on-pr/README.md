# Failures show up on the PR that causes them

## Goal

A change that breaks a check fails on its own pull request, not first in the merge queue or on main's nightly, and main's nightly runs green, so a red result names the PR that caused it.

## Plan

Planned with the maintainer on 2026-11-15 from the `/quest-run` of 2026-11-14 and 2026-11-15, in which kixel-ai/rind#748 and kixel-ai/rind#758 passed every PR check and then failed only in the queue, and main's mutants check broke twice on stale line pins.

- ✅ These quests sit in m0: a check that fails only after review blocks every PR behind it in the queue, and a failing main is m0 work (rejected: m1, m2).
- ✅ The `admin/prove` cache fix joins this epic in m0 although it is a local tool: it cost several proof agents a failed run in one night and is tiny (rejected: m2; dropping it and relying on agents knowing to delete `target/prove`).
- ✅ The armv7 `heap_scratch::detects_a_leak` failure seen once is not planned: one failure, not reproduced (rejected: a flake quest).
- ✅ The portable BINSEC ML-KEM timeout, seen twice, gets a quest that finds its cause (maintainer, 2026-11-17; rejected: not planning it; raising the timeout).
