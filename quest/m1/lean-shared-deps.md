# [S] Worktrees share one copy of the Lean dependencies

## Goal

A new worktree's `admin/prove` reuses the Mathlib and Aeneas builds another worktree on the same host already fetched or built, rather than unpacking its own 7.5-8.9 GB into `proofs/.lake/packages`, and rebuilds none of them.

## Plan

Decided with the maintainer on 2026-11-12, from read-only audits of the maintainer's agent hosts: ✅ Lake's artifact cache (rejected: building Aeneas and Mathlib in Nix, which is more work).

- The cost: each worktree holds 7.5-8.9 GB of dependencies sharing no disk blocks, about 170-180 GB per host across some 22 worktrees. Gated `admin/prove` runs also spent about 16.8 CPU-h rebuilding in 1.8 days, which goes too if dependencies stop rebuilding.
- Turn on `LAKE_ARTIFACT_CACHE=true` (Lean 4.22 and later; rind pins 4.35) with a `LAKE_CACHE_DIR` outside the worktree that every worktree of a user shares, in the `prove` dev shell, so `admin/prove` and a hand-run `lake build` both get it.
- Verify on the whole new-worktree flow: a fresh worktree runs `admin/prove lean` (`lake exe cache get`, then `lake build`) after another has, and reports its `proofs/.lake` size and whether any dependency rebuilt. Mathlib's `cache get` unpacks its own archives, which Lake's cache may not cover.
- Only if the cache does not cover the packages, fall back to a reflink copy of `.lake/packages` from a per-host copy keyed by `lake-manifest.json`. A reflink saves disk only on a filesystem that has them, such as Btrfs or XFS.
- Say how the shared cache is pruned once the manifest moves on, since it outlives the worktrees.
