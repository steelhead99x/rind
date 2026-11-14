# [S] rind's dev shell builds through the shared compile cache

## Goal

Cargo inside rind's Nix dev shell compiles through mbx, the compile cache the maintainer's hosts share across checkouts, so a new worktree reuses compiled work instead of building its own `target/` from scratch. Hosts without mbx behave as today.

## Plan

Found on 2026-11-12 while measuring agent build times on fedora, nixos, and desktop:

- The hosts put mbx's cargo shim in `~/.local/share/mbx/bin`, but `nix develop` puts the flake's cargo ahead of it on `PATH`, so rind's builds bypass it (`mbx doctor`: "shim not active"). Outside the dev shell the shim fails with "could not find the real Cargo", seen 18 times in desktop's transcripts.
- fedora holds 40 `target/` folders across 57 worktrees, 179 GB in total (median 4.2 GB); a cold `just check` costs 15 s to 2.5 min more than a warm one.
- [queue-warm-target](/quest/m0/queue-warm-target.md) lands the `shellHook` that puts the shim first in every shell the merge queue builds in, on any host with a shim. What remains here: the shells the queue does not enter, and hosts without mbx untouched. Fix the shim's "could not find the real Cargo" case if it is mbx's to fix, upstream.
- Measure a cold `just check` in a fresh worktree before and after, and check `mbx stats` shows hits.

## Required

- [The merge queue builds through mbx](/quest/m0/queue-warm-target.md) - the dev shells' `shellHook` that puts mbx's shim ahead of the toolchain
