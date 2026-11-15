# [S] pyca/verified-garbage is timed on nixos and kixtop

## Goal

`nixos` and `kixtop`, the report hosts the first measurement could not reach idle, time VG beside rind, and every cell where VG is at least as fast as rind at every size has a switch quest and a ✓ quest, as [the epic](/quest/m2/verified-garbage/README.md) records for the others.

## Plan

- rind-bench, `admin/bench-report`, and the weekly bench's tiers already time VG ([kixel-ai/rind#741](https://github.com/kixel-ai/rind/pull/741)). Run `admin/bench-report collect --host nixos --host kixtop` and `admin/bench-report summary .tmp/bench-report/<commit>`, the directory `collect` wrote, or rind-bench filtered to `(^|/)(rind|verified-garbage)(/|$)` at every size the report refresh's bar sets.
- `nixos` (Zen 3, AVX2 without AVX-512) is the report's only AMD AVX2 host; on 2026-11-13 its CI runners kept 28 to 31 of its 32 CPUs busy for six hours. `kixtop` (Apple M4) is the only Apple aarch64 host, where VG takes FEAT_SHA3's Keccak and DIT applies; it was offline.
- `desktop` was timed only under load (about 10 of 24 CPUs busy): rerun it idle too, to settle the cells its numbers alone suggest (Curve25519 and P-256 with AVX2).
- Add a cell either host wins to the matching switch quest, or a new switch and ✓ quest pair, and record each cell VG loses in the epic's README.

## Waiting

- Maintainer: bring `kixtop` online (an agent cannot wake the laptop); done when `ssh kixtop true` succeeds.
