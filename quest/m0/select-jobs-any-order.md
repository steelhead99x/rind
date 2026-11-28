# [XS] Dispatched jobs may be listed in any order

## Goal

`gh workflow run <workflow> -f jobs='...'` accepts the jobs in any order, so `jobs='lean cosim'` runs the same jobs as `jobs='cosim lean'`.

## Plan

Planned with the maintainer on 2026-11-27 (`/quest-run`).

- `sh/select-jobs.sh` currently rejects a list that isn't in workflow order. Agents dispatching `prove` hit this on 2026-11-27, for example with `jobs='lean cosim'`. AGENTS.md's examples happen to be in order, so nothing warns them. Keep rejecting unknown job and row names.
