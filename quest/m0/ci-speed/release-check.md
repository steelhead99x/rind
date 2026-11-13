# [M] Releases publish only after the full suite passes locally

## Goal

Before a release-plz PR merges, one `just` recipe runs the heavy suites the weekly CI runs, scoped to the crates the release PR versions plus everything depending on them, on a local Linux host at the release PR's head, and the release PR records the result. Nothing publishes that the full suite has not passed.

## Plan

Decided with the maintainer on 2026-11-12:

- ✅ Run it locally, before the release PR merges (rejected: a CI check on the release PR, which would re-run every time release-plz updates the PR; both, through one recipe).
- ✅ Scope: the crates whose version the release PR changes, plus their dependents (rejected: always every crate). A release of `rind` runs everything, since every crate depends on it. Select by the changed `version` fields, not by the diff: a release PR also changes `Cargo.lock`, which `sh/select.sh` maps to the whole workspace.
- The recipe runs, for the selected crates, every suite a Linux host can run from `build.yml`, `miri.yml`, `x86-cpu.yml`, `ctgrind.yml`, and `fuzz.yml`'s replay: `just ci` scoped to them, `SLOW_TESTS=1`, the SDE CPU tiers, `just armv7`, every `just qemu <shell>` target (s390x, i686, and the rest the flake defines), musl, the Android cross builds, `just portable`, `just wasm`, `just miri` on each of its targets, `just openmls` when rind-openmls is selected, ctgrind, and fuzz corpus replay. Derive the list from the workflows rather than copying it, so a new Linux job joins the release check too. macOS, Windows, and Apple-silicon rows are not Linux-runnable: the release PR links the last green nightly `build` run, which holds those rows.
- Run it through `quest gate` like any heavy local command.
- Say in CONTRIBUTING.md's Releases section that a release PR merges only after this recipe passes at its head, and where its result goes. `/quest-merge` picking a release PR should run it, so the step needs no person.
- Recommendation: the release PR records the head SHA the recipe passed on, so a later release-plz update visibly needs a re-run.

## Related

- [The heavy suites run weekly and finish](/quest/m0/ci-speed/weekly.md) - the same suites, on every crate, on hosted runners
- [rind 0.4 ships once](/quest/m2/api/release-0.4.md) - the next release this gates
