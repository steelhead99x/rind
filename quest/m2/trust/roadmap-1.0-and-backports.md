# [S] Define 1.0 roadmap, gate semver with cargo-semver-checks, scope changelogs, and document security backports

## Goal

Evaluators see clear 1.0 exit criteria and a security hotfix/backport branch policy, CI automatically catches accidental semver breaks on published crates via `cargo-semver-checks`, and `rind/CHANGELOG.md` is cleanly scoped to `rind` changes rather than mixing unrelated workspace noise.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ define the 1.0 roadmap, add `cargo-semver-checks`, scope `rind/CHANGELOG.md`, and document security backport branches (rejected: skip).

- **1.0 exit criteria**:
  - Add a clear, factual "Path to 1.0" / stability roadmap section (in `README.md` or `STABILITY.md` / `AUDIT.md`, fitting the existing docs layout) listing what must be true before cutting `rind 1.0` (API stability across 0.4+, CI/CT/coverage/fuzzing gates, external audit milestone, MSRV & semver guarantees), handing any binding commitment wording to the maintainer in the PR.
- **`cargo-semver-checks` CI gate**:
  - Add `cargo-semver-checks` to CI (for PRs or release checks against the latest published crates.io version of `rind` and published Rust adapters) so accidental breaking changes in minor/patch releases fail before publish.
- **Changelog scoping**:
  - Audit and clean up `rind/CHANGELOG.md` (and adapter changelogs / release script) so `rind`'s changelog records user-visible changes to `rind` itself rather than unrelated internal or adapter-only churn.
- **Security hotfix & backport branch policy**:
  - Document how security fixes will be backported to supported release lines (e.g. `release/0.x` maintenance branches for active minor versions, patch release tags, and GHSA advisory mapping) in `SECURITY.md` / release docs, flagging the exact supported-branch window for maintainer confirmation in the PR.
