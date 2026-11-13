# [XS] Dependabot proposes Cargo dependency updates

## Goal

`.github/dependabot.yml` also covers the `cargo` ecosystem: one grouped weekly PR of the workspace's routine crate updates, with the same 7-day cooldown the GitHub Actions updates use. Dependabot is not known to hold the transitive crates a bump pulls in to that cooldown (dependabot-core #16428 reports a Cargo lockfile update that skipped it), so reviewing each PR includes checking its `Cargo.lock` diff for versions published in the last 7 days.

## Plan

Planned with the maintainer on 2026-11-13: ✅ Dependabot bumps crates (rejected: the [upstream run](/quest/m2/upstream-updates.md) bumps them by hand), ✅ in m2 (rejected: m0, which its README keeps for urgent work), ✅ ignore semver-major updates (rejected: propose majors too).

- An update that changes the version an adapter tracks is an adapter release, not a routine update, which is why majors are ignored. Below 1.0 that version is major.minor (`sh/adapter-versions.sh`), so also ignore minor updates of each crate an adapter tracks below 1.0. That's the dependency named after the adapter, such as rustls, or the crates `package.metadata.rind.upstream` stands for, such as rind-openmls's `openmls_traits` and its sibling crates at 0.6 (not `openmls` itself, a 0.9 dev-dependency). Drop a crate's minor ignore once the adapter's tracked requirement reaches 1.0, not when the upstream first releases 1.0, since a later 0.x minor would still change the adapter's tracked major.minor; the upstream run checks the list each run. The upstream run reviews what Dependabot skips.
- Cargo treats any `0.x` minor bump, and any `0.0.x` patch bump, as breaking, while Dependabot calls them minors and patches, so for crates that are not adapter upstreams, such as libcrux's, the grouped PR's CI is what catches the break.
