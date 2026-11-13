# [M] A page per library says how to move from it to rind

## Goal

For each library rind stands in for, the site has a page at its own address, such as `/from/ring`, that gives the exact change: the `Cargo.toml` lines, the names that differ, and what rind cannot back. A picker on the landing page takes a visitor to theirs. Each is a page a search for "replace ring" or an agent choosing a dependency can land on directly.

## Plan

Decided 2026-11-12 (maintainer, /quest-plan): ✅ one of the three showpieces, and ✅ real pages, not a widget, because nothing on the site may exist only inside one.

- The pages, on 2026-11-12: ring, by its adapter or by the `[patch.crates-io]` route through rind-patch; aws-lc-rs, by its adapter; rustls; and the crates with an adapter of their own (rcgen, jsonwebtoken, dimpl, str0m, object_store, openmls). MIGRATING.md's "Crates with their own crypto backend" survey gets one page listing each crate and what it needs.
- MIGRATING.md and each adapter's README are the source. Render their sections; do not write the steps a second time. Where a page needs text they lack, add it to them. If their headings are too loose to build from, give them the anchors or structure the build needs in this PR.
- A page's steps and its dependency line describe the same code, so a reader who copies both gets a build. `main` runs ahead of crates.io between releases, in its text and in its versions. On 2026-11-12 MIGRATING.md uses `CbcIv`, which rind 0.3.2 does not export (`git grep CbcIv rind-v0.3.2 -- rind/src` prints nothing). Every published adapter's manifest was one patch ahead of crates.io that day (rind-rustls said 0.23.4 where crates.io had 0.23.3), and rind-openmls's manifest says 0.6.0 while the crate is unpublished until rind 0.4 ([the release quest](/quest/m2/api/release-0.4.md), which sets `release = false` for it in `.release-plz.toml` until then).
- So no version is typed into a template, and none is read from `main`'s manifest alone. Recommended: build each page from the guide and README at the crate's newest release tag (`rind-v*`, `rind-ring-v*`, and so on), with the version that tag published, and add a note with the git dependency where `main` has moved on. If the tagged files lack the structure the build needs, render `main`'s with the git dependency and a line saying the page describes unreleased code, until a release carries the structure. Either way a crates.io line names only a version the registry lists (its sparse index, `https://index.crates.io`, answers that at build time), and a crate with no release gets the git dependency and is called unreleased.
- A release changes what these pages should say without changing a file under `site/`. [The deploy](/quest/m2/site/deploy.md) covers that; if this quest lands first, add the rule to its Plan.
- Each page states what its adapter cannot back, from the list its README keeps, before the reader finds out by compiling.
- The agent prompt for `MIGRATE.md` is on every page, since it covers each route these pages describe (`MIGRATE.md:39-45`): rustls and the crates above it, the crates an adapter serves, ring's and aws-lc-rs's APIs, and a crate that hard-wires ring 0.17.
- The patch route is ring's alone: [rind-patch](https://github.com/kixel-ai/rind-patch)'s workspace holds one crate, named `ring`, so the aws-lc-rs page offers the dependency rename and no `[patch]` line. An aws-lc-rs shim would be new work with its own test, and is not planned here.
- `sh/patch.sh` and `patch/fixture` already test ring's patch route. If a page shows a snippet no test builds, say which in the PR.
- [The API's shape](/quest/m2/api/shape.md) may rename and move types before rind 0.4. These pages are rendered from MIGRATING.md, so they follow it without a second edit.

## Required

- [The landing page builds from the repository](/quest/m2/site/landing.md) - the `site/` project and the picker's place on it
