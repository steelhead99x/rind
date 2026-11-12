# [S] Each adapter's API is diffed against its upstream's

## Goal

`just ci` fails when a published `rind-<consumer>` adapter's public API differs from the provider its upstream ships, for each Cargo feature set upstream offers, apart from the omissions the adapter's README lists. An item added, removed, renamed, or given another signature fails the check, and so does a README omission the diff no longer finds.

## Plan

Planned from the 2026-11-09 tooling audit. The exact-API rule has no machine check:

- A one-off comparison of rustdoc surfaces on 2026-11-08 found additions, changed signatures, and renamed items in every adapter. [moq-dev/rind#522](https://github.com/moq-dev/rind/pull/522), [moq-dev/rind#521](https://github.com/moq-dev/rind/pull/521), [moq-dev/rind#516](https://github.com/moq-dev/rind/pull/516), [moq-dev/rind#515](https://github.com/moq-dev/rind/pull/515), and [moq-dev/rind#519](https://github.com/moq-dev/rind/pull/519) fixed them and add no check, so the next drift is found by the next hand audit.
- `sh/adapter-versions.sh` checks only that an adapter's version begins with its upstream's breaking part.
- cargo-semver-checks, through release-plz, compares an adapter with its own last release, not with upstream.
- No job builds an adapter's features one at a time: rind-aws-lc-rs declares 13 and rind-ring 3, and only the default set, `--no-default-features`, and `wipe` are built.

Guidance:

- Diff rustdoc JSON, as the audit did, against the upstream version `Cargo.lock` resolves. The upstream side is the provider module where the adapter mirrors one (`rustls::crypto::aws_lc_rs` for rind-rustls) and the whole crate where it replaces one (ring, aws-lc-rs).
- The omissions must be read from one place. Recommended: a list beside each adapter that the check reads and the README's section is checked against, so the two cannot disagree.
- Compare per feature set upstream declares, so a feature that upstream gates an item behind gates it in the adapter too.
- rind-object-store has no upstream provider shape to copy; exclude it and say why where the check lists the adapters.
- rustdoc's JSON output is unstable. Pin the toolchain that writes it in the flake, so a new release cannot fail the gate.
- Scope it in `sh/dispatch.sh` to an adapter's sources, its manifest, and `Cargo.lock`, as the `versions` module is scoped (`sh/dispatch.sh:57`). An upstream release reaches rind only through a lockfile change, so no nightly run is needed.
- If the doc builds make it too slow for the gate, run it in `lints.yml` nightly and on pull requests that touch an adapter.
