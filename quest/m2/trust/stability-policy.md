# [S] rind says what a version number promises

## Goal

One section of the repository's docs, linked from the README, states rind's stability policy as the maintainer has confirmed it: what a minor and a patch release may change before 1.0, how the minimum supported Rust version moves, how an adapter's version follows its upstream, and what would have to be true for a 1.0.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): ✅ write it. An adopter pinning a crypto library wants to know how often it will break them, and today the answer is spread over `CONTRIBUTING.md`, quest files, and habit.

Draft it from what the repository already does, and change no practice:

- Breaking changes go in a minor release while rind is 0.x, are batched so adapters re-pin once ([rind 0.4 ships once](/quest/m2/api/release-0.4.md)), and each has its row in MIGRATING.md.
- The minimum Rust version is the workspace's `rust-version` (1.90 that day), and CI checks it (`sh/dispatch.sh`'s `msrv` module, `.github/workflows/lints.yml`). One crate sets its own: rind-openmls declares 1.91 (`rind-openmls/Cargo.toml:10`), and the `msrv` module leaves out every package whose `rust-version` differs from rind's (`sh/dispatch.sh:234`), so CI checks the workspace's version and nothing checks that one. The policy says an adapter may need a newer Rust than rind where its upstream does, where a reader finds each crate's, and that such a crate's declared version is not built in CI today. What is not written anywhere is when it may rise and whether a rise is a breaking change.
- An adapter's version begins with its upstream's breaking version, and its API is its upstream's (`CONTRIBUTING.md`'s Releases section, `sh/adapter-versions.sh`). Link there; don't restate it.
- Which CPUs and targets are supported is PLATFORMS.md's. Link there too.

What only the maintainer can say goes under `Waiting` when the draft is ready, each with the options and what the audit recommends:

- The MSRV rule. Recommended: it may rise in a minor release and never in a patch. Whether it also trails stable Rust by some margin is theirs to pick: look up how rustls, ring, and RustCrypto word theirs and offer those as the options.
- What 1.0 means. Recommended: say plainly that there is no date, and name the conditions the maintainer cares about, without inventing any.
- Whether a security fix is ever backported to the previous minor.

Put it where an adopter looks: a short section in the README that links to the full text in `CONTRIBUTING.md` or a file of its own, whichever the maintainer prefers in review.
