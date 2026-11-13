# [S] Releases, docs.rs, and a comparison an adopter can read

## Goal

Each crate release has a GitHub Release carrying its changelog, docs.rs renders `rind` with every public item documented for the targets that matter, and the README has one table comparing rind with ring, aws-lc-rs, and RustCrypto, generated from the files that already hold the facts.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): ✅ all three, as one quest since each is small.

GitHub Releases:

- `.release-plz.toml:3` sets `git_release_enable = false`, so the only GitHub Release that day was rind-dart's. Find why before changing it: `git log -S git_release_enable -- .release-plz.toml` and the PR that set it. If the reason still holds, write it beside the setting and stop this part there with what you found.
- If it does not, enable releases for the published crates, with release-plz's changelog as the body. Tags and releases are created by the release job, which already runs only when a release PR merges.

docs.rs:

- No crate sets `[package.metadata.docs.rs]`, so docs.rs builds `rind` with its own defaults. Set the targets rind has backends for (x86_64 and aarch64 Linux, and one that takes the portable backend) and the features a reader needs to see.
- Check the build the way docs.rs runs it, with `cargo +nightly rustdoc` and `--cfg docsrs`, and fix what it warns about.
- The adapters get the same where they have features.

The comparison:

- One table in the README: pure Rust or not, build tools needed, targets, which algorithms, what is formally verified, and speed in one line with a link, for rind, ring, aws-lc-rs, and RustCrypto.
- Every cell comes from a file that already states it and is checked: ALGORITHMS.md, PLATFORMS.md, BENCHMARKS.md's build-cost section, and `benchmarks/verified.toml`. Generate it or test it the way the README's heatmap is kept current, so it cannot drift. A cell with no source is left out, not written from memory.
- It states the other libraries' strengths as plainly as rind's, each with a link to that project's own page: the FIPS 140-3 validation behind aws-lc-rs's `fips` feature, which rind lacks, and the audits ring and RustCrypto's crates have had.
- The validation belongs to particular AWS-LC-FIPS module versions, which that feature builds against, not to every aws-lc-rs build. Name the feature and take the module and its status from aws-lc-rs's own page.
- The README's first line stays as the maintainer wrote it.
