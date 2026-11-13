# Someone evaluating rind finds what they look for

## Goal

A team deciding whether to depend on rind finds, in the repository and on its release pages, what a crypto dependency is judged by: how to report a vulnerability, what a version number promises, what each release changed, how it compares with the alternatives, and what a security reviewer would need to start.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): of the pieces the audit offered, the maintainer picked ✅ a security policy, ✅ a stability policy, ✅ release notes with docs.rs and a comparison, and ✅ an audit-readiness package. Distribution packaging was offered and not picked.

The audit looked at rind the way an adopter's security review would. The engineering is there and written down (TESTING.md, PLATFORMS.md, ALGORITHMS.md, `benchmarks/verified.toml`, the proofs), and what is missing is the front door:

- No SECURITY.md, though GitHub's private vulnerability reporting is already on for the repository.
- Nothing says what a release may break, what the minimum Rust version is as a promise, or what 1.0 would mean, though the practice exists: `rust-version = "1.90"` checked in CI, breaking changes batched into one 0.4, adapters versioned by their upstream.
- `git_release_enable = false` in `.release-plz.toml`, so GitHub's Releases page shows none of the crates' changelogs, and no crate sets `[package.metadata.docs.rs]`.
- No one page that says what rind's checks cover and what they don't, for a reviewer.

Left alone on purpose: the README's first line is the maintainer's voice, and nothing here rewrites it. None of this commissions an audit or promises a response time; each quest writes down what is true and hands anything that is a promise back to the maintainer.
