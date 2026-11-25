# Someone evaluating rind finds what they look for

## Goal

A team deciding whether to depend on rind finds, in the repository and on its release pages, what a crypto dependency is judged by: how to report a vulnerability, what a version number promises, what each release changed, how it compares with the alternatives, and what a security reviewer would need to start.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): of the pieces the audit offered, the maintainer picked ✅ a security policy, ✅ a stability policy, ✅ release notes with docs.rs and a comparison, and ✅ an audit-readiness package. Distribution packaging was offered and not picked.

The audit looked at rind the way an adopter's security review would. The engineering was there and written down (TESTING.md, PLATFORMS.md, ALGORITHMS.md, `benchmarks/verified.toml`, the proofs); what was missing was the front door, which the picked pieces supply.

Left alone on purpose: the README's first line is the maintainer's voice, and nothing here rewrites it. None of this commissions an audit or promises a response time; each quest writes down what is true and hands anything that is a promise back to the maintainer.

Decided 2026-11-21 (maintainer, /quest-plan): added five follow-up trust quests covering a 1-page TCB & Axiom Ledger + VG theorem-binding check + drafted human sign-off policy, a 1.0 roadmap + `cargo-semver-checks` + changelog scoping + security backports, supply-chain hardening (`cargo-vet`, SLSA attestations, reproducible builds, OpenSSF Scorecard, `security.txt`/CVE note), crates.io/docs.rs/site/benchmark-methodology polish, and a phased third-party audit scope + grant packet. Keeping `"Cryptography slop"` on docs.rs/site untouched was confirmed again (rejected: rewriting it).

