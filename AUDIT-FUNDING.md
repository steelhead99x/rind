# Audit funding packet (stub)

Notes for the maintainer's own applications: what each program asks for and
the facts about rind to cite, with links. The summary, impact statement,
budget, and timeline are the maintainer's to write; none is drafted here.
Program details are from each program's pages on 2026-11-25 and change; check
the linked page before applying. [AUDIT-SCOPE.md](AUDIT-SCOPE.md) is the
technical scope to attach.

## Facts to cite

- No outside party has audited rind ([README.md](README.md#before-you-depend-on-it)).
- The scope, with file and line counts and what is machine-checked versus
  human-reviewed: [AUDIT-SCOPE.md](AUDIT-SCOPE.md); the threat model, provenance,
  and checks: [AUDIT.md](AUDIT.md).
- Pure Rust, no C toolchain, memory-safe outside `low`, the FIPS build's DRBG handle, and the bindings:
  [AUDIT.md's `unsafe` table](AUDIT.md#unsafe), [BENCHMARKS.md's build cost](BENCHMARKS.md#build-cost).
- Formal proofs, and the trust base they rest on:
  [BENCHMARKS.md's verified code](BENCHMARKS.md#verified-code),
  [proofs/README.md](proofs/README.md#trust-base).
- Drop-in providers for rustls, ring, and aws-lc-rs:
  [README.md](README.md), [MIGRATING.md](MIGRATING.md), [rind-rustls](rind-rustls/README.md).
- Published on [crates.io](https://crates.io/crates/rind) under permissive licenses
  ([LICENSE](LICENSE)).
- Where it is used, and downstream consumers (maintainer to fill in; MoQ is
  [moq-dev/moq](https://github.com/moq-dev/moq)).
- Prior audits of the alternatives, for context: [README.md's comparison](README.md#compared-with-the-alternatives).

## OSTIF

[Open Source Technology Improvement Fund](https://ostif.org). A nonprofit that
scopes and manages audits of open source projects, paid for by funders such as
the Sovereign Tech Agency, Alpha-Omega, and the Linux Foundation, rather than a
grant to the maintainer.

- Asks for: maintainer buy-in and participation, and a scope tailored to the
  project (per its [impact report](https://ostif.org/wp-content/uploads/2025/01/2024-Sovereign-Tech-Agency_OSTIF-Impact-Report.pdf)). Confirm the intake step on
  [ostif.org](https://ostif.org) or by email; its apply page was not reachable
  when this was written.
- Offers: firm selection and management of the engagement. Its published
  reports include
  [Mbed TLS's](https://ostif.org/wp-content/uploads/2026/10/26-05-2730-REP-MbedTLS-Security-Audit-OSTIF-V1.0.pdf),
  a TLS-library precedent.
- Cite: [AUDIT-SCOPE.md](AUDIT-SCOPE.md), Phase 1 inventory, the list of what is
  out of scope.
- Maintainer to decide: whether to approach OSTIF for a managed audit, and
  whether to commit to a public report (see the PR's `## Waiting`).

## Sovereign Tech Fund

[Sovereign Tech Agency's fund](https://www.sovereign.tech/programs/fund).
Investment in open digital base technologies; cryptography libraries and
encryption technologies are in its examples.

- Asks for (per the program page): applications only through its online
  platform, in English or German; proposed work costing over EUR 50,000; code and
  documentation under an OSI or FSF free license; no prototype
  development; open-source technologies the applicant can name that depend on
  the component; no grant or investment from another public entity for the
  same activities, now or before; a decision in about 10 weeks and a contract
  about 6 months from submission.
- Cite: the license, the published crates, adopters (maintainer to fill in),
  [AUDIT-SCOPE.md](AUDIT-SCOPE.md) as the work plan for an audit line item.
- Open: whether a security audit alone, or an audit plus follow-up fixes and the
  proof work in [proofs/README.md](proofs/README.md), is the proposal.
- The agency also funds audits through OSTIF
  ([impact report](https://ostif.org/wp-content/uploads/2025/01/2024-Sovereign-Tech-Agency_OSTIF-Impact-Report.pdf)),
  so one route may reach the other.
- Not this program: the [Fellowship](https://www.sovereign.tech/programs/fellowship)
  pays individual maintainers, not an audit.

## ISRG Prossimo

[Prossimo](https://www.memorysafety.org), the Internet Security Research
Group's memory-safety project. It supports Rust replacements of critical
infrastructure, funded by donors, rustls among them.

- Asks for: no formal application process is published; it links maintainers
  with funders and points to donate@abetterinternet.org for upcoming
  initiatives.
- Cite: rind as a pure-Rust backend for rustls ([rind-rustls](rind-rustls/README.md)),
  which Prossimo already supports.
- Open: whether to write to them at all, or to start through
  rustls's maintainers; and what initiative, if any, rind would be.
