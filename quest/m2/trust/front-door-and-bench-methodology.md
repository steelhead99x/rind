# [S] Polish crates.io, docs.rs, website front door, and benchmark methodology

## Goal

A developer or security reviewer landing on `rind`'s crates.io page, `docs.rs`, `README.md`, `AUDIT.md`, `BENCHMARKS.md`, or the project website gets accurate, up-to-date facts, clear library comparisons, transparent benchmark methodology (including dependency versions, `Dit::hold()` disclosure, and non-Nix reproduction commands), and complete site navigation and metadata.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ polish the crates.io, docs.rs, README/AUDIT, benchmark methodology, and website front door (rejected: changing the `"Cryptography slop"` phrasing on docs.rs/site, keeping the maintainer's voice untouched per [quest/m2/trust/README.md](/quest/m2/trust/README.md)).

- **crates.io and docs.rs metadata**:
  - Polish `rind/Cargo.toml` (`description`, `keywords`, `categories`, `documentation`, `homepage`) so crates.io search and metadata accurately reflect `rind` without overwriting the maintainer's voice where intentionally kept.
  - Add `[package.metadata.docs.rs]` (`all-features = true`, `rustdoc-args = ["--cfg", "docsrs"]`, targets where helpful) across published Rust adapter crates (`rind-rustls`, `rind-ring`, `rind-aws-lc-rs`, `rind-rcgen`, `rind-openmls`, etc.) so `docs.rs` builds cleanly with full feature documentation.
- **Refresh stale counts in `README.md` and `AUDIT.md`**:
  - Fix stale test/proof/algorithm/crate counts in `README.md` and `AUDIT.md` (e.g. `AUDIT.md:69-70, 313-318`) and where possible add a lightweight check or script note so numbers stay synchronized.
- **Comparison table & transparent benchmark methodology**:
  - Refine the comparison table (`rind` vs. `aws-lc-rs`, `ring`, `RustCrypto`, `OpenSSL`) with clear, fair trade-offs (pure-Rust build, binary size, verification status, maturity/audit status, algorithm coverage).
  - Document benchmark methodology clearly in `BENCHMARKS.md`: exact competitor crate/OpenSSL versions pinned in each run, explicit disclosure of `Dit::hold()` in `rind-bench/benches/criterion/mod.rs:46` and how it relates to single-call latency, and plain `cargo bench` reproduction commands for reviewers who do not use Nix.
- **Website polish (`site/`)**:
  - Add a favicon (`site/src/layouts/Base.astro`) and prominent navigation links to `AUDIT.md` and `SECURITY.md` (`site/src/layouts/Base.astro`, `site/src/lib/landing.ts`) so visitors can jump straight to safety evidence and vulnerability reporting.

## Related

- [Add missing Argon2id, SLH-DSA, unheld-DIT, and small-record TLS benchmark baselines](/quest/m2/bench/missing-baselines-and-dit-row.md)
