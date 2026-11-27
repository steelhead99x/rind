# [S] Frame the comparison table and crates.io pitch for a reviewer

## Goal

A developer or security reviewer comparing `rind` with `aws-lc-rs`, `ring`, RustCrypto, and OpenSSL sees, in the README's comparison table, on the website, and on crates.io, clear and fair trade-offs in the maintainer's own words.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ polish the crates.io, docs.rs, README/AUDIT, benchmark methodology, and website front door (rejected: changing the `"Cryptography slop"` phrasing on docs.rs/site, keeping the maintainer's voice untouched per [quest/m2/trust/README.md](/quest/m2/trust/README.md)).

[kixel-ai/rind#1038](https://github.com/kixel-ai/rind/pull/1038) did the factual part: docs.rs metadata on every adapter with features, crates.io keywords, a generated and checked `unsafe` table and current coverage facts in `AUDIT.md`, a Methodology section in `BENCHMARKS.md` (per-host crate versions from each measured commit's `Cargo.lock`, the `Dit::hold()` disclosure, and a plain `cargo bench` command), a favicon, and links to `AUDIT.md` and `SECURITY.md` on the landing page.

What remains is copy the maintainer writes. Notes on what to cover:

- **Comparison table** (`README.md`, rendered by `admin/bench-report`'s `comparison_table`):
  - Whether to add columns for binary size (from `BENCHMARKS.md`'s Build cost), audit status, and maturity, or keep those in the bullets under the table.
  - Whether OpenSSL gets a row; it is timed in `BENCHMARKS.md` but absent from the table.
  - How the "What the table leaves out favors the others" bullets frame FIPS, audits, and maturity.
- **crates.io description** (`rind/Cargo.toml`): whether "forked from graviola" still says what rind is now that it no longer tracks Graviola.
- **Website pitch**: whether the landing page needs anything beyond the README's words it quotes.

## Waiting

- Maintainer: write the comparison table framing and crates.io description from the notes above; an agent cannot, since this is the maintainer's own voice. Done when the notes are settled and this quest is deleted.
