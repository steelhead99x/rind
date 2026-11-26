# [S] Close what the 2026-11-21 docs audit left

## Goal

The documentation gaps the docs audit found that need a Rust edit or a maintainer's call are closed, so the next `docs` audit starts from a cleaner baseline. The audit's PR already fixed the mechanical ones.

## Plan

- The published adapters `rind-dimpl`, `rind-jsonwebtoken`, `rind-object-store`, `rind-openmls`, `rind-rcgen`, `rind-rustls`, and `rind-str0m` carry no `#![warn(missing_docs)]`, unlike `rind`, `rind-ring`, `rind-aws-lc-rs`, and `rind-fips`. Every item of theirs is documented today (`RUSTFLAGS='-W missing_docs' cargo check -p <crate>` is silent), so add the lint to each `lib.rs` and let the gate's `--deny warnings` hold it.
- The `VG` abbreviation for pyca/verified-garbage is defined only in `proofs/README.md`, yet BENCHMARKS.md uses it 7 times and ALGORITHMS.md 35. The audit defined it once in ALGORITHMS.md; BENCHMARKS.md is generated, so say "verified-garbage (VG)" at its first use in `admin/bench-report`'s text or in `benchmarks/gaps.toml`, then render.
- AUDIT.md's `unsafe` table is counted by hand from `admin/audit unsafe` and had drifted from 453 to 720 in `rind/src/low/x86_64` since `2abc90e9`. Have `admin/audit check` fail when a row's count differs from `admin/audit unsafe`'s, as it already does for the pins table, so the table is generated or checked rather than recounted.

## Related

- [Check every Markdown link and anchor in the gate](/quest/m2/docs-links-check.md) - the check that would have caught the broken anchor this audit found
