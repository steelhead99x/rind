# [L] rind-aws-lc-rs passes aws-lc-rs's own test suite

## Goal

rind-aws-lc-rs runs aws-lc-rs's own tests, vendored from the aws-lc-rs release its version tracks, against the adapter, as rind-ring runs ring's under `rind-ring/tests/ring/`. Each upstream test that exercises something rind cannot back is skipped with a pointer to the README's "Not offered" list. Every other upstream test passes.

## Plan

Planned with the maintainer on 2026-11-12. ✅ Port upstream's tests (rejected: differential tests written in rind against aws-lc-rs, which lose upstream's edge cases; both). Upstream's suite also checks the adapter rule itself: it behaves exactly as aws-lc-rs does.

Why: on the 2026-11-12 nightly run, 228 of rind-aws-lc-rs's 510 functions never ran under any test, and about 60% of its lines ran. Most of the gap is in `aead.rs`, `aead/tls.rs`, `rsa.rs`, `signature.rs`, `cipher.rs`, `agreement.rs`, and `error.rs`. aws-lc-rs's own tests reach 95.8% of its Rust lines (Codecov's last `main` upload, 2024-04-29; its coverage job now runs only on PRs).

Guidance:

- Source: `aws-lc-rs/tests/` and `aws-lc-rs/tests/data/` in [aws/aws-lc-rs](https://github.com/aws/aws-lc-rs), at the tag matching the version `rind-aws-lc-rs/Cargo.toml` tracks (v1.19.0 on 2026-11-12). The published crate ships no tests, so take them from the repository. Keep the license headers, and confirm the license terms the way rind-ring did for ring's.
- Exclude the vendored tests from the published package, as `rind-ring/Cargo.toml` does with `exclude = ["tests/ring"]`.
- Expect failures, which are divergences. Under the adapter rule each one is a bug: fix it in this PR when it is small, otherwise plan a follow-up. ML-DSA is offered (`signature::{ML_DSA_44, ML_DSA_65, ML_DSA_87}` and `PqdsaKeyPair`; see [ALGORITHMS.md](/ALGORITHMS.md)), so `pqdsa_test.rs` is in scope. FIPS-only tests stay skipped, since the adapter refuses `fips`.
- Record how to re-vendor on an aws-lc-rs bump next to where rind-ring records it, if it does.

## Related

- [Adapter crates' surviving mutants](/quest/m2/confidence/mutants-adapters.md) - these tests kill many of rind-aws-lc-rs's mutants, so that quest starts after this one
