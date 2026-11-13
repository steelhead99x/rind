# [S] Adapter crates' surviving mutants

## Goal

The 103 mutants in the `rind-<consumer>` adapters that no test catches are killed by tests, and their `exclude_re` entries in `.cargo/mutants.toml` are gone. Most are `Debug` and `Display` impls, `PartialEq` on algorithm handles, and accessors no test compares with the upstream crate's: `tag_len`, `block_len`, `chaining_len`, rustls' `encrypted_payload_len`, and QUIC's confidentiality and integrity limits.

## Plan

- Where the upstream crate has the same value, such as ring's or rustls' aws-lc-rs provider's, test against it rather than a literal.
- Run `admin/mutants -p <crate>` on each adapter to confirm none survive.
- Start from the list as the adapter PRs leave it. Those PRs rewrite the adapters to their upstreams' exact APIs, and [kixel-ai/rind#521](https://github.com/kixel-ai/rind/pull/521) and [kixel-ai/rind#515](https://github.com/kixel-ai/rind/pull/515) already edit this block of `exclude_re`, so recount the survivors, and drop each entry that no longer matches a mutant, before writing tests.

## Required

- [rind-aws-lc-rs passes aws-lc-rs's own test suite](/quest/m2/confidence/aws-lc-rs-upstream-tests.md) - upstream's tests kill rind-aws-lc-rs's mutants first, so none gets a hand-written test
