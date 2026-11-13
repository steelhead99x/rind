# [S] Adapter crates' surviving mutants

## Goal

The adapters' surviving mutants that change behavior a consumer relies on are killed by tests, and their `exclude_re` entries in `.cargo/mutants.toml` are gone: accessors no test compares with the upstream crate's (`tag_len`, `block_len`, `chaining_len`, rustls' `encrypted_payload_len`, QUIC's confidentiality and integrity limits), `PartialEq` on algorithm handles, and survivors such as rind-dimpl's `SecureRandom::fill` replaced with `Ok(())` and a deleted `(Secp384r1, SHA256)` arm in its `verify_signature`. `Debug` and `Display` survivors stay excluded.

## Plan

- Narrowed on 2026-11-12 while planning [the mutants slim-down](/quest/m0/ci-speed/mutants-slim.md): the maintainer chose to drop low-value mutant work, and the `Debug` and `Display` survivors are that; the rest hide real gaps, such as an RNG that fills nothing.
- Where the upstream crate has the same value, such as ring's or rustls' aws-lc-rs provider's, test against it rather than a literal.
- Confirm none survive with `admin/mutants --file` on Linux, on the files whose entries it drops, or with a hosted campaign scoped to the crate, a `mutants.yml` dispatch with `-f package=<crate>`, since `admin/mutants` runs a whole crate only on GitHub-hosted runners. On Apple silicon `admin/mutants` adds the DIT campaign's `--re` filter, which leaves out the adapters' mutants.
- Start from the list as the adapter PRs left it. They rewrote the adapters to their upstreams' exact APIs, and [kixel-ai/rind#521](https://github.com/kixel-ai/rind/pull/521) and [kixel-ai/rind#515](https://github.com/kixel-ai/rind/pull/515), both merged on 2026-11-10, edited this block of `exclude_re`, so the Goal's 103 was counted before them: recount the survivors, and drop each entry that no longer matches a mutant, before writing tests. Recount with the adapter entries switched off: `admin/mutants` hands its arguments to `cargo mutants`, which reads `.cargo/mutants.toml` and never lists a mutant `exclude_re` matches, so through the file as it is an entry that still hides a survivor looks unused. Copy the file into `.tmp/` without the adapter block and pass it with `cargo mutants`' `--config`, in the same two places as the bullet above: named files on Linux, or the hosted campaign.

## Required

- [rind-aws-lc-rs runs aws-lc-rs's in-crate tests of its public API](/quest/m2/confidence/aws-lc-rs-unit-tests.md) - upstream's tests kill rind-aws-lc-rs's mutants first, so none gets a hand-written test
