# [S] Adapter mutants

## Goal

Mutation testing covers the adapters correctly, and the package lists and test runs are not duplicated or stale.

## Plan

Difficulty: 4/10 (estimate).

Fork PR #23 (mirrored by fork #113). Upstream twin #792, on hold.

Done on the PR branch:
- The `Padding` pin sat inside `macro_rules`, which cargo-mutants never mutates, so it is gone.
- AES-128 QUIC and TLS 1.2 limits match rustls 0.23.46's aws-lc-rs provider; the QUIC test pins the RFC 9001 values.
- [kixel-ai/rind#609](https://github.com/kixel-ai/rind/pull/609) removed the `wipe` feature, and with it the grouped test runs and `admin/mutants-cargo`; `sh/dispatch.sh` and `admin/mutants` are `main`'s.
- `rind-rcgen`'s tests build with its `zeroize` feature, so `zeroize_clears` runs and kills `impl Zeroize for KeyPair` replaced with `()`.
- The `rind-openmls` `sign` exclusion matches the scratch array's bound by column; the merge of #804's column pins had moved it onto the caught SEQUENCE length.

x86_64 campaigns, none missed once the two fixes above are in: `rind-rustls` 281 mutants, `rind-dimpl` 91, `rind-ring` 331, `rind-str0m` 59, `rind-rcgen` 113, `rind-openmls` 98. Their sources and mutant lists are the same on the PR head as where the hosted campaigns ran.

Left:
- `rind-aws-lc-rs`: its hosted campaign at `1a2a68c` missed 35 mutants that no exclusion ever covered, and the crate has since gained about 3,000 lines of tests. Rerun it on the current head, as `gh workflow run mutants.yml --ref <branch> -f campaign=x86_64 -f package=rind-aws-lc-rs`, and kill or exclude what survives.
- The aarch64 campaigns.
