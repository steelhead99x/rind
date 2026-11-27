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
- `Debug` and `Display` survivors stay excluded, as quest/m2/confidence/mutants-adapters.md and upstream main's `.cargo/mutants.toml` keep them; the tests that checked only those are gone.

x86_64 campaigns, none missed once the two fixes above are in: `rind-rustls` 281 mutants, `rind-dimpl` 91, `rind-ring` 331, `rind-str0m` 59, `rind-rcgen` 113, `rind-openmls` 98. Their sources and mutant lists are the same on the PR head as where the hosted campaigns ran.

`rind-aws-lc-rs`, x86_64: on main at `7c3158d5`, 24 of the 35 mutants its hosted campaign at `1a2a68c` missed still survived, besides the nine `Debug` and `Display` ones. The PR branch kills 20 with tests against aws-lc-rs and excludes the equivalent or feature-gated rest. One test found a divergence, now fixed: `PublicEncryptingKey::from_der` refused a 1024-bit key as `InvalidEncoding` where aws-lc-rs says `TooSmall`. Those mutants ran locally (cargo-mutants, no CPU-masked rows, which only add tests).

Left:
- A whole `rind-aws-lc-rs` x86_64 campaign on the current head, for mutants added since `1a2a68c`: `gh workflow run mutants.yml --ref <branch> -f campaign=x86_64 -f package=rind-aws-lc-rs` (960 mutants; Actions does not run on the fork's account right now).
- The aarch64 campaigns.
