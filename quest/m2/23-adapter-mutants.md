# [S] Adapter mutants

## Goal

Mutation testing covers the adapters correctly, and the package lists and test runs are not duplicated or stale.

## Plan

Difficulty: 4/10 (estimate).

Fork PR #23 (mirrored by fork #113), head `f2e26577`. Score 6/10. Upstream twin #792. A partial diff is saved. Also needs fork fix `bf25c044`; expect a conflict with upstream #804.

Done on the PR branch (checked with `admin/mutants --expand-diff-self-test` and `rustfmt`; the campaign and nextest did not run, since `cargo-mutants` and the git dependencies are unavailable offline):
- The `Padding` pin sits inside `macro_rules`, which cargo-mutants never mutates, so it is gone.
- AES-128 QUIC and TLS 1.2 limits match rustls 0.23.46's aws-lc-rs provider; the QUIC test now pins the RFC 9001 values.
- `RIND_MUTANTS_STUB` is gone.
- [kixel-ai/rind#609](https://github.com/kixel-ai/rind/pull/609) removed the `wipe` feature, so the grouped test runs (`wiping_packages`, `run_grouped`), `admin/mutants-cargo` and its test, and the `wipe` features they set are gone from this branch. `sh/dispatch.sh`, `admin/mutants`, and the manifests are `main`'s.

Hosted x86_64 campaigns on the PR branch, none missed: `rind-rustls` 280 mutants (186 caught, 94 unviable), `rind-dimpl` 90 (82, 8), `rind-ring` 331 (239, 92). No Debug or Display pin is left in `.cargo/mutants.toml`.

Left:
- The `rind-aws-lc-rs`, `rind-rcgen`, `rind-str0m`, and `rind-openmls` campaigns, and the other architectures.
- `just check`, clippy, and nextest in CI or the dev shell.
- Expect a conflict with upstream #804.
