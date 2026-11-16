# [S] Adapter mutants

## Goal

Mutation testing covers the adapters correctly, and the package lists and test runs are not duplicated or stale.

## Plan

Difficulty: 4/10 (estimate).

Fork PR #23 (mirrored by fork #113), head `f2e26577`. Score 6/10. Upstream twin #792. A partial diff is saved. Also needs fork fix `bf25c044`; expect a conflict with upstream #804.

Done on the PR branch (checked with `admin/mutants-cargo-test`, `admin/mutants --expand-diff-self-test`, and `rustfmt`; the campaign and nextest did not run, since `cargo-mutants` and the git dependencies are unavailable offline):
- The wipe run of rind's tests includes `--lib` again.
- The `Padding` pin sits inside `macro_rules`, which cargo-mutants never mutates, so it is gone.
- An empty package selection is the workspace, like `--workspace`.
- AES-128 QUIC and TLS 1.2 limits match rustls 0.23.46's aws-lc-rs provider; the QUIC test now pins the RFC 9001 values.
- The split-out package list comes from the manifests (`wiping_packages`), not by hand.
- `rind-rcgen`'s second build runs only `--lib --test zeroing`.
- `RIND_MUTANTS_STUB` is gone.

Left:
- Run the campaign on GitHub-hosted runners (`gh workflow run mutants.yml --ref <branch> -f package=rind-rustls`) and the nextest runs in `just check`.
- The "extra test run" low is not pinned down; recheck once the above runs.
- Expect a conflict with upstream #804.
