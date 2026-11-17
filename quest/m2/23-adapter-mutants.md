# [S] Adapter mutants

## Goal

Mutation testing covers the adapters correctly, and the package lists and test runs are not duplicated or stale.

## Plan

Difficulty: 4/10 (estimate).

Fork PR #23 (mirrored by fork #113), head `f2e26577`. Score 6/10. Upstream twin #792. A partial diff is saved. Also needs fork fix `bf25c044`; expect a conflict with upstream #804.

Mediums:
- Run rind's unit tests with wipe again, using `--lib`.
- The Padding pin sits inside `macro_rules` and probably matches nothing.
- An empty package selection is not the same build as `--workspace`.
- Compare the AES-128 QUIC and TLS 1.2 limits with aws-lc-rs.

Lows:
- The split-out package list is hand-written.
- `rind-rcgen`'s tests run twice.
- There is an extra test run.
- `RIND_MUTANTS_STUB` is dead.
