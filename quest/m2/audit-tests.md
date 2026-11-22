# [M] Audit test coverage

## Goal

Run the `tests` audit: `quest audit tests` prints what it checks, what each finding becomes, and how to plan its next run.

## Plan

Baseline from the first run (2026-11-21, `main` at `253c93f6`). Coverage is the nightly `coverage.yml` report, `admin/coverage` under `cargo llvm-cov` with `SLOW_TESTS=1` and the CPU-denied and SDE reruns, read from the last successful run's "Measure coverage" log; its function counts are per monomorphized instance. Lines, Linux/x86_64: `rind` 99.05% (1058 of 111142 missed), `rind-aws-lc-rs` 94.21%, `rind-ring` 94.83%, `rind-rustls` 98.84%, `rind-dimpl` 94.76%, `rind-str0m` 96.62%, `rind-rcgen` 90.70%, `rind-object-store` 87.14%, `rind-jsonwebtoken` 97.24%, `rind-openmls` 99.73%, `rind-dart` 96.99%, `rind-python` 95.42%; total 98.43% lines, 94.62% functions, 82.99% branches. macOS/aarch64 total: 98.61% lines, 94.35% functions. `rind-fips` (90.55%) and `rind-openssl` (77.52%) are unpublished and left out of the goal.

Scope this audit leaves to others: function-level gaps belong to [every published function runs under a test](/quest/m2/confidence/uncovered-functions.md), wiping to [zeroing and scratch gaps](/quest/m2/confidence/zeroing-and-scratch-gaps.md), wall-clock and skipped tests to [a test that skips itself says so](/quest/m2/confidence/skipped-tests-pass.md), and what tests cost to the `cost` audit.

Check first:

- Cargo features no test job turns on. Run 1 found `rind-aws-lc-rs`'s `unstable` and `dev-tests-only` never built in a test, and fixed it with a self dev-dependency as `rind-rcgen` does for `zeroize`; list `[features]` in each `Cargo.toml` against the `cargo test` lines in `build.yml` and `sh/dispatch.sh`.
- `proptest-regressions/` files whose source file has no `proptest!` left, which proptest never replays: match each file's path to its `rind/src` or `rind/tests` source.
- `#[should_panic]` without `expected`, and early `return`s in tests.
- Wycheproof files `admin/testing` lists against `thirdparty/vectors/wycheproof/testvectors_v1`, and the upstream directory for new files of an algorithm rind offers.
- `fix` commits that touch Rust and no test: 33 of 93 on run 1, the two read, #324 and #244, had tests.

## Audit

- tests

## Required

- [m1](/quest/m1/README.md) - the audit runs once per milestone

## Scheduled

- 2026-11-28 - a week after the first run, so a milestone that closes fast does not rerun the audit at once
