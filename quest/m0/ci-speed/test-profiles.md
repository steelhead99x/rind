# [S] Optimize dev/test Cargo profiles for fast test runs

## Goal

Workspace dev/test builds use compact line-table debuginfo and optimize pure-Rust cryptographic dependencies and slow test paths without breaking `admin/ctgrind`'s debug checks, cutting `cargo nextest` wall time from ~65s locally (~212s on 4-core hosted runners) to ~5–10s and shrinking linked test binaries and disk writes.

## Plan

Profiled from `nextest` output on run `44980938788` (1,929 tests, 64.6s wall on 16 cores / 212.3s on 4-core hosted runner): 5 unoptimized `-O0` tests dominate the wall clock (`rind::mid::slhdsa::tests::acvp_sig_gen` 59.0s, `rind::mid::argon2::tests::reference_kat` 50.5s, `rind::high::oprf::voprf::tests::largest_batch` 46.0s, `rind::crosschecks::blind_rsa::matches_blind_rsa_signatures` 28.7s, `rind-aws-lc-rs::rsa_test::rsa8192_*` 22–24s). `Cargo.toml` currently sets no `[profile.dev]` `debug` or `opt-level` overrides beyond the 4 `overflow-checks`/`debug-assertions` entries for `ctgrind`.

- ✅ Optimize dev-dependencies and/or test profiles in `Cargo.toml` while preserving `ctgrind`'s debug builds (maintainer, 2026-11-21, referencing `../moq`).
- Follow `moq-dev/moq`'s `Cargo.toml` pattern:
  - Set `[profile.dev] debug = "line-tables-only"` (`profile.test` inherits it; drops full DWARF variable/type info while keeping panic/backtrace `file:line`, slashing link time and binary/disk size; `~/.cargo/config.toml` `debug = false` continues to override locally where configured).
  - Set `[profile.dev.package."*"] opt-level = 2` (or targeted `opt-level = 3` on slow oracle/math crates like `rsa`, `slh-dsa`, `fips205`, `voprf`, `p256`, `p384`, `p521`, `crypto-bigint`, `curve25519-dalek`, `blind-rsa-signatures` — measure both and check `ctgrind` compatibility).
  - For slow tests inside `rind` itself (`slhdsa::acvp_sig_gen`, `argon2::reference_kat`, `voprf::largest_batch`), evaluate `[profile.test] opt-level = 1` vs a dedicated `[profile.test-fast]` (`inherits = "test"`, `opt-level = 2`, `debug-assertions = true`, `overflow-checks = true`) used by `just check` / `pr-check.yml` / `queue-build.yml`, keeping plain debug available for `admin/ctgrind` and `debug_assertions` checks. With `test-fast`, `check:rs`'s follow-up `cargo build --benches --examples` ([local-fast-check](/quest/m0/ci-speed/local-fast-check.md)) passes the same `--profile test-fast`, since a build under `dev` writes to `target/debug` and recompiles every dependency the nextest pass built in `target/test-fast`.
- Verify `admin/ctgrind` (debug and release rows, including the 4 crates with `overflow-checks = false` / `debug-assertions = false` in `Cargo.toml`) still passes with no false positives or suppressed checks, and record before/after `nextest` wall time and compile time in the PR body.

## Related

- [Local just check is a fast test-only loop with single-pass clippy](/quest/m0/ci-speed/local-fast-check.md) - runs `nextest` as the primary local loop
- [The merge queue builds through mbx, warm across groups](/quest/m0/queue-warm-target.md) - caches the optimized dev-dependencies once across worktrees and queue runs
