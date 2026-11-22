# [S] A test that skips itself says so

## Goal

A test that returns early because a CPU feature or `SLOW_TESTS` is missing prints that it did, and the gate cannot report a primitive covered when its test never ran. A hang detector in a test waits on its child without a wall-clock deadline.

## Plan

Found by the `tests` audit's run on `main` at `253c93f6`. Verified by reading each site; none ran under valgrind or a CPU the site skips.

- 32 unit tests under `rind/src/low/{x86_64,aarch64}/` begin `if !is_x86_feature_detected!("avx2") { return; }` (28), `bmi2` (1), or `is_aarch64_feature_detected!("sha3")` (3), and report as passed on a CPU without it. Each kernel is also reached through the rind-level tests, and `detects_the_expected_cpu` fails a tier whose runner lacks the feature `RIND_TEST_X86_AVX2` and its siblings say it has, so CI lands the right path. What is missing is the line saying a kernel test did not run, which `high::hmac::ct_sde_hmac` already asserts instead (`assert!(is_x86_feature_detected!("sha"), ...)`).
- 11 sites read `SLOW_TESTS` and `return` or skip their long vectors when it is unset (`tests/wycheproof.rs` `pbkdf2_tests`, `tests/heap_scratch.rs` `rsa_generate`, `high/digest.rs`, `high/ecdsa.rs`, `high/kem.rs`, `tests/crosschecks.rs`). The merge gate's `cargo nextest run` does not set it, so those vectors run only in `build.yml`'s release step and the artificial-CPU tiers' filtered rerun, and a gate log shows them as passed.
- `rind-fips/tests/fork.rs` and `rind/src/fips_rng.rs`'s fork test poll `waitpid(WNOHANG)` against a 10 s `Instant` deadline and a 1000 x 10 ms loop, so a loaded runner fails them as a hang. `quest context`'s rule is that unit tests mock time instead.

Recommended: give the early returns one helper, `crate::test::skipped(why)`, that prints `skipped: <why>` to stdout and returns, so a nextest log names what did not run, and have the SLOW_TESTS ones call it (rejected: `#[ignore]`, which would need `--include-ignored` in every job that now sets `SLOW_TESTS`). For the two fork tests, block in `waitpid` and let nextest's per-test `slow-timeout` (a `.config/nextest.toml` with `terminate-after`) kill a hang, which a child that never exits would still cause (rejected: a longer deadline, which only moves the flake).

## Waiting

- Maintainer: decide whether a CPU skip should fail instead of print on the tiers that name the feature (recommended: print only, since `detects_the_expected_cpu` already fails a mis-detected tier; the alternative is `assert!` as `ct_sde_hmac` does, which breaks every runner without AVX2 or SHA-3).
- Maintainer: decide whether nextest's `slow-timeout` may stand in for the fork tests' deadline (recommended: yes; the alternative keeps the deadline and accepts the flake).
