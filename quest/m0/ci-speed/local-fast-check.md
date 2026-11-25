# [M] Local just check is a fast test-only loop with single-pass clippy

## Goal

Running `just check` locally completes in seconds on a warm cache by running only `fmt`, a single-pass test build and `cargo nextest` run (with clippy enforced during the test compilation via `RUSTC_WORKSPACE_WRAPPER=clippy-driver`, eliminating the separate `cargo clippy --all-targets` build), and sub-second repository lints—skipping `cross`, `wasm`, `msrv`, `vartime`, `adapters`, `site`, `cargo doc`, doc-tests, and `rind-acvp` (unless `rind-fips`/`rind-acvp` changed). `CONTRIBUTING.md` directs agents and developers to run `just check` before pushing instead of `just ci`.

## Plan

Today `sh/dispatch.sh` maps `just check` to the exact same 15+ modules as `just ci` (`verb=$action; [[ "$verb" != ci ]] || verb=check`), and `CONTRIBUTING.md` line 49 says "Run `just ci` before every push." Inside `check:rs` (11m 05s on queue run `44980938788`), `cargo clippy --all-targets` (2m 02s) and `cargo nextest run` (2m 39s compile) compile the entire workspace twice with different rustc wrappers, followed by `rind-fips-module`/`rind-acvp` clippy and tests (3m 32s), doc-tests (22s), and `cargo doc` (1m 01s).

- ✅ Local `just check` runs `fmt` + scoped `cargo nextest` (no separate `clippy` build, no `doc`/`doctests`, no `rind-acvp` unless `rind-fips`/`rind-acvp` changed, no `cross`/`msrv`/`wasm`/`adapters`/`vartime`/`site`) + sub-second repo lints (`quest`, `shell`, `nix`, `testing`, `audit`, `license`, `compat`, `bench`, `gh`, `versions`, `deny`); `CONTRIBUTING.md` tells agents to run `just check` before pushing instead of `just ci` (maintainer, 2026-11-21; rejected: separate `cargo clippy --lib --tests` pass; keeping full 19-crate `check rs` locally).
- ✅ Adopt `moq-dev/moq`'s single-pass test-and-clippy pattern (`rs/justfile`: `CARGO_BUILD_WARNINGS=deny RUSTC_WORKSPACE_WRAPPER=$(command -v clippy-driver) cargo nextest run --locked --tests ...`) so clippy runs inside the test compilation itself with no second compile—both locally in `just check` and in `check:rs` for `just ci` / `pr-check.yml` / `queue-build.yml` (maintainer, 2026-11-21, referencing `../moq`). `--tests` skips benches, examples, and every `[[bin]]` that sets `test = false`, such as all of `rind-fuzz`'s fuzz targets, which `cargo clippy --all-targets` lints today, and nextest cannot run `rind-bench`'s `harness = false` criterion benches, so `--all-targets` is no substitute: `check:rs` follows the nextest pass with `cargo build --bins --benches --examples` under the same wrapper and `CARGO_BUILD_WARNINGS=deny`, which reuses the pass's dependency artifacts and keeps every target, fuzz targets included, linted before merge. Local `just check` skips that step.
- Keep `just ci` (`just gate` / nightly `check.yml`) covering `cargo doc`, doc-tests, `--all-targets` (benches/examples/fuzzers), `rind-acvp` whenever `rind` changes, and the heavy cross/adapter/msrv/vartime modules.
- Record warm and cold `just check` timings before and after in the PR body.

## Related

- [The merge queue builds through mbx, warm across groups](/quest/m0/queue-warm-target.md) - activates `mbx` in `flake.nix` so local `just check` builds start warm across worktrees
- [Optimize dev/test Cargo profiles for fast test runs](/quest/m0/ci-speed/test-profiles.md) - cuts the `nextest` run time inside `just check`
- [Thin the self-hosted merge queue to host rs and fast lints](/quest/m0/ci-speed/thin-merge-queue.md) - shares the single-pass `check:rs` speedup in `queue-build.yml`
