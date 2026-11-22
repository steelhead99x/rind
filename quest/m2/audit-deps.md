# [M] Audit dependencies

## Goal

Run the `deps` audit: `quest audit deps` prints what it checks, what each finding becomes, and how to plan its next run.

## Audit

- deps

## Plan

Baseline from the 2026-11-21 run (m1), which covered releases through that date; its findings and results stay in its PR.

- Scope it covered: every `Cargo.toml` and `Cargo.lock` (the workspace, `fuzz`, `rind-bench`, the three standalone workspaces `admin/build-cost-fixtures/*`, `patch/fixture`, and the `thirdparty/blind-rsa-signatures` fork), `flake.nix` and its pins, `.github` actions and the tool versions workflows install, `site` and `site/deploy` (bun), and the two `pyproject.toml` files. The copied code and the crates' routine updates belong to [upstream-updates](/quest/m2/upstream-updates.md); the audit read its pins, not their diffs.
- Check first: [blind-rsa-upstream](/quest/m2/blind-rsa-upstream.md) and [dependency-pins](/quest/m2/dependency-pins.md), if still open. Then the libcrux release wave of 2026-11-19 (0.0.10 to 0.0.12 across the `libcrux-*` crates), hpke-rs 0.8.1, crabgrind 0.6.0, and x509-cert 0.3.1, which `sh/cooldown.sh` kept out of the lock until 2026-11-26. `rind-bench`'s libcrux crates trail `rind`'s and `fuzz`'s, which is why the lock holds two or three of each `libcrux-*` crate and crabgrind 0.2, 0.3, and 0.4.
- Holds that are decided: `untrusted` 0.7 in `rind-aws-lc-rs` mirrors aws-lc-rs; `foreign-types` 0.3 is the openssl crate's; `p256`, `p384`, `p521`, and `rand_core` 0.13 and 0.6 in `rind` and `fuzz` are voprf 0.5's; `voprf =0.6.0-pre.2` in `rind-bench` is the only release on RustCrypto's current curves; `rust-version` 1.91 in `rind-openmls`, 1.94 in `fuzz`, and 1.95 in `rind-bench` each name their cause.
- Method that worked: `cargo deny check` in `nix develop` (it fetches the advisory database into `CARGO_HOME`, about five minutes cold), the crates.io sparse index for latest releases and each locked version's `rust_version`, `git ls-remote --tags` for actions and tools, and a bare `--filter=blob:none` clone for fork drift.
- A dependency a grep finds no use of may still be used: `fuzz` compiles `rind/tests/oracle/*.rs` and `rind/src/test/reference.rs` through `#[path]`, so `libcrux-ed25519` and `libcrux-p256` show no use in `fuzz/`; macros name `p384`, `p521`, and the `frost-*` crates; `md-5`'s library is `md5`. Remove it and `cargo check --all-targets` before calling it unused.
- Left out: Lean, Aeneas, and Mathlib pins (the proof re-audit's), and Nix packages the shells take from nixpkgs.

## Required

- [m1](/quest/m1/README.md) - the audit runs once per milestone

## Scheduled

- 2026-11-28 - one week after the last run
