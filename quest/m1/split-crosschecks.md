# [S] Split rind/tests/crosschecks.rs into per-family test binaries

## Goal

`rind/tests/crosschecks.rs` (191 KB) is split into per-family integration test binaries (symmetric, curves, rsa, post-quantum, and protocols) so an algorithm-scoped `cargo nextest` run recompiles and links only the touched family's test binary instead of the whole monolith. Cargo still builds every dev-dependency of `rind` for any of its test targets, so this saves no oracle-crate compilation; those stay cached across local edits.

## Plan

Today `rind/tests/crosschecks.rs` is a single 191 KB integration test target importing every differential-test oracle (`aws-lc-rs`, `aws-lc-sys`, RustCrypto symmetric crates, `rsa`, `blind-rsa-signatures`, `libcrux-*`, `ml-kem`, `ml-dsa`, `slh-dsa`, `fips205`, `hpke-rs`, `pakery-*`, `matter-crypto`, `akd_core`, `vrf-rfc9381`, `frost-*`, `voprf`, `p256`/`p384`/`p521`). Even when running one symmetric test, Cargo must recompile and link the whole monolith after any change to `rind`.

- Isolating the oracle crates too would take a separate test package per family, each with its own dev-dependencies. Not planned: the oracles compile once and stay cached, so that buys only cold builds, at the cost of five more workspace crates.

- ✅ Split `rind/tests/crosschecks.rs` into per-family integration test files (maintainer, 2026-11-21). Placed in `m1` ("the agent hosts' smaller costs") because `m0`'s `mbx`, `just check`, and test-profile quests deliver the urgent wins first.
- Split `rind/tests/crosschecks.rs` into focused integration test targets under `rind/tests/` (for example `crosschecks_symmetric.rs`, `crosschecks_curves.rs`, `crosschecks_rsa.rs`, `crosschecks_pq.rs`, `crosschecks_protocols.rs`), sharing any tiny helpers under `rind/tests/oracle/` (which already exists).
- Update `TESTING.md` (checked by `admin/testing`), `admin/x86-cpu` (`SKIP` filters for `slh_dsa_*::sign_verify`), and `sh/dispatch.sh` / `sh/test-filter.sh` (if landed) so every test name and skip rule continues to match. If [scoped-tests](/quest/m0/ci-speed/scoped-tests.md) landed first, point its self-test's trigger and its unlisted-test inventory at every split file instead of `crosschecks.rs`, and its target selectors at the per-family binaries, and verify `cargo nextest list -p rind` preserves the exact test count.

## Related

- [Scope local tests to changed primitives and skip adapter fan-out on low/ edits](/quest/m0/ci-speed/scoped-tests.md) - pairs `--test <family>` selection with per-family test binaries
