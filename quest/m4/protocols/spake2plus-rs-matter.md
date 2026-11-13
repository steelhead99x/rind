# [S] SPAKE2+ matches rs-matter's

## Goal

`rind::spake2plus`'s Matter PASE suite runs a differential test against rs-matter's own SPAKE2+ engine, the implementation Rust Matter devices commission with, alongside the connectedhomeip vectors and the `matter-crypto` differential it already has.

## Plan

- Add a test beside `high::spake2plus::matches_matter_crypto` that runs a PASE handshake with injected ephemeral scalars through rs-matter's prover and verifier and through rind's, and compares the shares, confirmations, and `Ke`.
- Take rs-matter, or the crate that publishes its engine, as a crates.io dev-dependency only; `deny.toml` denies git dependencies.
- Decided with the maintainer on 2026-11-12: connectedhomeip's vectors and the `matter-crypto` differential are enough for SPAKE2+ to land; this test comes once rs-matter publishes its engine (rejected: block SPAKE2+ on rs-matter now).
- Decided with the maintainer on 2026-11-13: ✅ keep this quest (rejected: drop it).

## Waiting

- project-chip/rs-matter: publishes its SPAKE2+ engine, `sc::pase::spake2p`, on crates.io. On 2026-11-12 rs-matter 0.4.1 kept it `pub(crate)`, and its main branch had moved it into the unpublished `rs-matter-sc` crate. Check with `cargo search rs-matter-sc`, then whether the newest rs-matter or rs-matter-sc exports the module.
