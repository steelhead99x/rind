# [M] rind's adapters run on wasm32

## Goal

rind-rustls and rind-ring build and pass their tests on `wasm32-wasip2`, and build on `wasm32-unknown-unknown`, in CI, so a project that ships to the browser or to a wasm runtime can move its TLS and its ring users to rind. MIGRATE.md stops telling such a project to stop.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): ✅ adapters on wasm32 are one of the four ecosystem bets. The 2026-11-04 plan left Bitwarden and Matrix out because they "need wasm", and [MIGRATE.md](/MIGRATE.md) tells an agent to stop if "a binary's release target needs an adapter on wasm32".

The library is already there: every PR compiles `rind` for both wasm targets, and the nightly runs its vector tests on `wasm32-wasip2` under wasmtime (`just wasm`, `sh/wasm.sh`, PLATFORMS.md). What is missing is the adapters, which nothing builds for wasm, so nobody knows what fails.

- Find out first: build each adapter for both targets and list what breaks, in the adapter or in its upstream. rustls needs a time source and a certificate verifier that work on the target, and those are the caller's to supply as they are with any provider.
- rind-rustls and rind-ring first, since they are what a wasm project reaches for. Then each other published adapter either builds on wasm in the same CI job or its README says it does not and why.
- wasm is where pure Rust wins outright: aws-lc-rs does not build for it, and ring needs a C compiler targeting wasm. So the tests there run without the differential ones, as `rind`'s do, and the comparison in the README is "builds at all".
- Constant time is unchecked on wasm, and PLATFORMS.md already says why. The adapters' READMEs point there.
- `wasm32-unknown-unknown` stays compile-only, as it is for `rind`: its tests need a JavaScript host.
- Update MIGRATE.md's two wasm sentences, MIGRATING.md, and PLATFORMS.md's wasm paragraph to name the adapters CI covers.
- An npm package is not part of this (offered on 2026-11-12 and not picked).
