# [M] rind-openmls runs MLS on rind

## Goal

A published `rind-openmls` adapter implements openmls's `OpenMlsCrypto` provider traits on rind, covering the MLS ciphersuites rind's primitives back, so an openmls user drops its RustCrypto or libcrux provider for rind.

## Plan

Decided with the maintainer on 2026-11-07, as a follow-up from [moq-dev/rind#449](https://github.com/moq-dev/rind/pull/449). openmls needs HPKE with the exporter, which `rind::hpke` offers, plus AEADs, HKDF, and signatures rind already has.

- Follow the adapter rules: its own crate, a version matching openmls's breaking version (CONTRIBUTING.md's Releases), no re-exported rind types, and exactly the API of the openmls provider it replaces, adding nothing (`AGENTS.md`). Say in the PR which of openmls's providers, `openmls_rust_crypto` or `openmls_libcrux_crypto`, it mirrors item for item.
- No `MissingFeature` and no `Result` on its constructor, which an earlier plan here had: [the adapters epic](/quest/m0/adapters/README.md) removes both from every adapter.
- Run openmls's provider test suite and its interop tests against the RustCrypto provider. Document unsupported ciphersuites, such as X448 and Ed448, in the README.

## Related

- [HPKE's post-quantum KEMs](/quest/m4/protocols/hpke-pq.md) - the KEMs under MLS's post-quantum ciphersuites, which this adds once both have landed
