<h1 align="center">rind-openmls</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/moq-dev/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-openmls)](https://crates.io/crates/rind-openmls)
[![Documentation](https://img.shields.io/docsrs/rind-openmls)](https://docs.rs/rind-openmls/)

This crate provides a crypto provider for [OpenMLS](https://github.com/openmls/openmls), backed by [rind](https://github.com/moq-dev/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).

It offers exactly the API of [openmls_rust_crypto](https://docs.rs/openmls_rust_crypto), item for item, so replacing that dependency and its `use` lines is the whole migration:

```rust
use rind_openmls::OpenMlsRustCrypto;

let provider = OpenMlsRustCrypto::default();
```

It offers the ciphersuites openmls_rust_crypto does: `MLS_128_DHKEMX25519_AES128GCM_SHA256_Ed25519`, `MLS_128_DHKEMX25519_CHACHA20POLY1305_SHA256_Ed25519`, and `MLS_128_DHKEMP256_AES128GCM_SHA256_P256`.
It signs and verifies with Ed25519 and ECDSA on P-256 and P-384, seals HPKE to X25519, P-256, and P-384, and draws randomness from the system's source.

What rind cannot back:

- The X448 and Ed448 ciphersuites, which openmls_rust_crypto lacks too.
- The P-384 and P-521 ciphersuites, which openmls_rust_crypto lacks too. rind has their primitives, so they come once openmls_rust_crypto offers them or fixed test vectors can validate them: the MLS test vectors give some P-521 private keys without their leading zero ([mlswg/mls-implementations#176](https://github.com/mlswg/mls-implementations/issues/176)), and openmls's copy of the crypto-basics vectors signs both suites over SHA-256.
- The `draft-ietf-mls-pq-ciphersuites` feature: rind's HPKE has no post-quantum KEM yet.
- The `targeted-messages-draft` feature: rind's HPKE has no PSK mode.
- The `virtual-clients-draft` feature: rind has no FF1.

Naming one of those features fails to resolve, and turning on openmls's own `targeted-messages-draft` or `virtual-clients-draft` fails to compile this crate, rather than failing at run time.

License: Apache-2.0 OR ISC OR MIT-0
