<h1 align="center">rind-dimpl</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/moq-dev/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-dimpl)](https://crates.io/crates/rind-dimpl)
[![Documentation](https://img.shields.io/docsrs/rind-dimpl)](https://docs.rs/rind-dimpl/)

This crate provides a `CryptoProvider` for [dimpl](https://github.com/algesten/dimpl), backed by [rind](https://github.com/moq-dev/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).

Build dimpl with `default-features = false`, since its default features compile aws-lc-rs.
Then hand the provider to each config:

```rust
let config = dimpl::Config::builder()
    .with_crypto_provider(rind_dimpl::default_provider())
    .build()?;
```

Or install it for the process with `dimpl::crypto::CryptoProvider::install_default`.

It negotiates DTLS 1.2 ECDHE-ECDSA and DTLS 1.3 with AES-128-GCM, AES-256-GCM, and ChaCha20-Poly1305, over X25519, P-256, and P-384, and signs with ECDSA P-256 or P-384 keys in PKCS#8 or SEC1, as DER or PEM.
dimpl's PSK suite, AES-128-CCM-8, is not offered.
A PEM key whose preamble starts with `0` is refused: that byte is the tag every DER key starts with, and a DER key's later bytes are secret, so rind never searches them for PEM.

License: Apache-2.0 OR ISC OR MIT-0
