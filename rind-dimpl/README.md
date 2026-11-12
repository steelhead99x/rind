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

`default_provider()` returns dimpl's `CryptoProvider`, as `dimpl::crypto::aws_lc_rs::default_provider()` does, so swapping one for the other changes no other code. rind cannot back:

- The PSK suite AES-128-CCM-8.

Where it behaves differently:

- ChaCha20-Poly1305 comes first on a CPU where rind runs AES without CPU instructions, for speed.
- A PEM key whose preamble starts with `0` is refused: that byte is the tag every DER key starts with, and a DER key's later bytes are secret, so rind never searches them for PEM.

License: Apache-2.0 OR ISC OR MIT-0
