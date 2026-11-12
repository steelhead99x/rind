<h1 align="center">rind-str0m</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/moq-dev/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-str0m)](https://crates.io/crates/rind-str0m)
[![Documentation](https://img.shields.io/docsrs/rind-str0m)](https://docs.rs/rind-str0m/)

This crate provides a `CryptoProvider` for [str0m](https://github.com/algesten/str0m), backed by [rind](https://github.com/moq-dev/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).

Build str0m with `default-features = false`, since its default features compile aws-lc-rs.
Then hand the provider to each connection:

```rust
use std::sync::Arc;
use std::time::Instant;

let provider = rind_str0m::default_provider();
let rtc = str0m::Rtc::builder()
    .set_crypto_provider(Arc::new(provider))
    .build(Instant::now());
```

Or install it for the process with `str0m::crypto::CryptoProvider::install_process_default`.

`default_provider()` and `dimpl_crypto_provider()` match [str0m-aws-lc-rs](https://crates.io/crates/str0m-aws-lc-rs), so swapping one for the other changes no other code.
`dimpl_crypto_provider()` returns the dimpl provider DTLS runs on, for building your own `dimpl::Config`.

rind cannot back, through [rind-dimpl](https://github.com/moq-dev/rind/tree/main/rind-dimpl):

- dimpl's PSK suite, AES-128-CCM-8.

Where it behaves differently:

- Where str0m-aws-lc-rs lets dimpl panic on an empty DTLS certificate or a private key it cannot load, this returns an error.
- DTLS puts ChaCha20-Poly1305 first on a CPU where rind runs AES without CPU instructions, for speed, as rind-dimpl does.
- A PEM private key whose preamble starts with `0` is refused, as rind-dimpl refuses it: that byte is the tag every DER key starts with, and a DER key's later bytes are secret, so rind never searches them for PEM.

A generated certificate's private key is returned in dimpl's `DtlsCertificate`, whose plain `Vec<u8>` str0m owns and nothing wipes when it is dropped.

License: Apache-2.0 OR ISC OR MIT-0
