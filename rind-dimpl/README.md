<h1 align="center">rind-dimpl</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-dimpl)](https://crates.io/crates/rind-dimpl)
[![Documentation](https://img.shields.io/docsrs/rind-dimpl)](https://docs.rs/rind-dimpl/)

This crate provides a `CryptoProvider` for [dimpl](https://github.com/algesten/dimpl), backed by [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).

Build dimpl with `default-features = false`, since its default features compile aws-lc-rs:

```toml
[dependencies]
dimpl = { version = "0.9", default-features = false }
rind-dimpl = "0.9"
```

That also removes dimpl's `rcgen` feature, which enables `aws-lc-rs`, and with it `dimpl::certificate::generate_self_signed_certificate()`: bring your own certificate.

Then hand the provider to each config, where dimpl's `crypto::aws_lc_rs::default_provider()` went:

```rust
let config = dimpl::Config::builder()
    .with_crypto_provider(rind_dimpl::default_provider())
    .build()?;
```

Or install it for the process with `dimpl::crypto::CryptoProvider::install_default`.

It negotiates DTLS 1.2 ECDHE-ECDSA and DTLS 1.3 with AES-128-GCM, AES-256-GCM, and ChaCha20-Poly1305, over X25519, P-256, and P-384, and signs with ECDSA P-256 or P-384 keys in PKCS#8 or SEC1, as DER or PEM.
A peer's key share is taken in every form dimpl's aws-lc-rs provider takes: X25519's 32 bytes, or a P-256 or P-384 point uncompressed, compressed, or hybrid with its prefix matching `y`, either bare or in a `SubjectPublicKeyInfo` that names the group's curve or spells out its parameters.

## What rind cannot back

- dimpl's PSK suite, AES-128-CCM-8.

## Behaves differently

- On a CPU where rind runs AES without CPU instructions, it puts ChaCha20-Poly1305 first, for speed.
- A PEM key whose preamble starts with `0` is refused: that byte is the tag every DER key starts with, and a DER key's later bytes are secret, so rind never searches them for PEM.

## WebAssembly

It builds for `wasm32-wasip2` and `wasm32-unknown-unknown`, the browser, where
rind needs its JavaScript random source, `getrandom = { version = "0.4",
features = ["wasm_js"] }`. [PLATFORMS.md](https://github.com/kixel-ai/rind/blob/main/PLATFORMS.md) lists what each adapter's
upstream needs there too, and why rind's constant-time checks do not cover wasm.

License: Apache-2.0 OR ISC OR MIT-0
