<h1 align="center">rind-rcgen</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-rcgen)](https://crates.io/crates/rind-rcgen)
[![Documentation](https://img.shields.io/docsrs/rind-rcgen)](https://docs.rs/rind-rcgen/)

This crate provides rcgen's `KeyPair` for [rcgen](https://github.com/rustls/rcgen), backed by [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
It generates and loads ECDSA P-256 and P-384, Ed25519, and RSA keys, as
rcgen's `aws_lc_rs` backend does.

Build rcgen with `default-features = false` so it compiles no other crypto backend:

```toml
[dependencies]
rcgen = { version = "0.14", default-features = false }
rind-rcgen = "0.14"
```

Then use `rind_rcgen::KeyPair` where rcgen's `crypto` feature would give `rcgen::KeyPair`.
Without that feature, rcgen needs each certificate's serial number set explicitly,
and leaves its key identifiers empty unless `key_identifier_method` is set.

```rust
use rind_rcgen::KeyPair;

let key = KeyPair::generate()?;

let mut params = rcgen::CertificateParams::new(["localhost".to_string()])?;
params.serial_number = Some(rcgen::SerialNumber::from(1));

let cert = params.self_signed(&key)?;
let key = key.serialize_der();
```

## What rind cannot back

`KeyPair` behaves as rcgen's on its `aws_lc_rs` backend, which loads more
than its default `ring` one: RSA keys generate, at 2048 bits from
`generate_for` or a chosen size from `generate_rsa_for`, SEC1 ECDSA and
PKCS#1 RSA keys load, and so do PKCS#8 v2 documents. As in AWS-LC, an RSA or
ECDSA one whose outer `publicKey` field is present is refused, and an Ed25519
one is checked against it. A key loaded from SEC1 or
PKCS#1 serializes to DER as given, not as PKCS#8, and `serialize_pem` labels
it `PRIVATE KEY` all the same, as rcgen's does. Where it differs:

- An ECDSA key whose curve is given by explicit parameters rather than its
  name, or whose public point is in X9.62's hybrid form, fails to load,
  where AWS-LC loads it: rind reads only named curves and compressed or
  uncompressed points.
- No P-521 or ML-DSA keys: rcgen names their algorithms only with its
  `aws_lc_rs` feature, which builds AWS-LC, so a P-521 key fails to load
  with `CouldNotParseKeyPair`.
- `RsaKeySize` is this crate's, for the same reason, with rcgen's variants.
- An unsupported algorithm returns `UnsupportedSignatureAlgorithm` where rcgen panics.
- PEM whose base64 is malformed returns `PemError` with rind's description, not the `base64` crate's.

The `pem` feature, on by default as rcgen's is, adds the PEM methods.
Keys and the key pair's DER copy are wiped on drop.
The `zeroize` feature, as rcgen's, implements `Zeroize` for `KeyPair`, clearing its DER copy.

## WebAssembly

It builds for `wasm32-wasip2` and `wasm32-unknown-unknown`, the browser, where
rind needs its JavaScript random source, `getrandom = { version = "0.4",
features = ["wasm_js"] }`. [PLATFORMS.md](https://github.com/kixel-ai/rind/blob/main/PLATFORMS.md) lists what each adapter's
upstream needs there too, and why rind's constant-time checks do not cover wasm.

License: Apache-2.0 OR ISC OR MIT-0
