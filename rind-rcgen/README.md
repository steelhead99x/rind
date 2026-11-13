<h1 align="center">rind-rcgen</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-rcgen)](https://crates.io/crates/rind-rcgen)
[![Documentation](https://img.shields.io/docsrs/rind-rcgen)](https://docs.rs/rind-rcgen/)

This crate provides rcgen's `KeyPair` for [rcgen](https://github.com/rustls/rcgen), backed by [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
It generates and loads ECDSA P-256 and P-384 and Ed25519 keys, and loads RSA keys.

Build rcgen with `default-features = false` so it compiles no other crypto backend,
and use `rind_rcgen::KeyPair` where rcgen's `crypto` feature would give `rcgen::KeyPair`.
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

`KeyPair` behaves as rcgen's on its `ring` backend, which is rcgen's default:

- No P-521 or ML-DSA keys, and no `generate_rsa_for` or `RsaKeySize`, which rcgen offers only with `aws_lc_rs`.
- RSA keys load but do not generate: `generate_for` returns `KeyGenerationUnavailable`.
- Only PKCS#8 private keys load, not SEC1 or PKCS#1.
- An unsupported algorithm returns `UnsupportedSignatureAlgorithm` where rcgen panics.

The `pem` feature, on by default as rcgen's is, adds the PEM methods.
The `wipe` feature wipes keys and the key pair's PKCS#8 copy on drop.
The `zeroize` feature, as rcgen's, implements `Zeroize` for `KeyPair`, clearing its PKCS#8 copy.

License: Apache-2.0 OR ISC OR MIT-0
