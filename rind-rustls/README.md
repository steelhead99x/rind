<h1 align="center">rind-rustls</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-rustls)](https://crates.io/crates/rind-rustls)
[![Documentation](https://img.shields.io/docsrs/rind-rustls)](https://docs.rs/rind-rustls/)

This crate provides an integration between [rustls](https://github.com/rustls/rustls) and [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).

Turn off rustls's default features, which compile aws-lc-rs, and add this crate:

```toml
[dependencies]
rustls = { version = "0.23", default-features = false, features = ["std", "tls12", "logging"] }
rind-rustls = "0.23"
```

Use it like:

```rust
rind_rustls::default_provider().install_default().unwrap();
```

And then use rustls as normal.

Its API is rustls's `crypto::aws_lc_rs` provider's, item for item, so
replacing `rustls::crypto::aws_lc_rs` with `rind_rustls` changes no other code.
A dependency that turns on rustls's `aws_lc_rs` or `ring` feature still
compiles that library; [MIGRATING.md](https://github.com/kixel-ai/rind/blob/main/MIGRATING.md#crates-with-their-own-crypto-backend)
says which features of each such crate avoid it.

## What rind cannot back

Nothing: it backs every item of rustls's `crypto::aws_lc_rs` provider.

## Behaves differently


- `default_provider()` puts ChaCha20-Poly1305 first on a CPU where rind runs
  AES without CPU instructions, for speed.
- `DEFAULT_CIPHER_SUITES` and `ALL_CIPHER_SUITES` list AES-128-GCM before
  AES-256-GCM, for speed.
- `hpke`'s NIST suites refuse a compressed public key, which RFC 9180 does
  not define, where upstream seals to one a message no recipient opens.
- `hpke`'s NIST suites refuse an X9.62 hybrid point (`0x06`/`0x07`) as a
  public or encapsulated key, as rind does everywhere; upstream takes one.
- `Ticketer` seals tickets with XChaCha20-Poly1305, where upstream's uses
  RFC 5077's AES-256-CBC and HMAC-SHA256.
- `sign::any_supported_type` refuses a PKCS#8 private key with bytes after its
  structure, where upstream's takes it.

## FIPS

The `fips` feature runs part of the provider in [rind-fips](../rind-fips/README.md)'s module. It builds only for glibc Linux on little-endian x86_64 and aarch64, and fails to compile elsewhere rather than offer a `fips` provider that runs nothing in a module. rind-fips is unpublished, so a published rind-rustls cannot carry this dependency until it is.

What runs in the module with `fips`: SHA-2, HMAC, and HKDF, so TLS 1.3's key schedule; TLS 1.3 and QUIC AES-128-GCM and AES-256-GCM record protection, with QUIC's AES header protection; ECDH on P-256 and P-384; ML-KEM-768 and ML-KEM-1024; and random bytes. Each reports `fips() == true`. X25519, which no module approves, stays in rind with `fips()` false, and counts only as the classical half of `X25519MLKEM768`, as in rustls's aws-lc-rs provider.

With `fips`, `default_provider()` offers only the suites and groups that report `fips()`: the TLS 1.3 AES-GCM suites, and `X25519MLKEM768`, `secp256r1`, and `secp384r1`. It drops ChaCha20-Poly1305 and bare X25519, as rustls's aws-lc-rs provider does under its `fips`.

What does not yet run in the module, so `CryptoProvider::fips()` is `false`:

- Signature verification, and the signing keys `KeyProvider` loads.
- The TLS 1.2 suites, which report `fips() == false` and are not offered by default: the module seals only TLS 1.3 records. They stay available when named, running outside the module, as the ChaCha20-Poly1305 suites do. rustls's aws-lc-rs provider counts its TLS 1.2 AES-GCM suites as FIPS.
- ECDH on P-521, and the hybrid and ML-KEM groups beyond the defaults, which are in the module but not in the default list.

## WebAssembly

rind-rustls builds for `wasm32-wasip2`, where CI runs its tests under
wasmtime, and for `wasm32-unknown-unknown`, the browser. rustls's aws-lc-rs
provider builds for neither, and its ring one needs a C compiler targeting
wasm. In the browser, turn on rind's JavaScript random source, `getrandom = {
version = "0.4", features = ["wasm_js"] }`, and give rustls a clock, as any
provider needs, such as `rustls-pki-types = { version = "1", features =
["web"] }`. rind's constant-time checks do not cover wasm; [PLATFORMS.md](https://github.com/kixel-ai/rind/blob/main/PLATFORMS.md)
says why.

License: Apache-2.0 OR ISC OR MIT-0
