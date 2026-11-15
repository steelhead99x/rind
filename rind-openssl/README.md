<h1 align="center">rind-openssl</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">

An [OpenSSL 3 provider](https://docs.openssl.org/3.5/man7/provider/) backed by [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
OpenSSL loads it through its configuration file, so whatever links OpenSSL 3, such as Node.js, Python's `cryptography`, Ruby, or nginx, signs with Ed25519 and agrees with X25519 through rind, with no change to its code.

## Setup

Build the library, which needs only Rust:

```sh
cargo build --release -p rind-openssl
```

This makes `target/release/librind_openssl.so`, or `.dylib` on macOS, which can live anywhere; `openssl version -m` names OpenSSL's own module directory.
Copy [`openssl.cnf`](openssl.cnf), set its `module` line to the library's path, and point `OPENSSL_CONF` at it, or merge its sections into the system's configuration:

```sh
export OPENSSL_CONF=/etc/ssl/rind.cnf
openssl list -providers
```

Check that the list names rind: OpenSSL carries on without a provider it cannot load, and then uses its default provider for everything.
The configuration activates OpenSSL's default provider beside rind, which keeps every algorithm rind does not register, and prefers rind's wherever it has one.
It also sets `nodejs_conf`, since Node.js otherwise reads only its own section of the file.

## Algorithms

| Algorithm | Operations | Against the default provider |
|---|---|---|
| X25519 | key generation, key exchange, the encoded public key TLS sends, and RFC 9180's `DeriveKeyPair` from `dhkem-ikm` | 1.2-1.4x on exchange, 1.6-2.4x on generation and exchange |
| Ed25519 | signing and verifying | 2.6-5.4x on signing, 2.2-4.7x on verifying |

Measured on an AMD Ryzen 9 9950X against OpenSSL 3.5.9's default provider, under load: with `openssl speed`, with Node.js 24, and with Python's `cryptography`, changing only `OPENSSL_CONF`.

OpenSSL's own encoders and decoders still read and write the keys, which move between the two providers as OpenSSL needs them.
OpenSSL's `evp_test` passes on its X25519 and Ed25519 data with this provider loaded and preferred, as [`sh/openssl.sh`](../sh/openssl.sh) runs it.

## What rind cannot back

- Ed25519ph and Ed25519ctx, asked of the `ED25519` signature algorithm through its `instance` parameter: rind signs only pure Ed25519, and fails these with an `unsupported by rind` error. The separate `ED25519ph` and `ED25519ctx` signature algorithms of OpenSSL 3.4 on stay the default provider's.
- ECDSA and ECDH over P-256, P-384, and P-521. OpenSSL gives every curve one `EC` key type, and signs a digest the caller made, which rind's API does not take.
- Everything else, such as X448, Ed448, RSA, ML-KEM, ML-DSA, ciphers, and digests, which stays the default provider's.

## Where it differs from the default provider

- A key given with both halves whose public half is not its private half's fails each signature, exchange, and export with an error saying so, and holds neither half. That includes such a key the default provider made, which moves to rind before each use. Importing it still succeeds: were the move refused, OpenSSL would run the use on the default provider.
- An Ed25519 public key of small order verifies no signature, as rind refuses such keys.
- It wipes every key it holds, and the key bytes it gives OpenSSL to move a key between providers, once it is done with them, as OpenSSL's own providers do.

License: Apache-2.0 OR ISC OR MIT-0
