<h1 align="center">rind-openssl</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">

An [OpenSSL 3 provider](https://docs.openssl.org/3.5/man7/provider/) backed by [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
OpenSSL loads it through its configuration file, so whatever links OpenSSL 3, such as Node.js, Python's `cryptography`, Ruby, or nginx, signs with Ed25519 and agrees with X25519 through rind, and with ECDSA and ECDH on the NIST curves once `ec = 1` is set, with no change to its code, except where a program signs ECDSA over a digest it made (Python's `cryptography` does, and fails under `ec = 1`: see [the NIST curves](#the-nist-curves)).

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
| ECDSA and ECDH on P-256, P-384, and P-521, with `ec = 1` | key import and generation, signing and verifying through `EVP_DigestSign` and `EVP_DigestVerify`, ECDH, and the TLS 1.3 groups | P-256: 1.9x signing, 1.3-1.4x verifying, 1.2-1.4x ECDH. P-384: 3.8-4.1x, 2.2-2.3x, 1.8-2.1x. P-521: 2.7-3.9x, 1.7-2.3x, 1.4-1.5x |

Measured on an AMD Ryzen 9 9950X against OpenSSL 3.5.9's default provider, under load: with `openssl speed`, with Node.js 24, and with Python's `cryptography`, changing only `OPENSSL_CONF`.
The NIST curves were measured later, on an Intel Core Ultra 9 275HX (24 cores, a laptop, with a load average of 2.7 to 5.1 from other programs) against OpenSSL 3.5.8's default provider, by `cargo test --release -p rind-openssl --test ec -- --ignored --nocapture`, which times each operation through the provider's own tables. The table gives the lowest and highest of rind's rate over the default provider's across three runs; the default provider's own rates moved by up to a quarter between runs, and its P-521 signing the most. `openssl speed -seconds 3 ecdhp256 ecdhp384 ecdhp521` agrees on ECDH: 1.4x, 2.7x, and 1.2x. Node.js 24 (OpenSSL 3.5.9, `--openssl-config`) and Python 3.12's `cryptography` 43 (OpenSSL 3.5.8, `OPENSSL_CONF`) were run on the same host, pinned to one core, three interleaved rounds each. Node: ECDH 1.25x on P-256, 2.0-2.1x on P-384, 1.4x on P-521; signing 1.7x, 3.7-3.9x, 3.2-3.3x; verifying 1.4x, 2.2-2.3x, 1.8-1.9x. Python, which can only run ECDH here (its ECDSA signs over a digest it made and fails under `ec = 1`): P-256 1.13x (median of five rounds pinned to one core; the first of three earlier rounds read 0.91x while the host was loaded, which is why an earlier version of this table said no change); P-384 2.4-2.5x; P-521 1.4-1.6x. A quiet desktop would narrow these ranges; the earlier figures here, from a shared 2.1 GHz Xeon VM against OpenSSL 3.0.13, mostly measured that OpenSSL's slower P-384.

## The NIST curves

They are off unless the provider's section of the configuration says `ec = 1`, because they change what already works: see the differences below.

```ini
[rind_sect]
module = /usr/local/lib/ossl-modules/librind_openssl.so
activate = 1
ec = 1
```

Anything but `1`, `0`, or no `ec` line fails the provider's start with an error naming the value.

OpenSSL's own encoders and decoders still read and write the keys, which move between the two providers as OpenSSL needs them.
OpenSSL's `evp_test` passes on its X25519 and Ed25519 data with this provider loaded and preferred, as [`sh/openssl.sh`](../sh/openssl.sh) runs it. That script also runs its ECDSA and ECDH data with `ec = 1`, less the stanzas rind refuses, which it counts.

## What rind cannot back

- Ed25519ph and Ed25519ctx, asked of the `ED25519` signature algorithm through its `instance` parameter: rind signs only pure Ed25519, and fails these with an `unsupported by rind` error. The separate `ED25519ph` and `ED25519ctx` signature algorithms of OpenSSL 3.4 on stay the default provider's.
- Other curves, such as secp256k1, brainpool, and P-224. OpenSSL gives every curve one `EC` key type, so with `ec = 1` a key of another curve imports, and each use of it then fails with an error saying so, rather than falling back to the default provider, which `?provider=rind` would otherwise do silently.
- ECDSA over a digest the caller made, `EVP_PKEY_sign` and `EVP_PKEY_verify`: rind's ECDSA takes the message. This includes `openssl speed ecdsa` and Python's `cryptography`, which sign that way, and which fail under `ec = 1`. Use `EVP_DigestSign` and `EVP_DigestVerify`.
- ECDSA over SHA-1, SHA-224, or SHA-3, ECDSA signatures other than DER, and the key derivation function of `EVP_PKEY_derive` on ECDH: each fails with an `unsupported by rind` error.
- Everything else, such as X448, Ed448, RSA, ML-KEM, ML-DSA, ciphers, and digests, which stays the default provider's.

## Where it differs from the default provider

- A key given with both halves whose public half is not its private half's fails each signature, exchange, and export with an error saying so, and holds neither half. That includes such a key the default provider made, which moves to rind before each use. Importing it still succeeds: were the move refused, OpenSSL would run the use on the default provider.
- An Ed25519 public key of small order verifies no signature, as rind refuses such keys.
- With `ec = 1`, ECDSA signs with the curve's own digest, SHA-256, SHA-384, and SHA-512 for P-256, P-384, and P-521, and takes no other: a signature with a different digest fails rather than changes what it signs. Verifying takes SHA-256, SHA-384, and SHA-512 on each curve.
- With `ec = 1`, the provider hashes the message as OpenSSL gives it, so a message of any length costs a constant amount of memory, and the digest cannot change once the message has begun.
- With `ec = 1`, importing a private key costs a public-key computation, as rind checks the two halves agree.
- It wipes every key it holds, and the key bytes it gives OpenSSL to move a key between providers, once it is done with them, as OpenSSL's own providers do.

License: Apache-2.0 OR ISC OR MIT-0
