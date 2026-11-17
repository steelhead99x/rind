# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed

- **Breaking:** pyrind takes the shape rind 0.4 did
  ([#781](https://github.com/kixel-ai/rind/pull/781)). `pyrind.signature` is
  gone: `pyrind.ecdsa`, `pyrind.ed25519`, and `pyrind.rsa` each have a
  `KeyPair` and a `PublicKey`, with their algorithms under each module's
  `sign` and `verify`. A public key's constructor takes the algorithm's own
  encoding, `from_spki` a `SubjectPublicKeyInfo`, and `to_spki` is only on the
  public key. An RSA public key takes PKCS#1, is bound to no algorithm, and
  verifies with any `rsa.verify` algorithm whose modulus floor it meets,
  raising `KeyRejected` at `verify` for a smaller key rather than as it
  loads. A key pair's `public_key()`, and `rsa.DecryptingKey`'s, returns
  the same object each call, made on the first.
- **Breaking:** `rsa.DecryptingKey.to_spki()` is gone, as `to_spki` is only
  on public keys; call `public_key().to_spki()`.
- **Breaking:** `rsa.EncryptingKey(algorithm, der)` takes only PKCS#1; load a
  `SubjectPublicKeyInfo` with `rsa.EncryptingKey.from_spki`.
- **Breaking:** `key_wrap.AesKek`'s four methods are two, each naming a
  `key_wrap.Mode`, `KW` or `KWP`.
- **Breaking:** `rsa.KeySize` equals only itself, never the int it once
  did, so its hash agrees with its equality.
- `agreement.PrivateKey.public_key()` and `kem.DecapsulationKey.public_key()`
  return the same object each call, made on the first.

### Added

- `rsa.PublicKey.modulus_len()`, and hashing for `rsa.KeySize` and
  `key_wrap.Mode`, so they key a dict.

Each name in 0.1 and its replacement:

| pyrind 0.1 | pyrind 0.2 |
|---|---|
| `signature.EcdsaKeyPair` | `ecdsa.KeyPair` |
| `signature.Ed25519KeyPair` | `ed25519.KeyPair` |
| `signature.RsaKeyPair` | `rsa.KeyPair` |
| `signature.EcdsaSigningAlgorithm` | `ecdsa.SigningAlgorithm` |
| `signature.RsaSigningAlgorithm` | `rsa.SigningAlgorithm` |
| `signature.VerificationAlgorithm`, for ECDSA | `ecdsa.VerificationAlgorithm` |
| `signature.VerificationAlgorithm`, for Ed25519 | none: `ed25519.PublicKey` takes no algorithm |
| `signature.RsaVerificationAlgorithm` | `rsa.VerificationAlgorithm` |
| `signature.sign.ECDSA_P256_SHA256_ASN1` and the other `ECDSA_` | `ecdsa.sign.P256_SHA256_ASN1` and so on |
| `signature.sign.RSA_PKCS1_SHA256` and the other `RSA_` | `rsa.sign.PKCS1_SHA256` and so on |
| `signature.verify.ECDSA_P256_SHA256_ASN1` and the other `ECDSA_` | `ecdsa.verify.P256_SHA256_ASN1` and so on |
| `signature.verify.ED25519` | none |
| `signature.verify.RSA_PKCS1_SHA256` and the other `RSA_` | `rsa.verify.PKCS1_SHA256` and so on |
| `signature.verify.legacy.RSA_PKCS1_1024_SHA1` and the others | `rsa.verify.legacy.PKCS1_1024_SHA1` and so on |
| `signature.PublicKey(verify.ECDSA_P256_SHA256_ASN1, point)` | `ecdsa.PublicKey(ecdsa.verify.P256_SHA256_ASN1, point)`, which refuses a `SubjectPublicKeyInfo` |
| `signature.PublicKey(verify.ED25519, key)` | `ed25519.PublicKey(key)`, which refuses a `SubjectPublicKeyInfo` |
| `signature.PublicKey(verify.RSA_PKCS1_SHA256, der)`, PKCS#1 or SPKI | `rsa.PublicKey(der)`, PKCS#1 only, or `rsa.PublicKey.from_spki(der)` |
| `signature.PublicKey.from_spki(algorithm, der)` | `ecdsa.PublicKey.from_spki(algorithm, der)`, `ed25519.PublicKey.from_spki(der)`, or `rsa.PublicKey.from_spki(der)` |
| `signature.PublicKey.from_components(algorithm, n, e)` | `rsa.PublicKey.from_components(n, e)` |
| `public_key.verify(message, signature)`, for RSA | `public_key.verify(algorithm, message, signature)` |
| an RSA key below the algorithm's floor, refused as it loads | refused with `KeyRejected` by `verify` |
| none | `rsa.PublicKey.modulus_len()` |
| `RsaKeyPair.public_key(algorithm)` | `rsa.KeyPair.public_key()` |
| `EcdsaKeyPair.to_spki()`, `Ed25519KeyPair.to_spki()`, `RsaKeyPair.to_spki()` | `key_pair.public_key().to_spki()` |
| `rsa.DecryptingKey.to_spki()` | `decrypting_key.public_key().to_spki()` |
| `rsa.EncryptingKey(algorithm, der)`, PKCS#1 or SPKI | `rsa.EncryptingKey(algorithm, der)`, PKCS#1 only, or `rsa.EncryptingKey.from_spki(algorithm, der)` |
| `key_wrap.AesKek.wrap(key)`, `unwrap(wrapped)` | `wrap_key(key_wrap.Mode.KW, key)`, `unwrap_key(key_wrap.Mode.KW, wrapped)` |
| `key_wrap.AesKek.wrap_padded(key)`, `unwrap_padded(wrapped)` | `wrap_key(key_wrap.Mode.KWP, key)`, `unwrap_key(key_wrap.Mode.KWP, wrapped)` |
| `rsa.KeySize.RSA_2048 == 0` and the like | `int(rsa.KeySize.RSA_2048) == 0` |

## [0.1.2](https://github.com/kixel-ai/rind/compare/rind-python-v0.1.1...rind-python-v0.1.2) - 2026-11-08

### Other

- *(python)* test musl and armv7 wheels ([#496](https://github.com/kixel-ai/rind/pull/496))

## [0.1.1](https://github.com/kixel-ai/rind/compare/rind-python-v0.1.0...rind-python-v0.1.1) - 2026-11-08

### Other

- updated the following local packages: rind

## [0.1.0](https://github.com/kixel-ai/rind/releases/tag/rind-python-v0.1.0) - 2026-11-07

### Added

- *(python)* pyrind, rind's API for Python ([#459](https://github.com/kixel-ai/rind/pull/459))
