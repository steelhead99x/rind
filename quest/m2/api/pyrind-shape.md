# [M] pyrind takes rind 0.4's shape

## Goal

pyrind's own API, which its README calls rind's misuse-resistant API, takes the shape rind 0.4 did in [kixel-ai/rind#781](https://github.com/kixel-ai/rind/pull/781): `pyrind.ecdsa`, `pyrind.ed25519`, and `pyrind.rsa` each have `KeyPair` and `PublicKey`, in place of `pyrind.signature`'s `EcdsaKeyPair`, `Ed25519KeyPair`, `RsaKeyPair`, and one `PublicKey` for every algorithm. pyrind-cryptography keeps pyca/cryptography's API exactly.

## Plan

Found by kixel-ai/rind#781, which changed only pyrind's calls into rind and kept its Python API (`rind-python/python/pyrind/signature/__init__.pyi`, `key_wrap.pyi`, `rsa/__init__.pyi`).

- Signatures, as rind's modules are: a public key's constructor takes the algorithm's own encoding, `from_spki` a `SubjectPublicKeyInfo`, and `to_spki` lives only on the public key. An RSA public key takes PKCS#1, is bound to no algorithm, and verifies with any `pyrind.rsa` verification algorithm whose modulus floor it meets, refusing a smaller key at `verify`; it has `modulus_len()`. `RsaKeyPair.public_key(algorithm)` becomes `rsa.KeyPair.public_key()`. A key pair's `public_key()` returns the same key object each call.
- The rest of #781 that pyrind exposes: `rsa.EncryptingKey(algorithm, der)`, which takes PKCS#1 or a `SubjectPublicKeyInfo` today, takes PKCS#1, with `EncryptingKey.from_spki`, and `key_wrap.AesKek`'s four methods become `wrap_key(mode, key)` and `unwrap_key(mode, wrapped)` with a `key_wrap.Mode` of `KW` or `KWP`.
- pyrind has no ML-DSA, VRF, OPRF, or SPAKE2+ today, so nothing there moves.
- It is a breaking change for pyrind alone, which is versioned apart from rind: release it as pyrind's next minor version (0.2.0 from 0.1.x), with a CHANGELOG table from each old name to its new one, as MIGRATING.md has for rind.
- Stubs, docs, `tests/`, and `bench/` move with it, and pyrind-cryptography's internals move to the new calls wherever they use pyrind's Python API; its own tests and pyca/cryptography's upstream suite still pass unchanged.
