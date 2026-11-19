# rind-signature

[RustCrypto](https://github.com/RustCrypto)'s [`signature`](https://crates.io/crates/signature) 3 traits on [rind](https://github.com/kixel-ai/rind), so code generic over `Signer` and `Verifier` runs on rind by naming a different type. Each type is a thin wrapper that calls rind: this crate adds no primitive and no encoding, and handles a secret only by passing it to rind. Each module mirrors the RustCrypto crate it stands in for: `ed25519` (`ed25519_dalek`'s `SigningKey` and `VerifyingKey`), `p256::ecdsa`, `p384::ecdsa`, `p521::ecdsa`, `ml_dsa`, and `rsa::{pkcs1v15, pss}`.

This crate adapts one upstream, `signature`, and its version begins with that crate's breaking part: a new major of `signature` is a new major of `rind-signature`, and of no other adapter.

RSA names its hashes with [rind-digest](../rind-digest/README.md)'s `sha2` types, as `rsa` names them with `sha2`'s, so `rind_signature::rsa::pkcs1v15::SigningKey<rind_digest::sha2::Sha256>` is the type to swap in for `rsa::pkcs1v15::SigningKey<sha2::Sha256>`.

```toml
[dependencies]
rind-signature = "3"
```

```rust
use rind_signature::ed25519::SigningKey;
use signature::{Signer, Verifier};

let key = SigningKey::from_bytes(&[7; 32]);
let signature = key.sign(b"message");
key.verifying_key().verify(b"message", &signature).unwrap();
```

## What rind cannot back

- Ed25519: `Ed25519ph` and context signatures (`DigestSigner`), `Generate`, `TryKeyInit`, serde and the PKCS#8 conversions of `ed25519_dalek` (rind has its own PKCS#8 on its key types), and key export as raw bytes. `verify` is as strict as `ed25519_dalek`'s `verify_strict`: a small-order public key is refused where `ed25519_dalek`'s `verify` accepts it.
- ECDSA: the generic `ecdsa::SigningKey<C>` (each curve has its own type under the module path its RustCrypto crate uses), RFC 6979 deterministic signing (rind signs with a random nonce, so a signature differs from RustCrypto's for the same key and message, and verifies under it), `Prehash`, `Digest`, `Randomized` and recoverable signing and verification, `SignatureWithOid`, `Generate`, key export (`to_bytes`), PKCS#8 and PEM, and serde. A signing key takes a scalar of exactly the field's length; RustCrypto's `from_slice` also left-pads a shorter one.
- ML-DSA: the deterministic `Signer` (rind signs hedged, with the empty context), the expanded signing key format, `DigestSigner`, `RandomizedSigner`, signing with a context or from `mu`, `Generate`, `KeyInit` and `KeyExport`, and PKCS#8. A key is made from its 32-byte seed with `SigningKey::from_seed`.
- RSA: a modulus under 2048 bits or over 8192 bits (rind refuses it, `rsa` accepts it), and so `VerifyingKey::new`, `new_with_auto_salt_len` and `From<PublicKey>`, which cannot fail in `rsa` and here are `try_new`, `try_new_with_auto_salt_len` and `TryFrom<PublicKey>`, `RandomizedSigner` and PSS with a salt of another length than the hash's, `Generate`, encryption, PKCS#8 and serde. A signing key is made from `rsa`'s `PrivateKey` through its PKCS#1 encoding, which `rsa` zeroizes when it is dropped; rind's key pair is the only copy this crate keeps.
