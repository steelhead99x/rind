# rind-signature

[RustCrypto](https://github.com/RustCrypto)'s [`signature`](https://crates.io/crates/signature) 3 traits on [rind](https://github.com/kixel-ai/rind), so code generic over `Signer` and `Verifier` runs on rind by naming a different type. Each type is a thin wrapper that calls rind: this crate adds no primitive and no encoding, and handles a secret only by passing it to rind. A signing key is only rind's key pair, whose drop wipes its whole value, public key included, so the wrapper keeps no copy of either. Each module keeps the names, paths, and re-exports of the RustCrypto crate it stands in for: `ed25519` (`ed25519_dalek`'s `SigningKey`, `VerifyingKey`, `Signature`, `Signer`, `Verifier`, `SignatureError` and length constants), `p256::ecdsa`, `p384::ecdsa` and `p521::ecdsa` (with `signature::{self, Error}`), `ml_dsa` (with its `signature` and key-trait re-exports), and `rsa::{pkcs1v15, pss}`, so `use p256::ecdsa::{signature::Signer, SigningKey}` becomes `use rind_signature::p256::ecdsa::{signature::Signer, SigningKey}`. `tests/upstream.rs` builds those crates' examples with only the crate in each path swapped.

This crate adapts one upstream, `signature`, and its version begins with that crate's breaking part: a new major of `signature` is a new major of `rind-signature`, and of no other adapter.

RSA names its hashes with [rind-digest](../rind-digest/README.md)'s `sha2` types, as `rsa` names them with `sha2`'s, so `rind_signature::rsa::pkcs1v15::SigningKey<rind_digest::sha2::Sha256>` is the type to swap in for `rsa::pkcs1v15::SigningKey<sha2::Sha256>`.

```toml
[dependencies]
rind-signature = "3"
```

```rust
use rind_signature::ed25519::{Signer, SigningKey, Verifier};

let key = SigningKey::from_bytes(&[7; 32]);
let signature = key.sign(b"message");
key.verifying_key().verify(b"message", &signature).unwrap();
```

## What rind cannot back

- Ed25519: `Ed25519ph`, context signatures and `Context`, so `DigestSigner` and `DigestVerifier`: rind signs pure Ed25519 only. `SigningKey::as_bytes`, since rind's key pair lends no view of its seed (`to_bytes` copies it out). `verify` is as strict as `ed25519_dalek`'s `verify_strict`, which is not offered separately, nor are `is_weak`, `verify_batch`, the `hazmat` module and the Montgomery and Edwards point conversions, for which rind has no public curve arithmetic: a small-order public key is refused where `ed25519_dalek`'s `verify` accepts it. `pkcs8` and serde (rind has its own PKCS#8 on its key types).
- ECDSA: the generic `ecdsa::SigningKey<C>` and `ecdsa::VerifyingKey<C>` (each curve has its own type under the module path its RustCrypto crate uses), and the curve crates' other modules and types, such as `p256::PublicKey`, `p256::SecretKey` and `p256::ecdh`: rind has no public curve arithmetic. RFC 6979 deterministic signing: rind signs with a random nonce, so a signature differs from RustCrypto's for the same key and message, and verifies under it. `RandomizedSigner`, `Generate` and other signing from a caller's random source, which rind's ECDSA does not take. `Prehash`, `DigestSigner` and `RecoveryId` with recoverable signing and verification, `SignatureWithOid`, PKCS#8 and PEM, and serde. A signing key takes a scalar of exactly the field's length; RustCrypto's `from_slice` also left-pads a shorter one. A verifying key takes a SEC1 point compressed or not, as RustCrypto's does, decompressing it through rind's key agreement public key.
- ML-DSA: the deterministic `Signer` (rind signs hedged, with the empty context, so a signature differs from RustCrypto's and verifies under it), `ExpandedSigningKey` with the expanded key format and its context, `mu` and deterministic signing, `DigestSigner`, `RandomizedSigner` (rind draws its own randomness), and `pkcs8`.
- RSA: a modulus under 2048 bits or over 8192 bits (rind refuses it, `rsa` accepts it), and so `VerifyingKey::new`, `new_with_auto_salt_len` and `From<PublicKey>`, which cannot fail in `rsa` and here are `try_new`, `try_new_with_auto_salt_len` and `TryFrom<PublicKey>`; `RandomizedSigner` and PSS with a salt of another length than the hash's; `Generate`, encryption, PKCS#8 and serde. A signing key is made from `rsa`'s `PrivateKey` by reading its private integers at their full width, and the CRT values `rsa` precomputed, into rind's component loader through buffers wiped on drop, so the import runs in constant time and frees nothing unwiped; a key whose precomputed values were cleared is refused until `precompute` restores them. rind's key pair is the only copy this crate keeps.
