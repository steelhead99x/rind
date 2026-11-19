# rind-rustcrypto

[RustCrypto](https://github.com/RustCrypto)'s traits on [rind](https://github.com/kixel-ai/rind), so code generic over `Digest`, `Mac`, `Aead`, `Signer` and `Verifier`, or the KEM traits, runs on rind by naming a different type. Each type is a thin wrapper that calls rind: this crate adds no primitive and no encoding, and handles a secret only by passing it to rind.

Each module mirrors the RustCrypto crate it stands in for, and each trait crate and version it implements is a cargo feature, so a new major of one trait crate is a new feature here, not a breaking release:

| Feature | Trait crate | Modules |
|---|---|---|
| `digest-0_11` | `digest` 0.11 | `sha2`, `sha3`, `hmac` |
| `aead-0_6` | `aead` 0.6 | `aes_gcm`, `chacha20poly1305` |
| `signature-3` | `signature` 3 | `ed25519`, `p256::ecdsa`, `p384::ecdsa`, `p521::ecdsa`, `ml_dsa` |

```toml
[dependencies]
rind-rustcrypto = { version = "0.1", features = ["digest-0_11"] }
```

```rust
use digest::Digest;
use rind_rustcrypto::sha2::Sha256;

assert_eq!(Sha256::digest(b"abc").len(), 32);
```

## What rind cannot back

- `Digest` for SHA-224, SHA-1 and MD5 (SHA-1 and MD5 are in `rind::digest::legacy`, not offered here), the SHA-3 SHAKE and cSHAKE extendable-output functions, KangarooTwelve, BLAKE2 and BLAKE3.
- HMAC over SHA-3 or SHA-512/256: rind keys HMAC with SHA-256, SHA-384 and SHA-512 only.
- `digest`'s `core_api` block-level traits (`CoreWrapper` and friends): the wrappers are whole hashes.
- `Aead` for AES-192-GCM (`aes_gcm` has it only as `AesGcm<Aes192, U12>`), for nonces other than 12 bytes and tags other than 16, for XChaCha20-Poly1305 with a caller-chosen nonce (rind offers it only with a random one), and for AES-GCM-SIV, AES-CCM, AES-OCB, ChaCha8 and ChaCha12.
- A refused open leaves a cleared buffer, where RustCrypto leaves it unspecified.
- Ed25519: `Ed25519ph` and context signatures (`DigestSigner`), `Generate`, `TryKeyInit`, serde and the PKCS#8 conversions of `ed25519_dalek` (rind has its own PKCS#8 on its key types), and key export as raw bytes. `verify` is as strict as `ed25519_dalek`'s `verify_strict`: a small-order public key is refused where `ed25519_dalek`'s `verify` accepts it.
- ECDSA: the generic `ecdsa::SigningKey<C>` (each curve has its own type under the module path its RustCrypto crate uses), RFC 6979 deterministic signing (rind signs with a random nonce, so a signature differs from RustCrypto's for the same key and message, and verifies under it), `Prehash`, `Digest`, `Randomized` and recoverable signing and verification, `SignatureWithOid`, `Generate`, key export (`to_bytes`), PKCS#8 and PEM, and serde. A signing key takes a scalar of exactly the field's length; RustCrypto's `from_slice` also left-pads a shorter one.
- ML-DSA: the deterministic `Signer` (rind signs hedged, with the empty context), the expanded signing key format, `DigestSigner`, `RandomizedSigner`, signing with a context or from `mu`, `Generate`, `KeyInit` and `KeyExport`, and PKCS#8. A key is made from its 32-byte seed with `SigningKey::from_seed`.
