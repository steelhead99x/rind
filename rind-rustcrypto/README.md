# rind-rustcrypto

[RustCrypto](https://github.com/RustCrypto)'s traits on [rind](https://github.com/kixel-ai/rind), so code generic over `Digest`, `Mac`, `Aead`, `Signer` and `Verifier`, or the KEM traits, runs on rind by naming a different type. Each type is a thin wrapper that calls rind: this crate adds no primitive and no encoding, and handles a secret only by passing it to rind.

Each module mirrors the RustCrypto crate it stands in for, and each trait crate and version it implements is a cargo feature, so a new major of one trait crate is a new feature here, not a breaking release:

| Feature | Trait crate | Modules |
|---|---|---|
| `digest-0_11` | `digest` 0.11 | `sha2`, `sha3`, `hmac` |
| `aead-0_6` | `aead` 0.6 | `aes_gcm`, `chacha20poly1305` |

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
