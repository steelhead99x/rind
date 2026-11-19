# rind-digest

[RustCrypto](https://github.com/RustCrypto)'s [`digest`](https://crates.io/crates/digest) 0.11 traits on [rind](https://github.com/kixel-ai/rind), so code generic over `Digest` and `Mac` runs on rind by naming a different type. Each type is a thin wrapper that calls rind: this crate adds no primitive and no encoding, and handles a secret only by passing it to rind. Each module mirrors the RustCrypto crate it stands in for: `sha2` (`Sha256`, `Sha384`, `Sha512`, `Sha512_256`), `sha3` (`Sha3_256`, `Sha3_384`, `Sha3_512`) and `hmac::Hmac` over SHA-256, SHA-384 or SHA-512.

This crate adapts one upstream, `digest`, and its version begins with that crate's breaking part: a new major of `digest` is a new major of `rind-digest`, and of no other adapter.

```toml
[dependencies]
rind-digest = "0.11"
```

```rust
use digest::Digest;
use rind_digest::sha2::Sha256;

assert_eq!(Sha256::digest(b"abc").len(), 32);
```

## What rind cannot back

- `Digest` for SHA-224, SHA-1 and MD5 (SHA-1 and MD5 are in `rind::digest::legacy`, not offered here), the SHA-3 SHAKE and cSHAKE extendable-output functions, KangarooTwelve, BLAKE2 and BLAKE3.
- HMAC over SHA-3 or SHA-512/256: rind keys HMAC with SHA-256, SHA-384 and SHA-512 only.
- `digest`'s `core_api` block-level traits (`CoreWrapper` and friends): the wrappers are whole hashes.
