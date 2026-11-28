# rind-digest

[RustCrypto](https://github.com/RustCrypto)'s [`digest`](https://crates.io/crates/digest) 0.11 traits on [rind](https://github.com/kixel-ai/rind), so code generic over `Digest` and `Mac` runs on rind by naming a different type. Each type is a thin wrapper that calls rind: this crate adds no primitive and no encoding, and handles a secret only by passing it to rind. Each module keeps the path, names, and re-exports of the RustCrypto crate it stands in for: `sha2` (`Sha256`, `Sha384`, `Sha512`, `Sha512_256`, and `digest::{self, Digest}`), `sha3` (`Sha3_256`, `Sha3_384`, `Sha3_512`, and the same re-exports), and `hmac` (`Hmac` and `HmacReset` over SHA-256, SHA-384 or SHA-512, and `digest::{self, KeyInit, Mac}`), so `use sha2::{Digest, Sha256}` becomes `use rind_digest::sha2::{Digest, Sha256}`. The hashes have their crates' OIDs (the `oid` feature, on by default, as in `sha2`), so `rsa::pkcs1v15::SigningKey<rind_digest::sha2::Sha256>` works, and their `AlgorithmName`s. `tests/upstream.rs` builds those crates' README examples this way.

This crate adapts one upstream, `digest`, and its version begins with that crate's breaking part: a new major of `digest` is a new major of `rind-digest`, and of no other adapter.

```toml
[dependencies]
rind-digest = "0.11"
```

```rust
use rind_digest::sha2::{Digest, Sha256};

assert_eq!(Sha256::digest(b"abc").len(), 32);
```

## What rind cannot back

- `Sha224`, `Sha512_224`, `Sha3_224`, the `Keccak*` hashes, and the SHAKE, cSHAKE and TurboSHAKE extendable-output functions: rind has no public SHA-224, SHA-512/224, Keccak or SHAKE.
- `block_api` (each crate's block-level cores, such as `Sha256VarCore`) and `SerializableState`: the wrappers are whole hashes over rind's context, which exposes neither its blocks nor its state.
- `zeroize`'s `ZeroizeOnDrop` on the hashes: rind leaves digest contexts unwiped, since they hold no secret.
- `SimpleHmac`, `SimpleHmacReset`, `EagerHash`, and `Hmac` over any other hash, such as SHA-3 or SHA-512/256: rind keys HMAC with SHA-256, SHA-384 and SHA-512 only, so `Hmac<D>` takes the sealed `HmacHash` bound instead of `EagerHash`.
