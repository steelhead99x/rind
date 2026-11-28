# rind-kem

[RustCrypto](https://github.com/RustCrypto)'s [`kem`](https://crates.io/crates/kem) 0.3 traits on [rind](https://github.com/kixel-ai/rind), so code generic over `Kem`, `Encapsulate` and `Decapsulate` runs on rind by naming a different type. It keeps the names, paths, and re-exports of RustCrypto's [`ml-kem`](https://crates.io/crates/ml-kem) 0.3: `MlKem512`, `MlKem768` and `MlKem1024` in the `ml_kem_512`, `ml_kem_768` and `ml_kem_1024` modules with their aliases, generic `DecapsulationKey` and `EncapsulationKey` with `ml-kem`'s inherent methods, the `DecapsulationKey768`-style aliases, `B32`, `Seed`, `SharedKey`, and the `kem` traits and `array` re-exports, with its `getrandom` and `hazmat` features. `tests/upstream.rs` builds `ml-kem`'s example with only the crate swapped. Each type is a thin wrapper that calls rind: this crate adds no primitive and no encoding.

This crate adapts one upstream, `kem`, and its version begins with that crate's breaking part: a new major of `kem` is a new major of `rind-kem`, and of no other adapter.

```toml
[dependencies]
rind-kem = "0.3"
```

```rust
use rind_kem::{Decapsulate, Encapsulate, Seed, ml_kem_768::DecapsulationKey};

let dk = DecapsulationKey::from_seed(Seed::from([0x42; 64]));
// With the `getrandom` feature; `encapsulate_with_rng` takes any `CryptoRng`.
let (ciphertext, secret) = dk.encapsulation_key().encapsulate();
assert_eq!(dk.decapsulate(&ciphertext), secret);
```

Keys wipe themselves on drop, as rind's do: a decapsulation key is only rind's, whose wipe covers its encapsulation key too. `Generate` draws the 64-byte seed into a stack buffer it leaves unwiped, as rind leaves its stack temporaries, since the key rind makes holds and wipes its own copy, and `Encapsulate` hands its 32 random bytes to rind's `kem::Message`, which zeroes them.

## What rind cannot back

- `ParameterSet`'s `K`, `Eta1`, `Eta2`, `Du` and `Dv`: a set here names rind's algorithm and its encodings' sizes instead, so the `Kem` sizes are plain `typenum` sizes, not `ml-kem`'s arithmetic over those.
- Left out, though rind could back them: `ExpandedDecapsulationKey`, `ExpandedKeyEncoding` and `DecapsulationKey::from_expanded`, the expanded key form `ml-kem` deprecates, and `Clone` and `PartialEq` on `DecapsulationKey`. Keys come from `KeyInit`, `from_seed` or `Generate`, and `KeyExport` and `to_seed` give the seed back.
- The `pkcs8` and `pem` features' encodings (rind has its own on its key types), and the `zeroize` feature's `ZeroizeOnDrop` marker: rind's keys wipe themselves on drop whatever the features, without it.
