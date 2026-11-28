# rind-aead

[RustCrypto](https://github.com/RustCrypto)'s [`aead`](https://crates.io/crates/aead) 0.6 traits on [rind](https://github.com/kixel-ai/rind), so code generic over `Aead` and `AeadInOut` runs on rind by naming a different type. Each type is a thin wrapper that calls rind: this crate adds no primitive and no encoding, and handles a secret only by passing it to rind. Each module keeps the path, names, and re-exports of the RustCrypto crate it stands in for: `aes_gcm` (`Aes128Gcm`, `Aes256Gcm`, `Nonce`, `Tag`, and `aead::{self, AeadCore, AeadInOut, Error, Key, KeyInit, KeySizeUser}`) and `chacha20poly1305` (`ChaCha20Poly1305`, `Key`, `Nonce`, `Tag`, and the same re-exports with `consts` for `Key`), with their `alloc`, `getrandom`, `rand_core`, `arrayvec` and `bytes` features, which turn on `aead`'s, so `Key::<Aes256Gcm>::generate()` and `Nonce::generate()` work as in `aes-gcm`. `tests/upstream.rs` builds those crates' examples with only the crate in each path swapped.

This crate adapts one upstream, `aead`, and its version begins with that crate's breaking part: a new major of `aead` is a new major of `rind-aead`, and of no other adapter.

```toml
[dependencies]
rind-aead = "0.6"
```

```rust
use rind_aead::chacha20poly1305::{
    ChaCha20Poly1305, Nonce,
    aead::{Aead, Generate, Key, KeyInit},
};

let cipher = ChaCha20Poly1305::new(&Key::<ChaCha20Poly1305>::generate());
let nonce = Nonce::generate(); // unique per message
let sealed = cipher.encrypt(&nonce, b"hello".as_slice()).unwrap();
assert_eq!(cipher.decrypt(&nonce, sealed.as_slice()).unwrap(), b"hello");
```

## What rind cannot back

- `AesGcm` and `ChaChaPoly1305`, the generic types the aliases name, so AES-192-GCM, nonces other than 12 bytes and tags other than 16: rind's AEADs are those three with a 12-byte nonce and a 16-byte tag. Each of `Aes128Gcm`, `Aes256Gcm` and `ChaCha20Poly1305` is a type of its own here.
- `XChaCha20Poly1305` and its `XNonce`: rind offers XChaCha20-Poly1305 only with a nonce it draws itself. `ChaCha8Poly1305`, `ChaCha12Poly1305`, `XChaCha8Poly1305` and `XChaCha12Poly1305` (the `reduced-round` feature), and the `aes` block cipher re-export: rind has no reduced-round ChaCha and no raw AES block API.
- The `zeroize` feature's `ZeroizeOnDrop` marker: rind's keys wipe themselves on drop whatever the features, without it.
- A refused open leaves a cleared buffer, where RustCrypto leaves it unspecified.
