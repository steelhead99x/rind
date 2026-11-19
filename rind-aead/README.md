# rind-aead

[RustCrypto](https://github.com/RustCrypto)'s [`aead`](https://crates.io/crates/aead) 0.6 traits on [rind](https://github.com/kixel-ai/rind), so code generic over `Aead` and `AeadInOut` runs on rind by naming a different type. Each type is a thin wrapper that calls rind: this crate adds no primitive and no encoding, and handles a secret only by passing it to rind. Each module mirrors the RustCrypto crate it stands in for: `aes_gcm` (`Aes128Gcm`, `Aes256Gcm`) and `chacha20poly1305` (`ChaCha20Poly1305`).

This crate adapts one upstream, `aead`, and its version begins with that crate's breaking part: a new major of `aead` is a new major of `rind-aead`, and of no other adapter.

```toml
[dependencies]
rind-aead = "0.6"
```

```rust
use aead::{Aead, KeyInit, array::Array};
use rind_aead::chacha20poly1305::ChaCha20Poly1305;

let cipher = ChaCha20Poly1305::new_from_slice(&[0x42; 32]).unwrap();
let nonce = Array::try_from([0u8; 12].as_slice()).unwrap();
let sealed = cipher.encrypt(&nonce, b"hello".as_slice()).unwrap();
assert_eq!(cipher.decrypt(&nonce, sealed.as_slice()).unwrap(), b"hello");
```

## What rind cannot back

- `Aead` for AES-192-GCM (`aes_gcm` has it only as `AesGcm<Aes192, U12>`), for nonces other than 12 bytes and tags other than 16, for XChaCha20-Poly1305 with a caller-chosen nonce (rind offers it only with a random one), and for AES-GCM-SIV, AES-CCM, AES-OCB, ChaCha8 and ChaCha12.
- A refused open leaves a cleared buffer, where RustCrypto leaves it unspecified.
