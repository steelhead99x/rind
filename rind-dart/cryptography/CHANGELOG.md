## Unreleased

- Depends on rind 0.2.0, whose signature keys it moves to; its own API is
  unchanged.

## 0.1.0

- The cryptography package's `Cryptography` on rind 0.1.1: SHA-1 and
  SHA-2, HMAC, HKDF, PBKDF2, AES-GCM, ChaCha20-Poly1305 and
  XChaCha20-Poly1305, `AesCbc`, `AesCtr`, and `Chacha20` with a MAC such as
  `Hmac`, X25519, Ed25519, ECDH, ECDSA, and RSA signatures. `AesGcm` takes
  nonces of any length but zero, and `RsaPss` signs and verifies with its
  `nonceLengthInBytes`, its default 16 bytes included.
