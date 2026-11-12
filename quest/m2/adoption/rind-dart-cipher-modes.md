# [M] AES-CBC, AES-CTR, and ChaCha20 in rind-dart and rind_cryptography

## Goal

rind-dart exposes the unauthenticated ciphers rind's `cipher` module has,
AES-CBC, AES-CTR, and ChaCha20, and
[rind_cryptography](/rind-dart/cryptography/README.md) backs the `cryptography`
package's `AesCbc`, `AesCtr`, and `Chacha20` with a MAC on them, rather than
throwing `UnsupportedError`.

## Plan

- Kept (maintainer, 2026-11-12): apps on `cryptography` use AES-CBC with HMAC
  for stored data, and it fails on rind today.
- `cryptography`'s `AesCbc` and `AesCtr` always pair the cipher with a
  `MacAlgorithm`, often HMAC, computed over the ciphertext; rind_cryptography
  composes rind's cipher with its own HMAC the way the package's Dart
  implementation does, and `MacAlgorithm.empty` yields the bare cipher.
- That MAC covers the ciphertext only: the package's `Hmac` ignores its nonce,
  so the IV (nonce) is unauthenticated and changing it changes the first
  plaintext block undetected. Match the package for interoperability, and say
  in the README that integrity-sensitive data needs an AEAD or an envelope
  that authenticates the IV.
- Its tests then drop `aes_cbc_test.dart`, `aes_ctr_test.dart`, and
  `chacha20_test.dart` from
  [compat/cryptography.txt](/rind-dart/cryptography/compat/cryptography.txt).
- It needs a rind-dart release before rind_cryptography can depend on it.
