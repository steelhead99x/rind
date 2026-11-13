## Unreleased

- The unauthenticated ciphers: AES-CBC (`AesCbcEncryptingKey`,
  `AesCbcDecryptingKey`, `CbcIv`), AES-CTR (`AesCtr`), and ChaCha20
  (`ChaCha20`), sized by `CipherAlgorithm`.

## 0.1.0

- rind's AEADs, digests, HMAC, HKDF, PBKDF2, key agreement, signatures,
  ML-KEM-768, and RSA-OAEP, through a prebuilt library the build hook
  downloads and checks against its pinned SHA-256, or built from source with
  the `build_from_source` user-define.
