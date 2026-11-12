# rind_cryptography

The [`cryptography`](https://pub.dev/packages/cryptography) package's
`Cryptography` interface on [rind](https://pub.dev/packages/rind). An app
opts in with one line, and its existing `Sha256()`, `AesGcm`, `Ed25519`,
and other calls run on rind:

```dart
import 'package:rind_cryptography/rind_cryptography.dart';

void main() {
  RindCryptography.enable();
}
```

`Cryptography` is one factory the app installs. It does not compose a second
backend at setup, so an algorithm rind does not implement throws
`UnsupportedError` instead of falling through to the pure-Dart code.

| What runs on rind | What throws `UnsupportedError` |
|---|---|
| SHA-1, SHA-256, SHA-384, SHA-512 | SHA-224, BLAKE2b, BLAKE2s |
| HMAC, HKDF, and PBKDF2 over those hashes | Argon2id |
| AES-GCM with a 12-byte nonce, AES-CBC, AES-CTR | Poly1305 on its own, HChaCha20 |
| ChaCha20 and ChaCha20-Poly1305, XChaCha20-Poly1305 | ChaCha20 with a 24-byte nonce and no Poly1305 |
| X25519, ECDH and ECDSA on P-256, P-384, and P-521 | ECDSA with a hash other than the curve's |
| Ed25519 | |
| RSA PKCS#1 v1.5 and RSA-PSS, exponent 65537, 2048 to 8192 bits | other RSA sizes and exponents |

ECDSA signatures are fixed-length `r || s`. ECDSA signs P-256 with SHA-256,
P-384 with SHA-384, and P-521 with SHA-512. ECDH returns that many leading
bytes of the shared x coordinate. AES-CBC and AES-CTR are unauthenticated
on their own; the MAC is the one the `cryptography` cipher was given, over
the ciphertext. X25519 private keys are clamped when they are extracted, as
`cryptography`'s own backend does.

`withRandom` feeds cipher nonces and X25519 and Ed25519 seeds. ECDSA, ECDH,
and RSA key generation use rind's generator.

The tests run `cryptography_test` for the algorithms above, RFC 4231's HMAC
vectors for SHA-256, SHA-384, and SHA-512, and check that the others throw.
`cryptography_test`'s AES-GCM 1 000-cycle examples start from a 16-byte nonce,
which rind refuses, so those examples are not part of this run. Its HMAC file
also vectors SHA-224, which rind does not implement.
