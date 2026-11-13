# rind_cryptography

The [`cryptography`](https://pub.dev/packages/cryptography) package's
`Cryptography` on [rind](https://pub.dev/packages/rind), for what
[rind](https://github.com/kixel-ai/rind), a pure-Rust library, covers. One
line moves an app's existing code onto rind's assembly.

Its Dart layer costs part of rind's lead, most on small messages, since each
call loads the key it is given. On an AMD Ryzen 9 9950X, Linux 7.3, Dart
3.13, in microseconds per operation (`dart run benchmark/compare.dart`):

| Operation | rind_cryptography | cryptography (Dart) | rind |
|---|---:|---:|---:|
| SHA-256, 1 KiB | 0.47 | 6.1 | 0.43 |
| HMAC-SHA256, 64 B | 1.1 | 2.4 | 0.10 |
| AES-256-GCM seal, 1350 B | 1.7 | 31 | 0.17 |
| ChaCha20-Poly1305 seal, 1350 B | 2.2 | 17 | 0.57 |
| X25519 agree | 17 | 375 | 13 |
| Ed25519 sign, 64 B | 11 | 1340 | 4.0 |
| Ed25519 verify, 64 B | 20 | 1460 | 17 |
| ECDSA P-256 sign, 64 B | 12 | | 6.7 |
| ECDSA P-256 verify, 64 B | 30 | | 25 |

## Use

```shell
dart pub add rind_cryptography
```

rind's [setup](https://github.com/kixel-ai/rind/tree/main/rind-dart#setup)
and [platforms](https://github.com/kixel-ai/rind/tree/main/rind-dart#platforms)
apply: Android, iOS, macOS, Linux, and Windows, and no web.

Make rind the default before the app's first cryptography call, and the
package's constructors return rind's algorithms:

```dart
import 'package:cryptography/cryptography.dart';
import 'package:rind_cryptography/rind_cryptography.dart';

Future<void> main() async {
  Cryptography.instance = RindCryptography();

  final algorithm = AesGcm.with256bits();
  final secretKey = await algorithm.newSecretKey();
  final box = await algorithm.encrypt([1, 2, 3], secretKey: secretKey);
  print(await algorithm.decrypt(box, secretKey: secretKey));
}
```

## Coverage

| Algorithm | What works |
|---|---|
| `Sha1`, `Sha256`, `Sha384`, `Sha512` | all of it |
| `Hmac` | over SHA-1, SHA-256, SHA-384, SHA-512 |
| `Hkdf`, `Pbkdf2` | with those HMACs |
| `AesGcm` | 128, 192, and 256-bit keys, 12-byte nonces |
| `Chacha20.poly1305Aead`, `Xchacha20.poly1305Aead` | all of it, but XChaCha20-Poly1305 picks its own nonces |
| `X25519`, `Ed25519` | all of it |
| `Ecdh` | P-256, P-384, P-521 |
| `Ecdsa` | P-256 with SHA-256, P-384 with SHA-384, P-521 with SHA-512 |
| `RsaSsaPkcs1v15`, `RsaPss` | 2048 to 8192 bits, e = 65537, SHA-256, SHA-384, SHA-512 |

Everything else throws `UnsupportedError` where it is constructed, never
falling back to the package's Dart implementation: AES-CBC, AES-CTR,
ChaCha20 and XChaCha20 without Poly1305, Poly1305 and HChaCha20 alone,
BLAKE2, Argon2id, and SHA-224, as does an unsupported pairing such as
`Ecdsa.p256(Sha512())`. `toSync()` still returns the package's Dart
implementation, as it does under every backend.

Within what works, it differs from the Dart implementation and WebCrypto in
these ways:

- `AesGcm` takes only 12-byte nonces.
- `Xchacha20.poly1305Aead().encrypt` picks a random nonce itself and
  throws `UnsupportedError` when given one, as does `encryptStream`, which
  always passes one. It decrypts under any nonce.
- `Ecdh` and `Ecdsa` generate key pairs but make none from seeds.
- `RsaPss` signs only with a salt as long as the hash, so its default 16-byte
  salt signs nothing; with another salt length, it verifies any salt.
  `RsaSsaPkcs1v15` verifies SHA-1 signatures but makes none.
- RSA keys under 2048 bits, private keys without `dp`, `dq`, and `qi`, and
  key pairs whose parts disagree throw `ArgumentError`, as do public keys
  rind refuses, such as an X25519 key of small order or a point off its
  curve.
- Each operation is one native call, which never yields to the event loop:
  seal large messages off the UI isolate, as with `Isolate.run`.

## Tested against

Its own tests check each algorithm against the package's Dart
implementation where it has one, and against rind's API. The `cryptography`
package's own tests run on it too (`dart run tool/upstream_test.dart`),
skipping those [compat/cryptography.txt](compat/cryptography.txt) lists by
reason, most often algorithms rind lacks and class names in `toString()`.

## License

rind_cryptography is Apache-2.0, ISC, or MIT-0, at your option
([LICENSE](LICENSE)).
