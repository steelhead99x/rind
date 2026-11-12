# rind for Dart and Flutter

Fast, misuse-resistant cryptography for Dart and Flutter, through FFI to
[rind](https://github.com/moq-dev/rind), a pure-Rust library: AES-GCM,
ChaCha20-Poly1305, and XChaCha20-Poly1305, SHA-2 and SHA-3, HMAC, HKDF,
PBKDF2, X25519 and ECDH, Ed25519, ECDSA, and RSA signatures, RSA-OAEP, and
ML-KEM-768.

It is 7 to 2800 times faster than pure-Dart cryptography. On an
Intel i7-8700, in microseconds per operation (`dart run
benchmark/compare.dart`):

| Operation | rind | pointycastle | cryptography (Dart) |
|---|---:|---:|---:|
| SHA-256, 1 KiB | 2.1 | 19 | 15 |
| HMAC-SHA256, 64 B | 0.51 | 10 | 9.2 |
| AES-256-GCM seal, 1350 B | 0.85 | 2400 | 176 |
| ChaCha20-Poly1305 seal, 1350 B | 1.4 | 59 | 44 |
| X25519 agree | 21 | | 845 |
| Ed25519 sign | 8.0 | | 2700 |
| Ed25519 verify | 40 | | 4800 |
| ECDSA P-256 sign | 27 | 9900 | |
| ECDSA P-256 verify | 77 | 14000 | |

On a Pixel 10 Pro (Tensor G5, Android 17), with rind 0.1.0 in a
release-mode Flutter 3.50 app (Dart 3.14), the median of five runs, which
spread up to 3x as Android moves the thread between cores:

| Operation | rind | pointycastle | cryptography (Dart) |
|---|---:|---:|---:|
| SHA-256, 1 KiB | 1.6 | 340 | 99 |
| HMAC-SHA256, 64 B | 0.93 | 150 | 38 |
| AES-256-GCM seal, 1350 B | 4.1 | 5300 | 340 |
| ChaCha20-Poly1305 seal, 1350 B | 9.1 | 300 | 300 |
| X25519 agree | 230 | | 1700 |
| Ed25519 sign | 35 | | 8300 |
| Ed25519 verify | 160 | | 11000 |
| ECDSA P-256 sign | 57 | 24000 | |
| ECDSA P-256 verify | 180 | 42000 | |

## Setup

```shell
dart pub add rind
```

The package's build hook downloads rind's prebuilt library for each target the
app builds for from this version's
[GitHub release](https://github.com/moq-dev/rind/releases), and refuses one
whose SHA-256 differs from the one the package pins. It honors the
`HTTPS_PROXY` environment variable.

To build rind from source instead, set this in the app's `pubspec.yaml`:

```yaml
hooks:
  user_defines:
    rind:
      build_from_source: true
```

That needs [Rust](https://rustup.rs) 1.90 or later with the standard library
of each target the app builds for, and for Android the NDK that Flutter's
Android toolchain provides:

```shell
# Android
rustup target add aarch64-linux-android armv7-linux-androideabi x86_64-linux-android
# iOS
rustup target add aarch64-apple-ios aarch64-apple-ios-sim x86_64-apple-ios
```

## Platforms

Android on arm64, armv7, and x86_64; iOS on devices and the simulator;
macOS, Linux, and Windows on arm64 and x86_64; and Linux on armv7. The build
fails for any other target, such as Android's 32-bit x86, rather than falling
back to slower code. There is no web build: rind has no WebAssembly backend.

rind needs NEON on arm64 CPUs, which every Android and Apple device has. On a
CPU missing a feature rind requires, every call throws an `UnsupportedError`
naming it.

## Use

```dart
import 'dart:convert';
import 'dart:typed_data';

import 'package:rind/rind.dart';

void main() {
  final key = Uint8List(32);
  fillRandom(key);

  final aead = AeadKey(AeadAlgorithm.chacha20Poly1305, key);
  // Never reuse a nonce with one key; RandomizedNonceKey picks its own.
  final nonce = Nonce.assumeUniqueForKey(Uint8List(12));
  final sealed = aead.seal(nonce, utf8.encode('hello'));
  print(utf8.decode(aead.open(nonce, sealed)));

  final pair = EcdsaKeyPair.generate(EcdsaSigningAlgorithm.p256Sha256Asn1);
  final signature = pair.sign(utf8.encode('hello'));
  final verifier = PublicKey(
    VerificationAlgorithm.ecdsaP256Sha256Asn1,
    pair.publicKey.bytes,
  );
  verifier.verify(utf8.encode('hello'), signature);
}
```

The API is rind's own: each algorithm is a constant, and each key type has one
role. Failures throw a `RindException` whose `error` says what failed, as
rind's `Error` does, and a refused key says why in its `reason`. SHA-1, MD5,
and RSA keys below 2048 bits are in `package:rind/legacy.dart`.

Keys live in native memory, which Dart frees without wiping: this package
builds rind without its `wipe` feature. To wipe keys, use rind from Rust with
`wipe`.

Generating RSA keys, RSA's private-key operations, and PBKDF2 take
milliseconds to seconds, so call them off the UI isolate, as with
`Isolate.run`.

License: Apache-2.0 OR ISC OR MIT-0
