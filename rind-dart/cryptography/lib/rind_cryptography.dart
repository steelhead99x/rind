// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// The [`cryptography`](https://pub.dev/packages/cryptography) package's
/// `Cryptography` interface on [rind](https://pub.dev/packages/rind).
///
/// An app opts in with one line, and the `cryptography` factories
/// (`Sha256()`, `AesGcm.with256bits()`, `Ed25519()`, and the rest) run on
/// rind:
///
/// ```dart
/// import 'package:rind_cryptography/rind_cryptography.dart';
///
/// void main() {
///   RindCryptography.enable();
/// }
/// ```
library;

export 'src/cryptography.dart';
