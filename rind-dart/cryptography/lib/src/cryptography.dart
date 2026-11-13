// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// One library, so the algorithm classes stay private to it.
library;

import 'dart:math';
import 'dart:typed_data';

import 'package:cryptography/cryptography.dart';
import 'package:cryptography/dart.dart';
import 'package:rind/legacy.dart' as rind;
import 'package:rind/rind.dart' as rind;

part 'cipher.dart';
part 'der.dart';
part 'hash.dart';
part 'kdf.dart';
part 'key_exchange.dart';
part 'rsa.dart';
part 'signature.dart';

/// The `cryptography` package's [Cryptography] on rind.
///
/// Make it the default with `Cryptography.instance = RindCryptography()`, and
/// constructors such as `AesGcm.with256bits()` and `Ed25519()` run on rind.
/// An algorithm or parameter rind lacks throws [UnsupportedError] where it is
/// constructed, never falling back to the package's Dart implementation.
final class RindCryptography extends Cryptography {
  /// Makes the backend; [random], if given, picks the nonces, secret keys,
  /// and X25519 and Ed25519 key seeds the package generates, as it does for
  /// `DartCryptography`.
  RindCryptography({Random? random}) : _random = random;

  final Random? _random;

  @override
  AesCbc aesCbc({
    required MacAlgorithm macAlgorithm,
    PaddingAlgorithm paddingAlgorithm = PaddingAlgorithm.pkcs7,
    int secretKeyLength = 32,
  }) => _AesCbc(macAlgorithm, paddingAlgorithm, secretKeyLength, _random);

  @override
  AesCtr aesCtr({
    required MacAlgorithm macAlgorithm,
    int secretKeyLength = 32,
    int counterBits = 64,
  }) => _AesCtr(macAlgorithm, secretKeyLength, counterBits, _random);

  @override
  AesGcm aesGcm({int secretKeyLength = 32, int nonceLength = 12}) =>
      _AesGcm(secretKeyLength, nonceLength, _random);

  @override
  Argon2id argon2id({
    required int memory,
    required int parallelism,
    required int iterations,
    required int hashLength,
  }) => throw _unsupported('Argon2id');

  @override
  Blake2b blake2b({int hashLengthInBytes = 64}) =>
      throw _unsupported('BLAKE2b');

  @override
  Blake2s blake2s({int hashLengthInBytes = 32}) =>
      throw _unsupported('BLAKE2s');

  @override
  Chacha20 chacha20({required MacAlgorithm macAlgorithm}) =>
      macAlgorithm is DartChacha20Poly1305AeadMacAlgorithm
      ? _Chacha20Poly1305(_random)
      : _Chacha20(macAlgorithm, _random);

  @override
  Chacha20 chacha20Poly1305Aead() => _Chacha20Poly1305(_random);

  @override
  Ecdh ecdhP256({required int length}) => _Ecdh(_p256, length);

  @override
  Ecdh ecdhP384({required int length}) => _Ecdh(_p384, length);

  @override
  Ecdh ecdhP521({required int length}) => _Ecdh(_p521, length);

  @override
  Ecdsa ecdsaP256(HashAlgorithm hashAlgorithm) => _Ecdsa(_p256, hashAlgorithm);

  @override
  Ecdsa ecdsaP384(HashAlgorithm hashAlgorithm) => _Ecdsa(_p384, hashAlgorithm);

  @override
  Ecdsa ecdsaP521(HashAlgorithm hashAlgorithm) => _Ecdsa(_p521, hashAlgorithm);

  @override
  Ed25519 ed25519() => _Ed25519(_random);

  @override
  Hchacha20 hchacha20() => throw _unsupported('HChaCha20');

  @override
  Hkdf hkdf({required Hmac hmac, required int outputLength}) =>
      _Hkdf(hmac, outputLength);

  @override
  Hmac hmac(HashAlgorithm hashAlgorithm) => _Hmac(hashAlgorithm);

  @override
  Pbkdf2 pbkdf2({
    required MacAlgorithm macAlgorithm,
    required int iterations,
    required int bits,
  }) => _Pbkdf2(macAlgorithm, iterations, bits);

  @override
  Poly1305 poly1305() => throw _unsupported('Poly1305');

  @override
  RsaPss rsaPss(
    HashAlgorithm hashAlgorithm, {
    required int nonceLengthInBytes,
  }) => _RsaPss(hashAlgorithm, nonceLengthInBytes);

  @override
  RsaSsaPkcs1v15 rsaSsaPkcs1v15(HashAlgorithm hashAlgorithm) =>
      _RsaPkcs1(hashAlgorithm);

  @override
  Sha1 sha1() => const _Sha1();

  @override
  Sha224 sha224() => throw _unsupported('SHA-224');

  @override
  Sha256 sha256() => const _Sha256();

  @override
  Sha384 sha384() => const _Sha384();

  @override
  Sha512 sha512() => const _Sha512();

  @override
  RindCryptography withRandom(Random random) =>
      RindCryptography(random: random);

  @override
  X25519 x25519() => _X25519(_random);

  @override
  Xchacha20 xchacha20({required MacAlgorithm macAlgorithm}) =>
      throw _unsupported('XChaCha20 without Poly1305');

  @override
  Xchacha20 xchacha20Poly1305Aead() => _Xchacha20Poly1305(_random);

  @override
  String toString() => 'RindCryptography()';
}

UnsupportedError _unsupported(String what) =>
    UnsupportedError('rind has no $what');

/// [bytes] as a [Uint8List], copied only when it is another kind of list.
Uint8List _bytes(List<int> bytes) =>
    bytes is Uint8List ? bytes : Uint8List.fromList(bytes);

/// Whether [a] and [b] hold the same bytes, for public values only.
bool _equal(List<int> a, List<int> b) {
  if (a.length != b.length) return false;
  for (var i = 0; i < a.length; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}

/// Runs [f], turning rind's refusal of a key into the [ArgumentError] the
/// package throws for an invalid one.
T _keyArgument<T>(String name, Object? value, T Function() f) {
  try {
    return f();
  } on rind.RindException catch (e) {
    if (e.error == rind.RindError.keyRejected) {
      throw ArgumentError.value(value, name, e.reason ?? 'rejected by rind');
    }
    rethrow;
  }
}
