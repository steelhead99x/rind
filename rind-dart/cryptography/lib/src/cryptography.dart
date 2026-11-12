// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import 'dart:math';

import 'package:cryptography/cryptography.dart';

import 'backend.dart';

/// [Cryptography] implemented with rind.
///
/// [enable] installs it as [Cryptography.instance], which is the one line an
/// app needs. Algorithms rind does not implement (BLAKE2, Argon2, SHA-224,
/// Poly1305 on its own, HChaCha20, and ChaCha20 with a 24-byte nonce) throw
/// [UnsupportedError]. The `Cryptography` interface does not compose backends
/// when it is installed: one instance answers every factory.
class RindCryptography extends Cryptography {
  /// A rind backend. [random] is used for cipher nonces and for X25519 and
  /// Ed25519 seeds. ECDSA, ECDH, and RSA key generation use rind's own
  /// generator, which rejects scalars outside the curve order.
  const RindCryptography({Random? random}) : _random = random;

  /// Installs rind as [Cryptography.instance].
  static void enable() {
    Cryptography.instance = const RindCryptography();
  }

  final Random? _random;

  @override
  AesCbc aesCbc({
    required MacAlgorithm macAlgorithm,
    PaddingAlgorithm paddingAlgorithm = PaddingAlgorithm.pkcs7,
    int secretKeyLength = 32,
  }) {
    return RindAesCbc(
      macAlgorithm: macAlgorithm,
      paddingAlgorithm: paddingAlgorithm,
      secretKeyLength: secretKeyLength,
      random: _random,
    );
  }

  @override
  AesCtr aesCtr({
    required MacAlgorithm macAlgorithm,
    int secretKeyLength = 32,
    int counterBits = 64,
  }) {
    return RindAesCtr(
      macAlgorithm: macAlgorithm,
      secretKeyLength: secretKeyLength,
      counterBits: counterBits,
      random: _random,
    );
  }

  @override
  AesGcm aesGcm({int secretKeyLength = 32, int nonceLength = 12}) {
    if (nonceLength != 12) {
      throw UnsupportedError(
        'rind implements AES-GCM only with 12-byte nonces',
      );
    }
    return RindAesGcm(secretKeyLength: secretKeyLength, random: _random);
  }

  @override
  Argon2id argon2id({
    required int memory,
    required int parallelism,
    required int iterations,
    required int hashLength,
  }) {
    throw UnsupportedError('Argon2id is not implemented by rind');
  }

  @override
  Blake2b blake2b({int hashLengthInBytes = 64}) {
    throw UnsupportedError('BLAKE2b is not implemented by rind');
  }

  @override
  Blake2s blake2s({int hashLengthInBytes = 32}) {
    throw UnsupportedError('BLAKE2s is not implemented by rind');
  }

  @override
  Chacha20 chacha20({required MacAlgorithm macAlgorithm}) {
    return RindChacha20(macAlgorithm: macAlgorithm, random: _random);
  }

  @override
  Chacha20 chacha20Poly1305Aead() {
    return RindChacha20.poly1305Aead(random: _random);
  }

  @override
  Ecdh ecdhP256({required int length}) => RindEcdh.p256(length);

  @override
  Ecdh ecdhP384({required int length}) => RindEcdh.p384(length);

  @override
  Ecdh ecdhP521({required int length}) => RindEcdh.p521(length);

  @override
  Ecdsa ecdsaP256(HashAlgorithm hashAlgorithm) {
    return RindEcdsa.p256(hashAlgorithm);
  }

  @override
  Ecdsa ecdsaP384(HashAlgorithm hashAlgorithm) {
    return RindEcdsa.p384(hashAlgorithm);
  }

  @override
  Ecdsa ecdsaP521(HashAlgorithm hashAlgorithm) {
    return RindEcdsa.p521(hashAlgorithm);
  }

  @override
  Ed25519 ed25519() => RindEd25519(random: _random);

  @override
  Hchacha20 hchacha20() {
    throw UnsupportedError('HChaCha20 is not implemented by rind');
  }

  @override
  Hkdf hkdf({required Hmac hmac, required int outputLength}) {
    return RindHkdf(hmac: hmac, outputLength: outputLength);
  }

  @override
  Hmac hmac(HashAlgorithm hashAlgorithm) => RindHmac(hashAlgorithm);

  @override
  Pbkdf2 pbkdf2({
    required MacAlgorithm macAlgorithm,
    required int iterations,
    required int bits,
  }) {
    return RindPbkdf2(
      macAlgorithm: macAlgorithm,
      iterations: iterations,
      bits: bits,
    );
  }

  @override
  Poly1305 poly1305() {
    throw UnsupportedError('Poly1305 on its own is not implemented by rind');
  }

  @override
  RsaPss rsaPss(
    HashAlgorithm hashAlgorithm, {
    required int nonceLengthInBytes,
  }) {
    return RindRsaPss(hashAlgorithm, nonceLengthInBytes: nonceLengthInBytes);
  }

  @override
  RsaSsaPkcs1v15 rsaSsaPkcs1v15(HashAlgorithm hashAlgorithm) {
    return RindRsaPkcs1(hashAlgorithm);
  }

  @override
  Sha1 sha1() => const RindSha1();

  @override
  Sha224 sha224() {
    throw UnsupportedError('SHA-224 is not implemented by rind');
  }

  @override
  Sha256 sha256() => const RindSha256();

  @override
  Sha384 sha384() => const RindSha384();

  @override
  Sha512 sha512() => const RindSha512();

  @override
  RindCryptography withRandom(Random random) =>
      RindCryptography(random: random);

  @override
  X25519 x25519() => RindX25519(random: _random);

  @override
  Xchacha20 xchacha20({required MacAlgorithm macAlgorithm}) {
    throw UnsupportedError(
      'ChaCha20 with a 24-byte nonce is not implemented by rind; '
      'Xchacha20.poly1305Aead is',
    );
  }

  @override
  Xchacha20 xchacha20Poly1305Aead() =>
      RindXchacha20.poly1305Aead(random: _random);
}
