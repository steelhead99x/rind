// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'cryptography.dart';

final class _Hkdf extends Hkdf {
  _Hkdf(this.hmac, this.outputLength)
    : _algorithm = _hkdfOf(hmac.hashAlgorithm),
      super.constructor() {
    // HKDF's counter is one byte, so it expands at most 255 blocks.
    final max = 255 * hmac.hashAlgorithm.hashLengthInBytes;
    RangeError.checkValueInInterval(outputLength, 1, max, 'outputLength');
  }

  @override
  final Hmac hmac;

  @override
  final int outputLength;

  final rind.HkdfAlgorithm _algorithm;

  static rind.HkdfAlgorithm _hkdfOf(HashAlgorithm algorithm) =>
      switch (algorithm) {
        Sha1() => rind.hkdfSha1,
        Sha256() => rind.HkdfAlgorithm.sha256,
        Sha384() => rind.HkdfAlgorithm.sha384,
        Sha512() => rind.HkdfAlgorithm.sha512,
        _ => throw _unsupported('HKDF over $algorithm'),
      };

  @override
  Future<SecretKeyData> deriveKey({
    required SecretKey secretKey,
    List<int> nonce = const <int>[],
    List<int> info = const <int>[],
  }) async {
    final prk = rind.HkdfSalt(
      _algorithm,
      _bytes(nonce),
    ).extract(_bytes(await secretKey.extractBytes()));
    return SecretKeyData(
      prk.expand([_bytes(info)], outputLength),
      overwriteWhenDestroyed: true,
    );
  }
}

final class _Pbkdf2 extends Pbkdf2 {
  _Pbkdf2(this.macAlgorithm, this.iterations, this.bits)
    : _algorithm = _pbkdf2Of(macAlgorithm),
      super.constructor() {
    RangeError.checkValueInInterval(iterations, 1, 0xffffffff, 'iterations');
    if (bits < 1) throw RangeError.range(bits, 1, null, 'bits');
  }

  @override
  final MacAlgorithm macAlgorithm;

  @override
  final int iterations;

  @override
  final int bits;

  final rind.Pbkdf2Algorithm _algorithm;

  static rind.Pbkdf2Algorithm _pbkdf2Of(MacAlgorithm algorithm) {
    if (algorithm is! Hmac) throw _unsupported('PBKDF2 over $algorithm');
    return switch (algorithm.hashAlgorithm) {
      Sha1() => rind.pbkdf2HmacSha1,
      Sha256() => rind.Pbkdf2Algorithm.hmacSha256,
      Sha384() => rind.Pbkdf2Algorithm.hmacSha384,
      Sha512() => rind.Pbkdf2Algorithm.hmacSha512,
      _ => throw _unsupported('PBKDF2 over $algorithm'),
    };
  }

  @override
  Future<SecretKey> deriveKey({
    required SecretKey secretKey,
    required List<int> nonce,
  }) async {
    final secret = rind.Pbkdf2Secret(
      _algorithm,
      _bytes(await secretKey.extractBytes()),
    );
    // A partial last byte is kept whole, as the Dart implementation does.
    final derived = secret.derive(iterations, _bytes(nonce), (bits + 7) ~/ 8);
    return SecretKeyData(derived, overwriteWhenDestroyed: true);
  }
}
