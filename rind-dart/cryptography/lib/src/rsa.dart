// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'cryptography.dart';

/// Generates an RSA key pair of [modulusLength] bits with the public exponent
/// 65537, the only one rind uses.
RsaKeyPairData _rsaGenerate(int modulusLength, List<int> publicExponent) {
  final size = switch (modulusLength) {
    2048 => rsa.KeySize.rsa2048,
    3072 => rsa.KeySize.rsa3072,
    4096 => rsa.KeySize.rsa4096,
    6144 => rsa.KeySize.rsa6144,
    8192 => rsa.KeySize.rsa8192,
    _ => throw _unsupported('$modulusLength-bit RSA key generation'),
  };
  final exponent = publicExponent.skipWhile((b) => b == 0).toList();
  if (!_equal(exponent, const [1, 0, 1])) {
    throw _unsupported('RSA public exponents other than 65537');
  }
  return _rsaPairFromPkcs8(rsa.KeyPair.generate(size).toPkcs8());
}

/// The package's key pair for rind's PKCS#8 export of one.
RsaKeyPairData _rsaPairFromPkcs8(Uint8List der) {
  final info = _DerReader(_DerReader(der).read(_derSequence));
  info
    ..unsigned()
    ..read(_derSequence);
  final key = _DerReader(
    _DerReader(info.read(_derOctetString)).read(_derSequence),
  )..unsigned();
  return RsaKeyPairData(
    n: key.unsigned(),
    e: key.unsigned(),
    d: key.unsigned(),
    p: key.unsigned(),
    q: key.unsigned(),
    dp: key.unsigned(),
    dq: key.unsigned(),
    qi: key.unsigned(),
  );
}

/// The rind key pair for the package's [keyPair].
Future<({rsa.KeyPair key, RsaPublicKey publicKey})> _rsaKey(
  KeyPair keyPair,
) async {
  final data = await keyPair.extract();
  if (data is! RsaKeyPairData) {
    throw ArgumentError.value(data, 'keyPair', 'Should be an RSA key pair');
  }
  final dp = data.dp, dq = data.dq, qi = data.qi;
  if (dp == null || dq == null || qi == null) {
    // Computing them would take variable time on the private key.
    throw ArgumentError.value(data, 'keyPair', 'Needs dp, dq, and qi');
  }
  final pkcs1 = _derSequenceOf([
    _derUnsigned(const [0]),
    for (final value in [data.n, data.e, data.d, data.p, data.q, dp, dq, qi])
      _derUnsigned(value),
  ]);
  final key = _keyArgument('keyPair', data, () => rsa.KeyPair.fromPkcs1(pkcs1));
  return (key: key, publicKey: data.publicKey);
}

/// Whether [signature] verifies [message] under its RSA public key with
/// [algorithm].
bool _rsaVerify(
  rsa.VerificationAlgorithm algorithm,
  List<int> message,
  Signature signature,
) {
  final publicKey = signature.publicKey;
  if (publicKey is! RsaPublicKey) {
    throw ArgumentError.value(
      publicKey,
      'signature.publicKey',
      'Should be an RsaPublicKey',
    );
  }
  final key = _keyArgument(
    'signature.publicKey',
    publicKey,
    () => rsa.PublicKey.fromComponents(
      n: _bytes(publicKey.n),
      e: _bytes(publicKey.e),
    ),
  );
  // rind refuses a modulus below the algorithm's floor as it verifies.
  return _keyArgument(
    'signature.publicKey',
    publicKey,
    () => _verifies(
      () => key.verify(algorithm, _bytes(message), _bytes(signature.bytes)),
    ),
  );
}

final class _RsaPkcs1 extends RsaSsaPkcs1v15 {
  _RsaPkcs1(this.hashAlgorithm)
    : _signing = switch (hashAlgorithm) {
        Sha256() => rsa.SigningAlgorithm.pkcs1Sha256,
        Sha384() => rsa.SigningAlgorithm.pkcs1Sha384,
        Sha512() => rsa.SigningAlgorithm.pkcs1Sha512,
        _ => null,
      },
      _verification = switch (hashAlgorithm) {
        Sha1() => rsa.pkcs1Sha1,
        Sha256() => rsa.VerificationAlgorithm.pkcs1Sha256,
        Sha384() => rsa.VerificationAlgorithm.pkcs1Sha384,
        Sha512() => rsa.VerificationAlgorithm.pkcs1Sha512,
        _ => throw _unsupported('RSA PKCS#1 v1.5 with $hashAlgorithm'),
      },
      super.constructor();

  @override
  final HashAlgorithm hashAlgorithm;

  /// Null for SHA-1, which rind only verifies.
  final rsa.SigningAlgorithm? _signing;
  final rsa.VerificationAlgorithm _verification;

  @override
  Future<RsaKeyPair> newKeyPair({
    int modulusLength = RsaSsaPkcs1v15.defaultModulusLength,
    List<int> publicExponent = RsaSsaPkcs1v15.defaultPublicExponent,
  }) async => _rsaGenerate(modulusLength, publicExponent);

  @override
  Future<Signature> sign(List<int> message, {required KeyPair keyPair}) async {
    final signing = _signing;
    if (signing == null) {
      throw _unsupported('RSA PKCS#1 v1.5 signing with $hashAlgorithm');
    }
    final pair = await _rsaKey(keyPair);
    return Signature(
      pair.key.sign(signing, _bytes(message)),
      publicKey: pair.publicKey,
    );
  }

  @override
  Future<bool> verify(
    List<int> message, {
    required Signature signature,
  }) async => _rsaVerify(_verification, message, signature);
}

/// RSA-PSS with a salt of [nonceLengthInBytes], which verifies only
/// signatures of that salt length, as WebCrypto's does.
final class _RsaPss extends RsaPss {
  _RsaPss(this.hashAlgorithm, int nonceLengthInBytes)
    : nonceLengthInBytes = RangeError.checkValueInInterval(
        nonceLengthInBytes,
        0,
        65535,
        'nonceLengthInBytes',
      ),
      _signing = switch (hashAlgorithm) {
        Sha256() => rsa.PssSigningAlgorithm.sha256(nonceLengthInBytes),
        Sha384() => rsa.PssSigningAlgorithm.sha384(nonceLengthInBytes),
        Sha512() => rsa.PssSigningAlgorithm.sha512(nonceLengthInBytes),
        _ => throw _unsupported('RSA-PSS with $hashAlgorithm'),
      },
      _verification = switch (hashAlgorithm) {
        Sha256() => rsa.PssVerificationAlgorithm.sha256(nonceLengthInBytes),
        Sha384() => rsa.PssVerificationAlgorithm.sha384(nonceLengthInBytes),
        _ => rsa.PssVerificationAlgorithm.sha512(nonceLengthInBytes),
      },
      super.constructor();

  @override
  final HashAlgorithm hashAlgorithm;

  @override
  final int nonceLengthInBytes;

  final rsa.PssSigningAlgorithm _signing;
  final rsa.VerificationAlgorithm _verification;

  @override
  Future<RsaKeyPair> newKeyPair({
    int modulusLength = RsaPss.defaultModulusLength,
    List<int> publicExponent = RsaPss.defaultPublicExponent,
  }) async => _rsaGenerate(modulusLength, publicExponent);

  @override
  Future<Signature> sign(List<int> message, {required KeyPair keyPair}) async {
    final pair = await _rsaKey(keyPair);
    return Signature(
      pair.key.sign(_signing, _bytes(message)),
      publicKey: pair.publicKey,
    );
  }

  @override
  Future<bool> verify(
    List<int> message, {
    required Signature signature,
  }) async => _rsaVerify(_verification, message, signature);
}
