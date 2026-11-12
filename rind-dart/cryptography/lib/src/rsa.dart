// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'cryptography.dart';

/// Generates an RSA key pair of [modulusLength] bits with the public exponent
/// 65537, the only one rind uses.
RsaKeyPairData _rsaGenerate(int modulusLength, List<int> publicExponent) {
  final size = switch (modulusLength) {
    2048 => rind.RsaKeySize.rsa2048,
    3072 => rind.RsaKeySize.rsa3072,
    4096 => rind.RsaKeySize.rsa4096,
    6144 => rind.RsaKeySize.rsa6144,
    8192 => rind.RsaKeySize.rsa8192,
    _ => throw _unsupported('$modulusLength-bit RSA key generation'),
  };
  final exponent = publicExponent.skipWhile((b) => b == 0).toList();
  if (!_equal(exponent, const [1, 0, 1])) {
    throw _unsupported('RSA public exponents other than 65537');
  }
  return _rsaPairFromPkcs8(rind.RsaKeyPair.generate(size).toPkcs8());
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
Future<({rind.RsaKeyPair key, RsaPublicKey publicKey})> _rsaKey(
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
  final key = _keyArgument(
    'keyPair',
    data,
    () => rind.RsaKeyPair.fromPkcs1(pkcs1),
  );
  return (key: key, publicKey: data.publicKey);
}

/// Whether [signature] verifies [message] under its RSA public key with
/// [algorithm].
bool _rsaVerify(
  rind.RsaVerificationAlgorithm algorithm,
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
    () => rind.PublicKey.fromComponents(
      algorithm,
      n: _bytes(publicKey.n),
      e: _bytes(publicKey.e),
    ),
  );
  return _verifies(key, message, signature.bytes);
}

final class _RsaPkcs1 extends RsaSsaPkcs1v15 {
  _RsaPkcs1(this.hashAlgorithm)
    : _signing = switch (hashAlgorithm) {
        Sha256() => rind.RsaSigningAlgorithm.pkcs1Sha256,
        Sha384() => rind.RsaSigningAlgorithm.pkcs1Sha384,
        Sha512() => rind.RsaSigningAlgorithm.pkcs1Sha512,
        _ => null,
      },
      _verification = switch (hashAlgorithm) {
        Sha1() => rind.rsaPkcs1Sha1,
        Sha256() => rind.VerificationAlgorithm.rsaPkcs1Sha256,
        Sha384() => rind.VerificationAlgorithm.rsaPkcs1Sha384,
        Sha512() => rind.VerificationAlgorithm.rsaPkcs1Sha512,
        _ => throw _unsupported('RSA PKCS#1 v1.5 with $hashAlgorithm'),
      },
      super.constructor();

  @override
  final HashAlgorithm hashAlgorithm;

  /// Null for SHA-1, which rind only verifies.
  final rind.RsaSigningAlgorithm? _signing;
  final rind.RsaVerificationAlgorithm _verification;

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

/// RSA-PSS, which rind signs only with a salt as long as the hash, and
/// verifies with any salt when [nonceLengthInBytes] is another length.
final class _RsaPss extends RsaPss {
  _RsaPss(this.hashAlgorithm, this.nonceLengthInBytes)
    : _signing = switch (hashAlgorithm) {
        Sha256() => rind.RsaSigningAlgorithm.pssSha256,
        Sha384() => rind.RsaSigningAlgorithm.pssSha384,
        Sha512() => rind.RsaSigningAlgorithm.pssSha512,
        _ => throw _unsupported('RSA-PSS with $hashAlgorithm'),
      },
      _verification = nonceLengthInBytes == hashAlgorithm.hashLengthInBytes
          ? switch (hashAlgorithm) {
              Sha256() => rind.VerificationAlgorithm.rsaPssSha256,
              Sha384() => rind.VerificationAlgorithm.rsaPssSha384,
              _ => rind.VerificationAlgorithm.rsaPssSha512,
            }
          : switch (hashAlgorithm) {
              Sha256() => rind.VerificationAlgorithm.rsaPssSha256AnySalt,
              Sha384() => rind.VerificationAlgorithm.rsaPssSha384AnySalt,
              _ => rind.VerificationAlgorithm.rsaPssSha512AnySalt,
            },
      super.constructor() {
    if (nonceLengthInBytes < 0) {
      throw RangeError.range(nonceLengthInBytes, 0, null, 'nonceLengthInBytes');
    }
  }

  @override
  final HashAlgorithm hashAlgorithm;

  @override
  final int nonceLengthInBytes;

  final rind.RsaSigningAlgorithm _signing;
  final rind.RsaVerificationAlgorithm _verification;

  @override
  Future<RsaKeyPair> newKeyPair({
    int modulusLength = RsaPss.defaultModulusLength,
    List<int> publicExponent = RsaPss.defaultPublicExponent,
  }) async => _rsaGenerate(modulusLength, publicExponent);

  @override
  Future<Signature> sign(List<int> message, {required KeyPair keyPair}) async {
    if (nonceLengthInBytes != hashAlgorithm.hashLengthInBytes) {
      throw _unsupported(
        'RSA-PSS signing with a $nonceLengthInBytes-byte salt; it salts with '
        'as many bytes as the hash, ${hashAlgorithm.hashLengthInBytes}',
      );
    }
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
