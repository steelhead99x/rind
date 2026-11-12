// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'cryptography.dart';

/// A NIST curve, with the rind algorithms on it.
final class _Curve {
  const _Curve(
    this.type,
    this.length,
    this.agreement,
    this.signing,
    this.verification,
    this.hash,
  );

  final KeyPairType type;

  /// The length of a scalar and of each coordinate, in bytes.
  final int length;

  final rind.AgreementAlgorithm agreement;
  final rind.EcdsaSigningAlgorithm signing;
  final rind.VerificationAlgorithm verification;

  /// Whether [algorithm] is the hash ECDSA uses on this curve, the only one
  /// rind signs with.
  final bool Function(HashAlgorithm algorithm) hash;

  /// [key]'s point, uncompressed, as rind takes it.
  Uint8List point(EcPublicKey key) {
    if (key.type != type) {
      throw ArgumentError.value(key, 'publicKey', 'Should be a $type key');
    }
    if (key.x.length != length || key.y.length != length) {
      throw ArgumentError.value(key, 'publicKey', 'Wrong coordinate length');
    }
    return Uint8List(1 + 2 * length)
      ..[0] = 4
      ..setAll(1, key.x)
      ..setAll(1 + length, key.y);
  }

  /// [data]'s scalar and uncompressed point, after checking it is a key pair
  /// on this curve.
  ({Uint8List d, Uint8List point}) parts(KeyPairData data) {
    if (data is! EcKeyPairData || data.type != type) {
      throw ArgumentError.value(data, 'keyPair', 'Should be a $type key pair');
    }
    final d = data.d;
    if (d.length != length) {
      throw ArgumentError.value(data, 'keyPair', 'Wrong private key length');
    }
    return (d: _bytes(d), point: point(data.publicKey));
  }

  /// The package's key pair for [d] and its uncompressed [point].
  EcKeyPairData pair(Uint8List d, Uint8List point) => EcKeyPairData(
    d: d,
    x: Uint8List.sublistView(point, 1, 1 + length),
    y: Uint8List.sublistView(point, 1 + length),
    type: type,
  );
}

final _p256 = _Curve(
  KeyPairType.p256,
  32,
  rind.AgreementAlgorithm.ecdhP256,
  rind.EcdsaSigningAlgorithm.p256Sha256Fixed,
  rind.VerificationAlgorithm.ecdsaP256Sha256Fixed,
  (h) => h is Sha256,
);

final _p384 = _Curve(
  KeyPairType.p384,
  48,
  rind.AgreementAlgorithm.ecdhP384,
  rind.EcdsaSigningAlgorithm.p384Sha384Fixed,
  rind.VerificationAlgorithm.ecdsaP384Sha384Fixed,
  (h) => h is Sha384,
);

final _p521 = _Curve(
  KeyPairType.p521,
  66,
  rind.AgreementAlgorithm.ecdhP521,
  rind.EcdsaSigningAlgorithm.p521Sha512Fixed,
  rind.VerificationAlgorithm.ecdsaP521Sha512Fixed,
  (h) => h is Sha512,
);

final class _Ecdh extends Ecdh {
  _Ecdh(this._curve, this.length) : super.constructor() {
    // The shared secret is the x coordinate, which the caller may shorten.
    RangeError.checkValueInInterval(length, 1, _curve.length, 'length');
  }

  final _Curve _curve;

  /// The length of the shared secret, in bytes.
  final int length;

  @override
  KeyPairType get keyPairType => _curve.type;

  @override
  Future<EcKeyPair> newKeyPair() async {
    final key = rind.AgreementPrivateKey.generate(_curve.agreement);
    return _curve.pair(key.toScalar(), key.publicKey.bytes);
  }

  @override
  Future<EcKeyPair> newKeyPairFromSeed(List<int> seed) async =>
      throw _unsupported('ECDH key pairs from seeds');

  @override
  Future<SecretKey> sharedSecretKey({
    required KeyPair keyPair,
    required PublicKey remotePublicKey,
  }) async {
    final data = await keyPair.extract();
    final parts = _curve.parts(data);
    final key = _keyArgument(
      'keyPair',
      data,
      () => rind.AgreementPrivateKey.fromScalar(_curve.agreement, parts.d),
    );
    if (!_equal(key.publicKey.bytes, parts.point)) {
      throw ArgumentError.value(
        data,
        'keyPair',
        'The public key does not match the private key',
      );
    }
    if (remotePublicKey is! EcPublicKey) {
      throw ArgumentError.value(
        remotePublicKey,
        'remotePublicKey',
        'Should be an EcPublicKey',
      );
    }
    final peer = _curve.point(remotePublicKey);
    final secret = _keyArgument(
      'remotePublicKey',
      remotePublicKey,
      () => key.agree(peer),
    );
    // The view keeps the whole buffer alive, and destroy() overwrites only
    // the view, so clear the bytes it leaves out now.
    secret.fillRange(length, secret.length, 0);
    return SecretKeyData(
      Uint8List.sublistView(secret, 0, length),
      overwriteWhenDestroyed: true,
    );
  }
}

final class _X25519 extends X25519 {
  _X25519(Random? random) : super.constructor(random: random);

  @override
  Future<SimpleKeyPair> newKeyPairFromSeed(List<int> seed) async {
    final scalar = _clamped(seed);
    final key = rind.AgreementPrivateKey.fromScalar(
      rind.AgreementAlgorithm.x25519,
      scalar,
    );
    return SimpleKeyPairData(
      scalar,
      publicKey: SimplePublicKey(key.publicKey.bytes, type: KeyPairType.x25519),
      type: KeyPairType.x25519,
    );
  }

  /// [seed] clamped as RFC 7748 does, which is the private key the Dart
  /// implementation keeps.
  static Uint8List _clamped(List<int> seed) {
    if (seed.length != 32) {
      throw ArgumentError.value(seed.length, 'seed', 'Must be 32 bytes');
    }
    return Uint8List.fromList(seed)
      ..[0] &= 0xf8
      ..[31] &= 0x7f
      ..[31] |= 0x40;
  }

  @override
  Future<SecretKey> sharedSecretKey({
    required KeyPair keyPair,
    required PublicKey remotePublicKey,
  }) async {
    final data = await keyPair.extract();
    if (data is! SimpleKeyPairData || data.type != KeyPairType.x25519) {
      throw ArgumentError.value(
        data,
        'keyPair',
        'Should be an X25519 key pair',
      );
    }
    if (remotePublicKey is! SimplePublicKey ||
        remotePublicKey.type != KeyPairType.x25519) {
      throw ArgumentError.value(
        remotePublicKey,
        'remotePublicKey',
        'Should be an X25519 public key',
      );
    }
    final key = rind.AgreementPrivateKey.fromScalar(
      rind.AgreementAlgorithm.x25519,
      _clamped(data.bytes),
    );
    final secret = _keyArgument(
      'remotePublicKey',
      remotePublicKey,
      () => key.agree(_bytes(remotePublicKey.bytes)),
    );
    return SecretKeyData(secret, overwriteWhenDestroyed: true);
  }
}
