// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'cryptography.dart';

/// Whether [signature] verifies [message] under [key], so that only a bad
/// signature returns false.
bool _verifies(rind.PublicKey key, List<int> message, List<int> signature) {
  try {
    key.verify(_bytes(message), _bytes(signature));
    return true;
  } on rind.RindException catch (e) {
    if (e.error == rind.RindError.badSignature) return false;
    rethrow;
  }
}

final class _Ed25519 extends Ed25519 {
  _Ed25519(Random? random) : super.constructor(random: random);

  @override
  Future<SimpleKeyPair> newKeyPairFromSeed(List<int> seed) async {
    final key = _key(seed);
    return SimpleKeyPairData(
      Uint8List.fromList(seed),
      publicKey: SimplePublicKey(
        key.publicKey.bytes,
        type: KeyPairType.ed25519,
      ),
      type: KeyPairType.ed25519,
    );
  }

  static rind.Ed25519KeyPair _key(List<int> seed) {
    if (seed.length != 32) {
      throw ArgumentError.value(seed.length, 'seed', 'Must be 32 bytes');
    }
    return rind.Ed25519KeyPair.fromSeed(_bytes(seed));
  }

  @override
  Future<Signature> sign(List<int> message, {required KeyPair keyPair}) async {
    final data = await keyPair.extract();
    if (data is! SimpleKeyPairData || data.type != KeyPairType.ed25519) {
      throw ArgumentError.value(
        data,
        'keyPair',
        'Should be an Ed25519 key pair',
      );
    }
    // The Dart implementation, too, signs with the public key the seed
    // derives rather than the one the key pair holds.
    final key = _key(data.bytes);
    return Signature(
      key.sign(_bytes(message)),
      publicKey: SimplePublicKey(
        key.publicKey.bytes,
        type: KeyPairType.ed25519,
      ),
    );
  }

  @override
  Future<bool> verify(List<int> message, {required Signature signature}) async {
    final publicKey = signature.publicKey;
    if (publicKey is! SimplePublicKey ||
        publicKey.type != KeyPairType.ed25519) {
      throw ArgumentError.value(
        publicKey,
        'signature.publicKey',
        'Should be an Ed25519 public key',
      );
    }
    KeyPairType.ed25519.checkPublicKeyBytesFormat(publicKey.bytes);
    Ed25519.checkSignatureLength(signature.bytes.length);
    final rind.PublicKey key;
    try {
      key = rind.PublicKey(
        rind.VerificationAlgorithm.ed25519,
        _bytes(publicKey.bytes),
      );
    } on rind.RindException catch (e) {
      // The Dart implementation, too, verifies nothing under a public key
      // that is no point, rather than throwing.
      if (e.error == rind.RindError.keyRejected) return false;
      rethrow;
    }
    return _verifies(key, message, signature.bytes);
  }
}

final class _Ecdsa extends Ecdsa {
  _Ecdsa(this._curve, this.hashAlgorithm) : super.constructor() {
    if (!_curve.hash(hashAlgorithm)) {
      throw _unsupported('ECDSA on ${_curve.type} with $hashAlgorithm');
    }
  }

  final _Curve _curve;

  @override
  final HashAlgorithm hashAlgorithm;

  @override
  KeyPairType get keyPairType => _curve.type;

  @override
  Future<EcKeyPair> newKeyPair() async {
    final key = rind.EcdsaKeyPair.generate(_curve.signing);
    return _curve.pair(key.toScalar(), key.publicKey.bytes);
  }

  @override
  Future<EcKeyPair> newKeyPairFromSeed(List<int> seed) async =>
      throw _unsupported('ECDSA key pairs from seeds');

  @override
  Future<Signature> sign(List<int> message, {required KeyPair keyPair}) async {
    final data = await keyPair.extract();
    final parts = _curve.parts(data);
    final key = _keyArgument(
      'keyPair',
      data,
      () => rind.EcdsaKeyPair.fromScalarAndPublicKey(
        _curve.signing,
        parts.d,
        parts.point,
      ),
    );
    return Signature(key.sign(_bytes(message)), publicKey: data.publicKey);
  }

  @override
  Future<bool> verify(List<int> message, {required Signature signature}) async {
    final publicKey = signature.publicKey;
    if (publicKey is! EcPublicKey) {
      throw ArgumentError.value(
        publicKey,
        'signature.publicKey',
        'Should be an EcPublicKey',
      );
    }
    final point = _curve.point(publicKey);
    final key = _keyArgument(
      'signature.publicKey',
      publicKey,
      () => rind.PublicKey(_curve.verification, point),
    );
    return _verifies(key, message, signature.bytes);
  }
}
