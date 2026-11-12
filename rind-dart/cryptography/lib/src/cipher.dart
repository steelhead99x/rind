// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'cryptography.dart';

/// Seals and opens with a rind AEAD of 12-byte nonces and 16-byte tags.
mixin _Aead on Cipher {
  rind.AeadAlgorithm get _algorithm;

  Future<rind.AeadKey> _key(SecretKey secretKey) async {
    final bytes = await secretKey.extractBytes();
    if (bytes.length != secretKeyLength) {
      throw ArgumentError(
        '$this expects a secret key with $secretKeyLength bytes, got '
        '${bytes.length} bytes',
      );
    }
    return rind.AeadKey(_algorithm, _bytes(bytes));
  }

  static rind.Nonce _nonce(List<int> nonce) {
    if (nonce.length != 12) {
      throw ArgumentError.value(nonce, 'nonce', 'Must be 12 bytes');
    }
    return rind.Nonce.assumeUniqueForKey(_bytes(nonce));
  }

  Future<SecretBox> _seal(
    List<int> clearText,
    SecretKey secretKey,
    List<int>? nonce,
    List<int> aad,
  ) async {
    final key = await _key(secretKey);
    nonce ??= newNonce();
    final sealed = key.seal(_nonce(nonce), _bytes(clearText), aad: _bytes(aad));
    return _split(sealed, nonce);
  }

  Future<List<int>> _open(
    SecretBox secretBox,
    SecretKey secretKey,
    List<int> aad,
  ) async {
    final key = await _key(secretKey);
    final nonce = _nonce(secretBox.nonce);
    return _authenticated(
      () => key.open(nonce, _joined(secretBox), aad: _bytes(aad)),
    );
  }
}

/// A seal, the ciphertext followed by its 16-byte tag, as a [SecretBox].
SecretBox _split(Uint8List sealed, List<int> nonce) {
  final length = sealed.length - 16;
  return SecretBox(
    Uint8List.sublistView(sealed, 0, length),
    nonce: nonce,
    mac: Mac(Uint8List.sublistView(sealed, length)),
  );
}

/// [secretBox]'s ciphertext followed by its tag, as rind opens it.
///
/// A tag of another length never authenticates, even when the ciphertext's
/// last bytes would complete it.
Uint8List _joined(SecretBox secretBox) {
  final cipherText = secretBox.cipherText;
  final mac = secretBox.mac.bytes;
  if (mac.length != 16) throw SecretBoxAuthenticationError();
  return Uint8List(cipherText.length + mac.length)
    ..setAll(0, cipherText)
    ..setAll(cipherText.length, mac);
}

/// Runs [open], turning rind's refusal into the package's
/// [SecretBoxAuthenticationError].
Uint8List _authenticated(Uint8List Function() open) {
  try {
    return open();
  } on rind.RindException catch (e) {
    if (e.error == rind.RindError.decryptFailed) {
      throw SecretBoxAuthenticationError();
    }
    rethrow;
  }
}

void _checkKeyStreamIndex(int keyStreamIndex) {
  if (keyStreamIndex != 0) {
    throw UnsupportedError('rind has no AEAD key stream index');
  }
}

final class _AesGcm extends AesGcm with _Aead {
  _AesGcm(this.secretKeyLength, this.nonceLength, Random? random)
    : _algorithm = switch (secretKeyLength) {
        16 => rind.AeadAlgorithm.aes128Gcm,
        24 => rind.AeadAlgorithm.aes192Gcm,
        32 => rind.AeadAlgorithm.aes256Gcm,
        _ => throw ArgumentError.value(
          secretKeyLength,
          'secretKeyLength',
          'Must be 16, 24, or 32',
        ),
      },
      super.constructor(random: random) {
    if (nonceLength != 12) {
      throw _unsupported('AES-GCM with $nonceLength-byte nonces');
    }
  }

  @override
  final int secretKeyLength;

  @override
  final int nonceLength;

  @override
  final rind.AeadAlgorithm _algorithm;

  @override
  Future<SecretBox> encrypt(
    List<int> clearText, {
    required SecretKey secretKey,
    List<int>? nonce,
    List<int> aad = const <int>[],
    Uint8List? possibleBuffer,
  }) => _seal(clearText, secretKey, nonce, aad);

  @override
  Future<List<int>> decrypt(
    SecretBox secretBox, {
    required SecretKey secretKey,
    List<int> aad = const <int>[],
    Uint8List? possibleBuffer,
  }) => _open(secretBox, secretKey, aad);
}

final class _Chacha20Poly1305 extends Chacha20 with _Aead {
  _Chacha20Poly1305(Random? random) : super.constructor(random: random);

  @override
  MacAlgorithm get macAlgorithm => const DartChacha20Poly1305AeadMacAlgorithm();

  @override
  rind.AeadAlgorithm get _algorithm => rind.AeadAlgorithm.chacha20Poly1305;

  @override
  Future<SecretBox> encrypt(
    List<int> clearText, {
    required SecretKey secretKey,
    List<int>? nonce,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    _checkKeyStreamIndex(keyStreamIndex);
    return _seal(clearText, secretKey, nonce, aad);
  }

  @override
  Future<List<int>> decrypt(
    SecretBox secretBox, {
    required SecretKey secretKey,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    _checkKeyStreamIndex(keyStreamIndex);
    return _open(secretBox, secretKey, aad);
  }
}

/// XChaCha20-Poly1305, whose nonces rind always picks itself: a nonce the
/// caller passes to [encrypt] throws [UnsupportedError].
final class _Xchacha20Poly1305 extends Xchacha20 {
  _Xchacha20Poly1305(Random? random) : super.constructor(random: random);

  @override
  MacAlgorithm get macAlgorithm => DartXchacha20.poly1305AeadMacAlgorithm;

  Future<rind.RandomizedNonceKey> _key(SecretKey secretKey) async {
    final bytes = await secretKey.extractBytes();
    if (bytes.length != secretKeyLength) {
      throw ArgumentError(
        '$this expects a secret key with $secretKeyLength bytes, got '
        '${bytes.length} bytes',
      );
    }
    return rind.RandomizedNonceKey(_bytes(bytes));
  }

  @override
  Future<SecretBox> encrypt(
    List<int> clearText, {
    required SecretKey secretKey,
    List<int>? nonce,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    _checkKeyStreamIndex(keyStreamIndex);
    if (nonce != null) {
      throw UnsupportedError(
        'rind picks XChaCha20-Poly1305 nonces itself; pass no nonce',
      );
    }
    final key = await _key(secretKey);
    final sealed = key.seal(_bytes(clearText), aad: _bytes(aad));
    return _split(sealed.sealed, sealed.nonce);
  }

  @override
  Future<List<int>> decrypt(
    SecretBox secretBox, {
    required SecretKey secretKey,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    _checkKeyStreamIndex(keyStreamIndex);
    final key = await _key(secretKey);
    final nonce = secretBox.nonce;
    if (nonce.length != 24) {
      throw ArgumentError.value(nonce, 'nonce', 'Must be 24 bytes');
    }
    return _authenticated(
      () => key.open(_bytes(nonce), _joined(secretBox), aad: _bytes(aad)),
    );
  }
}
