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

/// The AES key size of a [secretKeyLength]-byte key.
rind.CipherAlgorithm _aes(int secretKeyLength) => switch (secretKeyLength) {
  16 => rind.CipherAlgorithm.aes128,
  24 => rind.CipherAlgorithm.aes192,
  32 => rind.CipherAlgorithm.aes256,
  _ => throw ArgumentError.value(
    secretKeyLength,
    'secretKeyLength',
    'Must be 16, 24, or 32',
  ),
};

/// [secretKey]'s bytes, once the package's own checks of it and the other
/// parameters pass for [cipher].
Future<Uint8List> _checkedKey(
  Cipher cipher,
  SecretKey secretKey, {
  required int length,
  required List<int> nonce,
  required List<int> aad,
  int keyStreamIndex = 0,
}) async {
  if (keyStreamIndex < 0) {
    throw ArgumentError.value(keyStreamIndex, 'keyStreamIndex');
  }
  final data = await secretKey.extract();
  cipher.checkParameters(
    length: length,
    secretKey: data,
    nonceLength: nonce.length,
    aadLength: aad.length,
    keyStreamIndex: keyStreamIndex,
  );
  return _bytes(data.bytes);
}

/// The package's MAC of [cipherText] as the [SecretBox] it seals.
Future<SecretBox> _boxed(
  Cipher cipher,
  Uint8List cipherText,
  SecretKey secretKey,
  List<int> nonce,
  List<int> aad,
) async {
  final mac = await cipher.macAlgorithm.calculateMac(
    cipherText,
    secretKey: secretKey,
    nonce: nonce,
    aad: aad,
  );
  return SecretBox(cipherText, nonce: nonce, mac: mac);
}

/// [input] XORed with a keystream of [blockLength]-byte blocks from byte
/// [keyStreamIndex], where [apply] XORs the keystream from a block's start.
Uint8List _xorFrom(
  int blockLength,
  int keyStreamIndex,
  List<int> input,
  Uint8List Function(int block, Uint8List data) apply,
) {
  final skip = keyStreamIndex % blockLength;
  final data = Uint8List(skip + input.length)..setAll(skip, input);
  // A copy, not a view: the skipped prefix holds raw keystream.
  return apply(keyStreamIndex ~/ blockLength, data).sublist(skip);
}

/// AES-CBC with the package's MAC over its ciphertext, as `DartAesCbc`
/// composes them.
final class _AesCbc extends AesCbc {
  _AesCbc(
    this.macAlgorithm,
    this.paddingAlgorithm,
    this.secretKeyLength,
    Random? random,
  ) : _algorithm = _aes(secretKeyLength),
      super.constructor(random: random);

  @override
  final MacAlgorithm macAlgorithm;

  @override
  final PaddingAlgorithm paddingAlgorithm;

  @override
  final int secretKeyLength;

  final rind.CipherAlgorithm _algorithm;

  // rind pads with PKCS#7 itself, and checks it in constant time; any other
  // padding is the package's, around rind's unpadded blocks.
  bool get _pkcs7 => identical(paddingAlgorithm, PaddingAlgorithm.pkcs7);

  @override
  Future<SecretBox> encrypt(
    List<int> clearText, {
    required SecretKey secretKey,
    List<int>? nonce,
    List<int> aad = const <int>[],
    Uint8List? possibleBuffer,
  }) async {
    nonce ??= newNonce();
    final key = rind.AesCbcEncryptingKey(
      _algorithm,
      await _checkedKey(
        this,
        secretKey,
        length: clearText.length,
        nonce: nonce,
        // DartAesCbc leaves AAD to the MAC, which MacAlgorithm.empty ignores.
        aad: macAlgorithm.supportsAad ? aad : const <int>[],
      ),
    );
    final iv = rind.CbcIv.assumeUnpredictable(_bytes(nonce));
    if (_pkcs7) {
      return _boxed(
        this,
        key.encrypt(iv, _bytes(clearText)),
        secretKey,
        nonce,
        aad,
      );
    }
    const blockLength = AesCbc.blockLengthInBytes;
    final padded = Uint8List(
      clearText.length +
          paddingAlgorithm.paddingLength(blockLength, clearText.length),
    )..setAll(0, clearText);
    paddingAlgorithm.setBlockPadding(blockLength, padded, clearText.length);
    return _boxed(this, key.encryptBlocks(iv, padded), secretKey, nonce, aad);
  }

  @override
  Future<List<int>> decrypt(
    SecretBox secretBox, {
    required SecretKey secretKey,
    List<int> aad = const <int>[],
    Uint8List? possibleBuffer,
  }) async {
    final cipherText = _bytes(secretBox.cipherText);
    final key = rind.AesCbcDecryptingKey(
      _algorithm,
      await _checkedKey(
        this,
        secretKey,
        length: cipherText.length,
        nonce: secretBox.nonce,
        // DartAesCbc leaves AAD to the MAC, which MacAlgorithm.empty ignores.
        aad: macAlgorithm.supportsAad ? aad : const <int>[],
      ),
    );
    // Before decrypting, so that a forged ciphertext never reaches the
    // padding check.
    await secretBox.checkMac(
      macAlgorithm: macAlgorithm,
      secretKey: secretKey,
      aad: aad,
    );
    const blockLength = AesCbc.blockLengthInBytes;
    if (cipherText.length % blockLength != 0) {
      throw ArgumentError.value(
        secretBox,
        'secretBox',
        'Invalid cipherText length: ${cipherText.length}',
      );
    }
    final iv = _bytes(secretBox.nonce);
    if (_pkcs7) {
      try {
        return key.decrypt(iv, cipherText);
      } on rind.RindException catch (e) {
        if (e.error == rind.RindError.decryptFailed) {
          throw SecretBoxPaddingError();
        }
        rethrow;
      }
    }
    final clearText = key.decryptBlocks(iv, cipherText);
    final padding = paddingAlgorithm.getBlockPadding(blockLength, clearText);
    if (padding < 0) throw SecretBoxPaddingError();
    return Uint8List.sublistView(clearText, 0, clearText.length - padding);
  }
}

/// AES-CTR with the package's MAC over its ciphertext, as `DartAesCtr`
/// composes them.
///
/// It counts over the whole 16-byte counter block, whatever [counterBits]
/// says, as `DartAesCtr` does, so that their ciphertexts match.
final class _AesCtr extends AesCtr {
  _AesCtr(
    this.macAlgorithm,
    this.secretKeyLength,
    this.counterBits,
    Random? random,
  ) : _algorithm = _aes(secretKeyLength),
      super.constructor(random: random);

  @override
  final MacAlgorithm macAlgorithm;

  @override
  final int secretKeyLength;

  @override
  final int counterBits;

  final rind.CipherAlgorithm _algorithm;

  // Takes a nonce of up to 16 bytes and zero fills the rest of the counter
  // block, as the package does.
  Uint8List _xor(
    Uint8List key,
    List<int> nonce,
    int keyStreamIndex,
    List<int> input,
  ) {
    if (nonce.length > 16) {
      throw ArgumentError.value(nonce, 'nonce', 'Must be at most 16 bytes');
    }
    final ctr = rind.AesCtr(_algorithm, key, 128);
    return _xorFrom(16, keyStreamIndex, input, (block, data) {
      final counterBlock = Uint8List(16)..setAll(0, nonce);
      for (var i = 15; i >= 0 && block != 0; i--) {
        block += counterBlock[i];
        counterBlock[i] = block & 0xff;
        block >>= 8;
      }
      return ctr.applyKeystream(counterBlock, data);
    });
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
    nonce ??= newNonce();
    final key = await _checkedKey(
      this,
      secretKey,
      length: clearText.length,
      nonce: nonce,
      aad: aad,
      keyStreamIndex: keyStreamIndex,
    );
    final cipherText = _xor(key, nonce, keyStreamIndex, clearText);
    return _boxed(this, cipherText, secretKey, nonce, aad);
  }

  @override
  Future<List<int>> decrypt(
    SecretBox secretBox, {
    required SecretKey secretKey,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    final key = await _checkedKey(
      this,
      secretKey,
      length: secretBox.cipherText.length,
      nonce: secretBox.nonce,
      aad: aad,
      keyStreamIndex: keyStreamIndex,
    );
    await secretBox.checkMac(
      macAlgorithm: macAlgorithm,
      secretKey: secretKey,
      aad: aad,
    );
    return _xor(key, secretBox.nonce, keyStreamIndex, secretBox.cipherText);
  }
}

/// ChaCha20 with the package's MAC over its ciphertext, as `DartChacha20`
/// composes them, for a MAC that uses none of the keystream. Poly1305 in
/// ChaCha20-Poly1305 uses its first block, and is [_Chacha20Poly1305].
final class _Chacha20 extends Chacha20 {
  _Chacha20(this.macAlgorithm, Random? random)
    : super.constructor(random: random) {
    if (macAlgorithm.keyStreamUsed != 0) {
      throw _unsupported('ChaCha20 with $macAlgorithm');
    }
  }

  @override
  final MacAlgorithm macAlgorithm;

  static Uint8List _xor(
    Uint8List key,
    List<int> nonce,
    int keyStreamIndex,
    List<int> input,
  ) {
    final chacha = rind.ChaCha20(key);
    return _xorFrom(
      64,
      keyStreamIndex,
      input,
      (block, data) => chacha.applyKeystream(_bytes(nonce), block, data),
    );
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
    nonce ??= newNonce();
    final key = await _checkedKey(
      this,
      secretKey,
      length: clearText.length,
      nonce: nonce,
      aad: aad,
      keyStreamIndex: keyStreamIndex,
    );
    final cipherText = _xor(key, nonce, keyStreamIndex, clearText);
    return _boxed(this, cipherText, secretKey, nonce, aad);
  }

  @override
  Future<List<int>> decrypt(
    SecretBox secretBox, {
    required SecretKey secretKey,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    final key = await _checkedKey(
      this,
      secretKey,
      length: secretBox.cipherText.length,
      nonce: secretBox.nonce,
      aad: aad,
      keyStreamIndex: keyStreamIndex,
    );
    await secretBox.checkMac(
      macAlgorithm: macAlgorithm,
      secretKey: secretKey,
      aad: aad,
    );
    return _xor(key, secretBox.nonce, keyStreamIndex, secretBox.cipherText);
  }
}
