// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// The package's documented entry point is [RindCryptography]. These classes
// are the implementations it returns.
// ignore_for_file: public_member_api_docs

import 'dart:typed_data';

import 'package:cryptography/cryptography.dart';
import 'package:cryptography/dart.dart';
import 'package:rind/legacy.dart' as legacy;
import 'package:rind/rind.dart' as rind;

Uint8List _bytes(List<int> data) => Uint8List.fromList(data);

Future<Hash> _hash(rind.DigestAlgorithm algorithm, List<int> input) async {
  return Hash(rind.digest(algorithm, _bytes(input)));
}

/// SHA-1.
final class RindSha1 extends Sha1 {
  /// SHA-1.
  const RindSha1() : super.constructor();

  @override
  Future<Hash> hash(List<int> input) => _hash(legacy.digestSha1, input);
}

/// SHA-256.
final class RindSha256 extends Sha256 {
  /// SHA-256.
  const RindSha256() : super.constructor();

  @override
  Future<Hash> hash(List<int> input) =>
      _hash(rind.DigestAlgorithm.sha256, input);
}

/// SHA-384.
final class RindSha384 extends Sha384 {
  /// SHA-384.
  const RindSha384() : super.constructor();

  @override
  Future<Hash> hash(List<int> input) =>
      _hash(rind.DigestAlgorithm.sha384, input);
}

/// SHA-512.
final class RindSha512 extends Sha512 {
  /// SHA-512.
  const RindSha512() : super.constructor();

  @override
  Future<Hash> hash(List<int> input) =>
      _hash(rind.DigestAlgorithm.sha512, input);
}

rind.HmacAlgorithm _hmacAlgorithm(HashAlgorithm hash) {
  if (hash is Sha1) return legacy.hmacSha1;
  if (hash is Sha256) return rind.HmacAlgorithm.sha256;
  if (hash is Sha384) return rind.HmacAlgorithm.sha384;
  if (hash is Sha512) return rind.HmacAlgorithm.sha512;
  throw UnsupportedError('${hash.runtimeType} is not an HMAC rind implements');
}

/// HMAC over a hash rind implements.
final class RindHmac extends Hmac {
  /// HMAC over [hashAlgorithm].
  RindHmac(this.hashAlgorithm) : super.constructor();

  @override
  final HashAlgorithm hashAlgorithm;

  rind.HmacAlgorithm get _hmac => _hmacAlgorithm(hashAlgorithm);

  @override
  Future<Mac> calculateMac(
    List<int> bytes, {
    required SecretKey secretKey,
    List<int> nonce = const <int>[],
    List<int> aad = const <int>[],
  }) async {
    if (aad.isNotEmpty) {
      throw ArgumentError.value(aad, 'aad', 'AAD is not supported by HMAC');
    }
    final key = rind.HmacKey(_hmac, _bytes(await secretKey.extractBytes()));
    return Mac(key.sign(_bytes(bytes)));
  }

  @override
  Future<MacSink> newMacSink({
    required SecretKey secretKey,
    List<int> nonce = const <int>[],
    List<int> aad = const <int>[],
  }) async {
    if (aad.isNotEmpty) {
      throw ArgumentError.value(aad, 'aad', 'AAD is not supported by HMAC');
    }
    final key = rind.HmacKey(_hmac, _bytes(await secretKey.extractBytes()));
    return _RindMacSink(rind.HmacContext(key));
  }
}

final class _RindMacSink extends MacSink {
  _RindMacSink(this._context);

  final rind.HmacContext _context;
  var _closed = false;

  @override
  bool get isClosed => _closed;

  @override
  void addSlice(List<int> chunk, int start, int end, bool isLast) {
    if (_closed) throw StateError('Sink is closed');
    if (end < start || start < 0 || end > chunk.length) {
      throw RangeError.range(end, start, chunk.length);
    }
    if (start != end) {
      _context.update(_bytes(chunk.sublist(start, end)));
    }
    if (isLast) close();
  }

  @override
  void close() {
    _closed = true;
  }

  @override
  Future<Mac> mac() async {
    if (!_closed) throw StateError('Sink is not closed');
    return Mac(_context.sign());
  }
}

/// HKDF over an HMAC rind implements.
final class RindHkdf extends Hkdf {
  /// HKDF with [hmac], producing [outputLength] bytes.
  const RindHkdf({required this.hmac, required this.outputLength})
    : super.constructor();

  @override
  final Hmac hmac;

  @override
  final int outputLength;

  @override
  Future<SecretKeyData> deriveKey({
    required SecretKey secretKey,
    List<int> nonce = const <int>[],
    List<int> info = const <int>[],
  }) async {
    final hash = hmac is RindHmac
        ? hmac as RindHmac
        : RindHmac(hmac.hashAlgorithm);
    final salt = rind.HkdfSalt(_hkdfOf(hash._hmac), _bytes(nonce));
    final prk = salt.extract(_bytes(await secretKey.extractBytes()));
    return SecretKeyData(prk.expand([_bytes(info)], outputLength));
  }
}

/// PBKDF2 over an HMAC rind implements.
final class RindPbkdf2 extends Pbkdf2 {
  /// PBKDF2 with [macAlgorithm], [iterations] rounds, and [bits] of output.
  const RindPbkdf2({
    required this.macAlgorithm,
    required this.iterations,
    required this.bits,
  }) : super.constructor();

  @override
  final MacAlgorithm macAlgorithm;

  @override
  final int iterations;

  @override
  final int bits;

  @override
  Future<SecretKey> deriveKey({
    required SecretKey secretKey,
    required List<int> nonce,
  }) async {
    if (bits <= 0 || bits % 8 != 0) {
      throw ArgumentError.value(
        bits,
        'bits',
        'must be a positive multiple of 8',
      );
    }
    final hmac = macAlgorithm is RindHmac
        ? macAlgorithm as RindHmac
        : macAlgorithm is Hmac
        ? RindHmac((macAlgorithm as Hmac).hashAlgorithm)
        : throw UnsupportedError('rind implements PBKDF2 only over HMAC');
    final secret = rind.Pbkdf2Secret(
      _pbkdf2Of(hmac._hmac),
      _bytes(await secretKey.extractBytes()),
    );
    return SecretKeyData(secret.derive(iterations, _bytes(nonce), bits ~/ 8));
  }
}

Future<SecretBox> _thenMac({
  required Uint8List cipherText,
  required List<int> nonce,
  required SecretKey secretKey,
  required List<int> aad,
  required MacAlgorithm macAlgorithm,
}) async {
  final mac = macAlgorithm == MacAlgorithm.empty
      ? Mac.empty
      : await macAlgorithm.calculateMac(
          cipherText,
          secretKey: secretKey,
          nonce: nonce,
          aad: aad,
        );
  return SecretBox(cipherText, nonce: nonce, mac: mac);
}

Future<void> _checkMac({
  required SecretBox secretBox,
  required SecretKey secretKey,
  required List<int> aad,
  required MacAlgorithm macAlgorithm,
}) {
  return secretBox.checkMac(
    macAlgorithm: macAlgorithm,
    secretKey: secretKey,
    aad: aad,
  );
}

Uint8List _padded(List<int> clearText, PaddingAlgorithm padding) {
  final extra = padding.paddingLength(16, clearText.length);
  final out = Uint8List(clearText.length + extra);
  out.setAll(0, clearText);
  if (extra != 0) padding.setBlockPadding(16, out, clearText.length);
  return out;
}

Uint8List _unpadded(Uint8List decrypted, PaddingAlgorithm padding) {
  final pad = padding.getBlockPadding(16, decrypted);
  if (pad < 0) {
    throw SecretBoxPaddingError(
      message: 'Invalid padding. Padding algorithm is $padding.',
    );
  }
  return Uint8List.sublistView(decrypted, 0, decrypted.length - pad);
}

/// AES-CBC, then the caller's MAC.
final class RindAesCbc extends AesCbc {
  /// AES-CBC with [secretKeyLength]-byte keys.
  const RindAesCbc({
    required this.macAlgorithm,
    required this.paddingAlgorithm,
    required this.secretKeyLength,
    super.random,
  }) : super.constructor();

  @override
  final MacAlgorithm macAlgorithm;

  @override
  final PaddingAlgorithm paddingAlgorithm;

  @override
  final int secretKeyLength;

  @override
  Future<SecretBox> encrypt(
    List<int> clearText, {
    required SecretKey secretKey,
    List<int>? nonce,
    List<int> aad = const <int>[],
    Uint8List? possibleBuffer,
  }) async {
    final key = await _aesKey(secretKey, secretKeyLength);
    final iv = _bytes(nonce ?? newNonce());
    if (iv.length != nonceLength) {
      throw ArgumentError.value(iv, 'nonce', 'Expected $nonceLength bytes');
    }
    final cipherText = rind.AesCbc.encryptBlocks(
      key,
      iv,
      _padded(clearText, paddingAlgorithm),
    );
    return _thenMac(
      cipherText: cipherText,
      nonce: iv,
      secretKey: secretKey,
      aad: aad,
      macAlgorithm: macAlgorithm,
    );
  }

  @override
  Future<List<int>> decrypt(
    SecretBox secretBox, {
    required SecretKey secretKey,
    List<int> aad = const <int>[],
    Uint8List? possibleBuffer,
  }) async {
    await _checkMac(
      secretBox: secretBox,
      secretKey: secretKey,
      aad: aad,
      macAlgorithm: macAlgorithm,
    );
    final key = await _aesKey(secretKey, secretKeyLength);
    final iv = _bytes(secretBox.nonce);
    final decrypted = rind.AesCbc.decryptBlocks(
      key,
      iv,
      _bytes(secretBox.cipherText),
    );
    return _unpadded(decrypted, paddingAlgorithm);
  }
}

/// AES-CTR, then the caller's MAC. The counter is the low [counterBits] of
/// the 16-byte nonce.
final class RindAesCtr extends AesCtr {
  /// AES-CTR with [secretKeyLength]-byte keys.
  const RindAesCtr({
    required this.macAlgorithm,
    required this.secretKeyLength,
    required this.counterBits,
    super.random,
  }) : super.constructor();

  @override
  final MacAlgorithm macAlgorithm;

  @override
  final int secretKeyLength;

  @override
  final int counterBits;

  @override
  Future<SecretBox> encrypt(
    List<int> clearText, {
    required SecretKey secretKey,
    List<int>? nonce,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    if (keyStreamIndex != 0) {
      throw UnsupportedError(
        'rind applies AES-CTR from the start of the nonce',
      );
    }
    final key = await _aesKey(secretKey, secretKeyLength);
    final block = _bytes(nonce ?? newNonce());
    if (block.length != nonceLength) {
      throw ArgumentError.value(block, 'nonce', 'Expected $nonceLength bytes');
    }
    final cipherText = rind.AesCtr.apply(
      key,
      block,
      _bytes(clearText),
      counterBits: counterBits,
    );
    return _thenMac(
      cipherText: cipherText,
      nonce: block,
      secretKey: secretKey,
      aad: aad,
      macAlgorithm: macAlgorithm,
    );
  }

  @override
  Future<List<int>> decrypt(
    SecretBox secretBox, {
    required SecretKey secretKey,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    if (keyStreamIndex != 0) {
      throw UnsupportedError(
        'rind applies AES-CTR from the start of the nonce',
      );
    }
    await _checkMac(
      secretBox: secretBox,
      secretKey: secretKey,
      aad: aad,
      macAlgorithm: macAlgorithm,
    );
    final key = await _aesKey(secretKey, secretKeyLength);
    return rind.AesCtr.apply(
      key,
      _bytes(secretBox.nonce),
      _bytes(secretBox.cipherText),
      counterBits: counterBits,
    );
  }
}

Future<Uint8List> _aesKey(SecretKey secretKey, int length) async {
  final key = _bytes(await secretKey.extractBytes());
  if (key.length != length) {
    throw ArgumentError.value(
      secretKey,
      'secretKey',
      'Expected $length bytes, got ${key.length}',
    );
  }
  return key;
}

rind.AeadAlgorithm _gcm(int secretKeyLength) {
  return switch (secretKeyLength) {
    16 => rind.AeadAlgorithm.aes128Gcm,
    24 => rind.AeadAlgorithm.aes192Gcm,
    32 => rind.AeadAlgorithm.aes256Gcm,
    _ => throw ArgumentError.value(secretKeyLength, 'secretKeyLength'),
  };
}

/// AES-GCM with a 12-byte nonce.
final class RindAesGcm extends AesGcm {
  /// AES-GCM with [secretKeyLength]-byte keys.
  const RindAesGcm({required this.secretKeyLength, super.random})
    : super.constructor();

  @override
  final int secretKeyLength;

  @override
  int get nonceLength => 12;

  @override
  Future<SecretBox> encrypt(
    List<int> clearText, {
    required SecretKey secretKey,
    List<int>? nonce,
    List<int> aad = const <int>[],
    Uint8List? possibleBuffer,
  }) async {
    final key = await _aesKey(secretKey, secretKeyLength);
    final iv = _bytes(nonce ?? newNonce());
    if (iv.length != 12) {
      throw ArgumentError.value(iv, 'nonce', 'Expected 12 bytes');
    }
    final sealed = rind.AeadKey(_gcm(secretKeyLength), key).seal(
      rind.Nonce.assumeUniqueForKey(iv),
      _bytes(clearText),
      aad: _bytes(aad),
    );
    return SecretBox(
      sealed.sublist(0, sealed.length - 16),
      nonce: iv,
      mac: Mac(sealed.sublist(sealed.length - 16)),
    );
  }

  @override
  Future<List<int>> decrypt(
    SecretBox secretBox, {
    required SecretKey secretKey,
    List<int> aad = const <int>[],
    Uint8List? possibleBuffer,
  }) async {
    final key = await _aesKey(secretKey, secretKeyLength);
    final iv = _bytes(secretBox.nonce);
    final sealed =
        Uint8List(secretBox.cipherText.length + secretBox.mac.bytes.length)
          ..setAll(0, secretBox.cipherText)
          ..setAll(secretBox.cipherText.length, secretBox.mac.bytes);
    try {
      return rind.AeadKey(
        _gcm(secretKeyLength),
        key,
      ).open(rind.Nonce.assumeUniqueForKey(iv), sealed, aad: _bytes(aad));
    } on rind.RindException catch (error) {
      if (error.error == rind.RindError.decryptFailed) {
        throw SecretBoxAuthenticationError();
      }
      rethrow;
    }
  }
}

/// ChaCha20 with a 12-byte nonce, or ChaCha20-Poly1305.
final class RindChacha20 extends Chacha20 {
  /// ChaCha20 authenticated by [macAlgorithm].
  const RindChacha20({required this.macAlgorithm, super.random})
    : super.constructor();

  /// ChaCha20-Poly1305.
  RindChacha20.poly1305Aead({super.random})
    : macAlgorithm = const DartChacha20Poly1305AeadMacAlgorithm(),
      super.constructor();

  @override
  final MacAlgorithm macAlgorithm;

  bool get _aead => macAlgorithm is DartChacha20Poly1305AeadMacAlgorithm;

  @override
  Future<SecretBox> encrypt(
    List<int> clearText, {
    required SecretKey secretKey,
    List<int>? nonce,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    if (keyStreamIndex != 0) {
      throw UnsupportedError(
        'rind applies ChaCha20 from the start of the nonce',
      );
    }
    final key = await _aesKey(secretKey, 32);
    final iv = _bytes(nonce ?? newNonce());
    if (iv.length != 12) {
      throw ArgumentError.value(iv, 'nonce', 'Expected 12 bytes');
    }
    if (_aead) {
      final sealed = rind.AeadKey(rind.AeadAlgorithm.chacha20Poly1305, key)
          .seal(
            rind.Nonce.assumeUniqueForKey(iv),
            _bytes(clearText),
            aad: _bytes(aad),
          );
      return SecretBox(
        sealed.sublist(0, sealed.length - 16),
        nonce: iv,
        mac: Mac(sealed.sublist(sealed.length - 16)),
      );
    }
    final cipherText = rind.ChaCha20.apply(key, iv, _bytes(clearText));
    return _thenMac(
      cipherText: cipherText,
      nonce: iv,
      secretKey: secretKey,
      aad: aad,
      macAlgorithm: macAlgorithm,
    );
  }

  @override
  Future<List<int>> decrypt(
    SecretBox secretBox, {
    required SecretKey secretKey,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    if (keyStreamIndex != 0) {
      throw UnsupportedError(
        'rind applies ChaCha20 from the start of the nonce',
      );
    }
    final key = await _aesKey(secretKey, 32);
    final iv = _bytes(secretBox.nonce);
    if (_aead) {
      final sealed =
          Uint8List(secretBox.cipherText.length + secretBox.mac.bytes.length)
            ..setAll(0, secretBox.cipherText)
            ..setAll(secretBox.cipherText.length, secretBox.mac.bytes);
      try {
        return rind.AeadKey(
          rind.AeadAlgorithm.chacha20Poly1305,
          key,
        ).open(rind.Nonce.assumeUniqueForKey(iv), sealed, aad: _bytes(aad));
      } on rind.RindException catch (error) {
        if (error.error == rind.RindError.decryptFailed) {
          throw SecretBoxAuthenticationError();
        }
        rethrow;
      }
    }
    await _checkMac(
      secretBox: secretBox,
      secretKey: secretKey,
      aad: aad,
      macAlgorithm: macAlgorithm,
    );
    return rind.ChaCha20.apply(key, iv, _bytes(secretBox.cipherText));
  }
}

/// XChaCha20-Poly1305. A bare 24-byte-nonce ChaCha20 is not rind's API.
final class RindXchacha20 extends Xchacha20 {
  /// XChaCha20-Poly1305.
  RindXchacha20.poly1305Aead({super.random})
    : macAlgorithm = const DartChacha20Poly1305AeadMacAlgorithm(),
      super.constructor();

  @override
  final MacAlgorithm macAlgorithm;

  @override
  Future<SecretBox> encrypt(
    List<int> clearText, {
    required SecretKey secretKey,
    List<int>? nonce,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    if (keyStreamIndex != 0) {
      throw UnsupportedError(
        'rind applies XChaCha20-Poly1305 from the start of the nonce',
      );
    }
    final key = await _aesKey(secretKey, 32);
    final iv = _bytes(nonce ?? newNonce());
    if (iv.length != 24) {
      throw ArgumentError.value(iv, 'nonce', 'Expected 24 bytes');
    }
    final sealed = rind.RandomizedNonceKey(key)
        .sealWithNonce(iv, _bytes(clearText), aad: _bytes(aad));
    return SecretBox(
      sealed.sublist(0, sealed.length - 16),
      nonce: iv,
      mac: Mac(sealed.sublist(sealed.length - 16)),
    );
  }

  @override
  Future<List<int>> decrypt(
    SecretBox secretBox, {
    required SecretKey secretKey,
    List<int> aad = const <int>[],
    int keyStreamIndex = 0,
    Uint8List? possibleBuffer,
  }) async {
    final key = await _aesKey(secretKey, 32);
    final sealed =
        Uint8List(secretBox.cipherText.length + secretBox.mac.bytes.length)
          ..setAll(0, secretBox.cipherText)
          ..setAll(secretBox.cipherText.length, secretBox.mac.bytes);
    try {
      return rind.RandomizedNonceKey(key)
          .open(_bytes(secretBox.nonce), sealed, aad: _bytes(aad));
    } on rind.RindException catch (error) {
      if (error.error == rind.RindError.decryptFailed) {
        throw SecretBoxAuthenticationError();
      }
      rethrow;
    }
  }
}

int _coordLen(KeyPairType<KeyPairData, PublicKey> type) {
  if (type == KeyPairType.p256) return 32;
  if (type == KeyPairType.p384) return 48;
  if (type == KeyPairType.p521) return 66;
  throw ArgumentError.value(type, 'type');
}

rind.AgreementAlgorithm _agreement(KeyPairType<KeyPairData, PublicKey> type) {
  if (type == KeyPairType.p256) return rind.AgreementAlgorithm.ecdhP256;
  if (type == KeyPairType.p384) return rind.AgreementAlgorithm.ecdhP384;
  if (type == KeyPairType.p521) return rind.AgreementAlgorithm.ecdhP521;
  throw ArgumentError.value(type, 'type');
}

Uint8List _point(List<int> x, List<int> y) {
  final out = Uint8List(1 + x.length + y.length);
  out[0] = 0x04;
  out.setAll(1, x);
  out.setAll(1 + x.length, y);
  return out;
}

Uint8List _scalar(List<int> d, int length) {
  if (d.length > length) {
    throw ArgumentError.value(d, 'd', 'Expected at most $length bytes');
  }
  if (d.length == length) return _bytes(d);
  final out = Uint8List(length);
  out.setAll(length - d.length, d);
  return out;
}

(List<int>, List<int>) _splitPoint(Uint8List point, int coord) {
  if (point.length != 1 + 2 * coord || point[0] != 0x04) {
    throw ArgumentError.value(point, 'point', 'Expected an uncompressed point');
  }
  return (point.sublist(1, 1 + coord), point.sublist(1 + coord));
}

/// ECDH on P-256, P-384, or P-521. [length] is how many leading bytes of the
/// shared x coordinate to return, as WebCrypto's `deriveBits` does.
final class RindEcdh extends Ecdh {
  /// ECDH P-256, returning [length] bytes.
  RindEcdh.p256(this.length)
    : keyPairType = KeyPairType.p256,
      super.constructor();

  /// ECDH P-384, returning [length] bytes.
  RindEcdh.p384(this.length)
    : keyPairType = KeyPairType.p384,
      super.constructor();

  /// ECDH P-521, returning [length] bytes.
  RindEcdh.p521(this.length)
    : keyPairType = KeyPairType.p521,
      super.constructor();

  /// How many leading bytes of the shared secret to return.
  final int length;

  @override
  final KeyPairType<KeyPairData, PublicKey> keyPairType;

  @override
  Future<EcKeyPair> newKeyPair() async {
    final algorithm = _agreement(keyPairType);
    final private = rind.AgreementPrivateKey.generate(algorithm);
    final coord = _coordLen(keyPairType);
    final (x, y) = _splitPoint(private.publicKey.bytes, coord);
    return EcKeyPairData(d: private.toScalar(), x: x, y: y, type: keyPairType);
  }

  @override
  Future<EcKeyPair> newKeyPairFromSeed(List<int> seed) async {
    final coord = _coordLen(keyPairType);
    final private = rind.AgreementPrivateKey.fromScalar(
      _agreement(keyPairType),
      _scalar(seed, coord),
    );
    final (x, y) = _splitPoint(private.publicKey.bytes, coord);
    return EcKeyPairData(
      d: _scalar(seed, coord),
      x: x,
      y: y,
      type: keyPairType,
    );
  }

  @override
  Future<SecretKey> sharedSecretKey({
    required KeyPair keyPair,
    required PublicKey remotePublicKey,
  }) async {
    final data = keyPair is EcKeyPairData
        ? keyPair
        : await keyPair.extract() as EcKeyPairData;
    if (remotePublicKey is! EcPublicKey) {
      throw ArgumentError.value(remotePublicKey, 'remotePublicKey');
    }
    final coord = _coordLen(keyPairType);
    final private = rind.AgreementPrivateKey.fromScalar(
      _agreement(keyPairType),
      _scalar(data.d, coord),
    );
    final secret = private.agree(_point(remotePublicKey.x, remotePublicKey.y));
    if (length <= 0 || length > secret.length) {
      throw ArgumentError.value(
        length,
        'length',
        'must be 1 to ${secret.length} bytes',
      );
    }
    return SecretKeyData(secret.sublist(0, length));
  }
}

rind.EcdsaSigningAlgorithm? _ecdsaSign(
  KeyPairType<KeyPairData, PublicKey> type,
  HashAlgorithm hash,
) {
  if (type == KeyPairType.p256 && hash is Sha256) {
    return rind.EcdsaSigningAlgorithm.p256Sha256Fixed;
  }
  if (type == KeyPairType.p384 && hash is Sha384) {
    return rind.EcdsaSigningAlgorithm.p384Sha384Fixed;
  }
  if (type == KeyPairType.p521 && hash is Sha512) {
    return rind.EcdsaSigningAlgorithm.p521Sha512Fixed;
  }
  return null;
}

rind.VerificationAlgorithm? _ecdsaVerify(
  KeyPairType<KeyPairData, PublicKey> type,
  HashAlgorithm hash,
) {
  if (type == KeyPairType.p256 && hash is Sha256) {
    return rind.VerificationAlgorithm.ecdsaP256Sha256Fixed;
  }
  if (type == KeyPairType.p384 && hash is Sha384) {
    return rind.VerificationAlgorithm.ecdsaP384Sha384Fixed;
  }
  if (type == KeyPairType.p521 && hash is Sha512) {
    return rind.VerificationAlgorithm.ecdsaP521Sha512Fixed;
  }
  return null;
}

/// ECDSA on one NIST curve with that curve's hash, signatures as fixed `r || s`.
final class RindEcdsa extends Ecdsa {
  /// ECDSA P-256.
  RindEcdsa.p256(this.hashAlgorithm)
    : keyPairType = KeyPairType.p256,
      super.constructor();

  /// ECDSA P-384.
  RindEcdsa.p384(this.hashAlgorithm)
    : keyPairType = KeyPairType.p384,
      super.constructor();

  /// ECDSA P-521.
  RindEcdsa.p521(this.hashAlgorithm)
    : keyPairType = KeyPairType.p521,
      super.constructor();

  @override
  final HashAlgorithm hashAlgorithm;

  @override
  final KeyPairType<KeyPairData, PublicKey> keyPairType;

  rind.EcdsaSigningAlgorithm get _sign {
    final algorithm = _ecdsaSign(keyPairType, hashAlgorithm);
    if (algorithm == null) {
      throw UnsupportedError(
        'rind signs ${keyPairType.name} only with its own hash, as fixed r || s',
      );
    }
    return algorithm;
  }

  @override
  Future<EcKeyPair> newKeyPair() async {
    final pair = rind.EcdsaKeyPair.generate(_sign);
    final coord = _coordLen(keyPairType);
    final (x, y) = _splitPoint(pair.publicKey.bytes, coord);
    return EcKeyPairData(d: pair.toScalar(), x: x, y: y, type: keyPairType);
  }

  @override
  Future<EcKeyPair> newKeyPairFromSeed(List<int> seed) async {
    final coord = _coordLen(keyPairType);
    final scalar = _scalar(seed, coord);
    final agreement = rind.AgreementPrivateKey.fromScalar(
      _agreement(keyPairType),
      scalar,
    );
    final (x, y) = _splitPoint(agreement.publicKey.bytes, coord);
    return EcKeyPairData(d: scalar, x: x, y: y, type: keyPairType);
  }

  @override
  Future<Signature> sign(List<int> message, {required KeyPair keyPair}) async {
    final data = keyPair is EcKeyPairData
        ? keyPair
        : await keyPair.extract() as EcKeyPairData;
    final coord = _coordLen(keyPairType);
    final pair = rind.EcdsaKeyPair.fromScalarAndPublicKey(
      _sign,
      _scalar(data.d, coord),
      _point(data.x, data.y),
    );
    return Signature(pair.sign(_bytes(message)), publicKey: data.publicKey);
  }

  @override
  Future<bool> verify(List<int> message, {required Signature signature}) async {
    final publicKey = signature.publicKey;
    if (publicKey is! EcPublicKey) return false;
    final algorithm = _ecdsaVerify(keyPairType, hashAlgorithm);
    if (algorithm == null) {
      throw UnsupportedError(
        'rind verifies ${keyPairType.name} only with its own hash, as fixed r || s',
      );
    }
    try {
      rind.PublicKey(
        algorithm,
        _point(publicKey.x, publicKey.y),
      ).verify(_bytes(message), _bytes(signature.bytes));
      return true;
    } on rind.RindException catch (error) {
      if (error.error == rind.RindError.badSignature) return false;
      if (error.error == rind.RindError.keyRejected) {
        throw ArgumentError.value(publicKey, 'publicKey', error.reason);
      }
      rethrow;
    }
  }
}

/// Ed25519.
final class RindEd25519 extends Ed25519 {
  /// Ed25519.
  const RindEd25519({super.random}) : super.constructor();

  @override
  Future<SimpleKeyPair> newKeyPairFromSeed(List<int> seed) async {
    if (seed.length != 32) {
      throw ArgumentError.value(seed, 'seed', 'Expected 32 bytes');
    }
    final pair = rind.Ed25519KeyPair.fromSeed(_bytes(seed));
    return SimpleKeyPairData(
      _bytes(seed),
      publicKey: SimplePublicKey(
        pair.publicKey.bytes,
        type: KeyPairType.ed25519,
      ),
      type: KeyPairType.ed25519,
    );
  }

  @override
  Future<Signature> sign(List<int> message, {required KeyPair keyPair}) async {
    final data = keyPair is SimpleKeyPairData
        ? keyPair
        : await (keyPair as SimpleKeyPair).extract();
    final pair = rind.Ed25519KeyPair.fromSeed(_bytes(data.bytes));
    return Signature(pair.sign(_bytes(message)), publicKey: data.publicKey);
  }

  @override
  Future<bool> verify(List<int> message, {required Signature signature}) async {
    final publicKey = signature.publicKey;
    if (publicKey is! SimplePublicKey) return false;
    try {
      rind.PublicKey(
        rind.VerificationAlgorithm.ed25519,
        _bytes(publicKey.bytes),
      ).verify(_bytes(message), _bytes(signature.bytes));
      return true;
    } on rind.RindException catch (error) {
      if (error.error == rind.RindError.badSignature) return false;
      rethrow;
    }
  }
}

Uint8List _clampX25519(List<int> seed) {
  if (seed.length != 32) {
    throw ArgumentError.value(seed, 'seed', 'Expected 32 bytes');
  }
  final clamped = _bytes(seed);
  clamped[0] &= 0xf8;
  clamped[31] &= 0x7f;
  clamped[31] |= 0x40;
  return clamped;
}

/// X25519. Extracted private keys are clamped, as the `cryptography` package's
/// own backend does.
final class RindX25519 extends X25519 {
  /// X25519.
  const RindX25519({super.random}) : super.constructor();

  @override
  Future<SimpleKeyPair> newKeyPairFromSeed(List<int> seed) async {
    final clamped = _clampX25519(seed);
    final pair = rind.AgreementPrivateKey.fromScalar(
      rind.AgreementAlgorithm.x25519,
      clamped,
    );
    return SimpleKeyPairData(
      clamped,
      publicKey: SimplePublicKey(
        pair.publicKey.bytes,
        type: KeyPairType.x25519,
      ),
      type: KeyPairType.x25519,
    );
  }

  @override
  Future<SecretKey> sharedSecretKey({
    required KeyPair keyPair,
    required PublicKey remotePublicKey,
  }) async {
    final data = keyPair is SimpleKeyPairData
        ? keyPair
        : await (keyPair as SimpleKeyPair).extract();
    if (remotePublicKey is! SimplePublicKey) {
      throw ArgumentError.value(remotePublicKey, 'remotePublicKey');
    }
    final private = rind.AgreementPrivateKey.fromScalar(
      rind.AgreementAlgorithm.x25519,
      _clampX25519(data.bytes),
    );
    return SecretKeyData(private.agree(_bytes(remotePublicKey.bytes)));
  }
}

bool _exponent65537(List<int> exponent) {
  var i = 0;
  while (i < exponent.length && exponent[i] == 0) {
    i++;
  }
  final rest = exponent.sublist(i);
  return rest.length == 3 && rest[0] == 1 && rest[1] == 0 && rest[2] == 1;
}

rind.RsaKeySize _rsaSize(int bits) {
  return switch (bits) {
    2048 => rind.RsaKeySize.rsa2048,
    3072 => rind.RsaKeySize.rsa3072,
    4096 => rind.RsaKeySize.rsa4096,
    6144 => rind.RsaKeySize.rsa6144,
    8192 => rind.RsaKeySize.rsa8192,
    _ => throw UnsupportedError(
      'rind generates RSA keys of 2048, 3072, 4096, 6144, or 8192 bits',
    ),
  };
}

int? _rsaHash(HashAlgorithm hash) {
  if (hash is Sha256) return 0;
  if (hash is Sha384) return 1;
  if (hash is Sha512) return 2;
  return null;
}

rind.RsaSigningAlgorithm _pkcs1(HashAlgorithm hash) {
  if (hash is Sha256) return rind.RsaSigningAlgorithm.pkcs1Sha256;
  if (hash is Sha384) return rind.RsaSigningAlgorithm.pkcs1Sha384;
  if (hash is Sha512) return rind.RsaSigningAlgorithm.pkcs1Sha512;
  throw UnsupportedError(
    'rind signs RSA PKCS#1 v1.5 with SHA-256, SHA-384, or SHA-512',
  );
}

rind.RsaVerificationAlgorithm _pkcs1Verify(HashAlgorithm hash) {
  if (hash is Sha256) return rind.VerificationAlgorithm.rsaPkcs1Sha256;
  if (hash is Sha384) return rind.VerificationAlgorithm.rsaPkcs1Sha384;
  if (hash is Sha512) return rind.VerificationAlgorithm.rsaPkcs1Sha512;
  throw UnsupportedError(
    'rind verifies RSA PKCS#1 v1.5 with SHA-256, SHA-384, or SHA-512',
  );
}

rind.RsaVerificationAlgorithm _pssVerify(HashAlgorithm hash) {
  if (hash is Sha256) return rind.VerificationAlgorithm.rsaPssSha256AnySalt;
  if (hash is Sha384) return rind.VerificationAlgorithm.rsaPssSha384AnySalt;
  if (hash is Sha512) return rind.VerificationAlgorithm.rsaPssSha512AnySalt;
  throw UnsupportedError(
    'rind verifies RSA-PSS with SHA-256, SHA-384, or SHA-512',
  );
}

final class _RindRsaPair extends RsaKeyPair {
  _RindRsaPair(this._native, this._publicKey) : super.constructor();

  final rind.RsaKeyPair _native;
  final RsaPublicKey _publicKey;

  @override
  Future<RsaKeyPairData> extract() async => _rsaPrivate(_native.toPkcs8());

  @override
  Future<RsaPublicKey> extractPublicKey() async => _publicKey;
}

RsaPublicKey _rsaPublic(Uint8List der) {
  final reader = _Der(der)..sequence();
  return RsaPublicKey(n: reader.integer(), e: reader.integer());
}

RsaKeyPairData _rsaPrivate(Uint8List pkcs8) {
  final reader = _Der(pkcs8)..sequence();
  reader.integer();
  reader.skip();
  final inner = _Der(reader.octetString())..sequence();
  inner.integer();
  final n = inner.integer();
  final e = inner.integer();
  final d = inner.integer();
  final p = inner.integer();
  final q = inner.integer();
  return RsaKeyPairData(n: n, e: e, d: d, p: p, q: q);
}

/// RSA-PSS. The salt length is the one the caller asks for.
final class RindRsaPss extends RsaPss {
  /// RSA-PSS over [hashAlgorithm] with a [nonceLengthInBytes]-byte salt.
  RindRsaPss(this.hashAlgorithm, {required this.nonceLengthInBytes})
    : super.constructor();

  @override
  final HashAlgorithm hashAlgorithm;

  @override
  final int nonceLengthInBytes;

  int get _hash {
    final id = _rsaHash(hashAlgorithm);
    if (id == null) {
      throw UnsupportedError(
        'rind signs RSA-PSS with SHA-256, SHA-384, or SHA-512',
      );
    }
    return id;
  }

  @override
  Future<RsaKeyPair> newKeyPair({
    int modulusLength = RsaPss.defaultModulusLength,
    List<int> publicExponent = RsaPss.defaultPublicExponent,
  }) async {
    if (!_exponent65537(publicExponent)) {
      throw UnsupportedError(
        'rind generates RSA keys only with exponent 65537',
      );
    }
    final native = rind.RsaKeyPair.generate(_rsaSize(modulusLength));
    final publicKey = _rsaPublic(native.publicKey(_pkcs1(hashAlgorithm)).bytes);
    return _RindRsaPair(native, publicKey);
  }

  @override
  Future<Signature> sign(List<int> message, {required KeyPair keyPair}) async {
    final pair = await _nativePair(keyPair, hashAlgorithm);
    final signature = pair._native.signPss(
      _hash,
      nonceLengthInBytes,
      _bytes(message),
    );
    return Signature(signature, publicKey: pair._publicKey);
  }

  @override
  Future<bool> verify(List<int> message, {required Signature signature}) async {
    return _rsaVerify(_pssVerify(hashAlgorithm), message, signature);
  }
}

/// RSA PKCS#1 v1.5.
final class RindRsaPkcs1 extends RsaSsaPkcs1v15 {
  /// RSA PKCS#1 v1.5 over [hashAlgorithm].
  RindRsaPkcs1(this.hashAlgorithm) : super.constructor();

  @override
  final HashAlgorithm hashAlgorithm;

  @override
  Future<RsaKeyPair> newKeyPair({
    int modulusLength = RsaSsaPkcs1v15.defaultModulusLength,
    List<int> publicExponent = RsaSsaPkcs1v15.defaultPublicExponent,
  }) async {
    if (!_exponent65537(publicExponent)) {
      throw UnsupportedError(
        'rind generates RSA keys only with exponent 65537',
      );
    }
    final native = rind.RsaKeyPair.generate(_rsaSize(modulusLength));
    return _RindRsaPair(
      native,
      _rsaPublic(native.publicKey(_pkcs1(hashAlgorithm)).bytes),
    );
  }

  @override
  Future<Signature> sign(List<int> message, {required KeyPair keyPair}) async {
    final pair = await _nativePair(keyPair, hashAlgorithm);
    return Signature(
      pair._native.sign(_pkcs1(hashAlgorithm), _bytes(message)),
      publicKey: pair._publicKey,
    );
  }

  @override
  Future<bool> verify(List<int> message, {required Signature signature}) async {
    return _rsaVerify(_pkcs1Verify(hashAlgorithm), message, signature);
  }
}

Future<_RindRsaPair> _nativePair(KeyPair keyPair, HashAlgorithm hash) async {
  if (keyPair is _RindRsaPair) return keyPair;
  throw UnsupportedError(
    'rind signs with a key it generated; importing RSA parameters is not wired here',
  );
}

Future<bool> _rsaVerify(
  rind.RsaVerificationAlgorithm algorithm,
  List<int> message,
  Signature signature,
) async {
  final publicKey = signature.publicKey;
  if (publicKey is! RsaPublicKey) return false;
  try {
    rind.PublicKey.fromComponents(
      algorithm,
      n: _bytes(publicKey.n),
      e: _bytes(publicKey.e),
    ).verify(_bytes(message), _bytes(signature.bytes));
    return true;
  } on rind.RindException catch (error) {
    if (error.error == rind.RindError.badSignature) return false;
    if (error.error == rind.RindError.keyRejected) {
      throw ArgumentError.value(publicKey, 'publicKey', error.reason);
    }
    rethrow;
  }
}

final class _Der {
  _Der(this.bytes);

  final Uint8List bytes;
  var i = 0;

  void sequence() {
    _tag(0x30);
  }

  Uint8List integer() {
    final value = _contents(0x02);
    if (value.isNotEmpty && value[0] == 0) return value.sublist(1);
    return value;
  }

  Uint8List octetString() => _contents(0x04);

  void skip() {
    final tag = bytes[i];
    _contents(tag);
  }

  Uint8List _contents(int tag) {
    final length = _tag(tag);
    final value = bytes.sublist(i, i + length);
    i += length;
    return value;
  }

  int _tag(int tag) {
    if (bytes[i++] != tag) {
      throw FormatException('unexpected DER tag');
    }
    final first = bytes[i++];
    if (first < 0x80) return first;
    var length = 0;
    for (var n = first & 0x7f; n > 0; n--) {
      length = (length << 8) | bytes[i++];
    }
    return length;
  }
}

rind.HkdfAlgorithm _hkdfOf(rind.HmacAlgorithm hmac) {
  if (hmac == rind.HmacAlgorithm.sha256) return rind.HkdfAlgorithm.sha256;
  if (hmac == rind.HmacAlgorithm.sha384) return rind.HkdfAlgorithm.sha384;
  if (hmac == rind.HmacAlgorithm.sha512) return rind.HkdfAlgorithm.sha512;
  if (hmac == legacy.hmacSha1) return legacy.hkdfSha1;
  throw UnsupportedError('$hmac is not an HKDF rind implements');
}

rind.Pbkdf2Algorithm _pbkdf2Of(rind.HmacAlgorithm hmac) {
  if (hmac == rind.HmacAlgorithm.sha256) return rind.Pbkdf2Algorithm.hmacSha256;
  if (hmac == rind.HmacAlgorithm.sha384) return rind.Pbkdf2Algorithm.hmacSha384;
  if (hmac == rind.HmacAlgorithm.sha512) return rind.Pbkdf2Algorithm.hmacSha512;
  if (hmac == legacy.hmacSha1) return legacy.pbkdf2HmacSha1;
  throw UnsupportedError('$hmac is not a PBKDF2 rind implements');
}
