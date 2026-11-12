// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Each algorithm against the cryptography package's Dart implementation
// where it has one, and against rind's own API where it has none.

import 'dart:math';
import 'dart:typed_data';

import 'package:cryptography/cryptography.dart';
import 'package:cryptography/dart.dart';
import 'package:rind/rind.dart' as rind;
import 'package:rind_cryptography/rind_cryptography.dart';
import 'package:test/test.dart';

final _rind = RindCryptography();

/// [length] bytes that differ from test to test.
Uint8List _bytes(int length, [int seed = 0]) => Uint8List.fromList([
  for (var i = 0; i < length; i++) (i * 7 + seed) & 0xff,
]);

final _lengths = [0, 1, 15, 16, 17, 63, 64, 65, 1000];

Matcher get _throwsAuthentication =>
    throwsA(isA<SecretBoxAuthenticationError>());

Matcher get _throwsUnsupported => throwsA(isA<UnsupportedError>());

void main() {
  test('constructors use the instance', () {
    final previous = Cryptography.instance;
    addTearDown(() => Cryptography.instance = previous);
    Cryptography.instance = _rind;
    for (final algorithm in <Object>[
      AesGcm.with256bits(),
      Chacha20.poly1305Aead(),
      Sha256(),
      Hmac.sha256(),
      Ed25519(),
      X25519(),
    ]) {
      expect(algorithm.runtimeType.toString(), startsWith('_'));
    }
  });

  test('what rind lacks throws where it is constructed', () {
    final hmac = _rind.hmac(_rind.sha256());
    final constructors = <Object Function()>[
      () => _rind.aesCbc(macAlgorithm: hmac),
      () => _rind.aesCtr(macAlgorithm: hmac),
      () => _rind.aesGcm(nonceLength: 16),
      () => _rind.argon2id(
        memory: 1,
        parallelism: 1,
        iterations: 1,
        hashLength: 32,
      ),
      () => _rind.blake2b(),
      () => _rind.blake2s(),
      () => _rind.chacha20(macAlgorithm: hmac),
      () => _rind.hchacha20(),
      () => _rind.poly1305(),
      () => _rind.sha224(),
      () => _rind.xchacha20(macAlgorithm: hmac),
      () => _rind.hmac(const DartSha224()),
      () => _rind.ecdsaP256(_rind.sha384()),
      () => _rind.ecdsaP384(_rind.sha256()),
      () => _rind.ecdsaP521(_rind.sha256()),
      () => _rind.rsaPss(_rind.sha1(), nonceLengthInBytes: 20),
      () => _rind.rsaSsaPkcs1v15(const DartSha224()),
      () => _rind.pbkdf2(macAlgorithm: Poly1305(), iterations: 1, bits: 256),
    ];
    for (final constructor in constructors) {
      expect(constructor, _throwsUnsupported);
    }
  });

  group('hash', () {
    final pairs = {
      _rind.sha1(): const DartSha1(),
      _rind.sha256(): const DartSha256(),
      _rind.sha384(): const DartSha384(),
      _rind.sha512(): const DartSha512(),
    };

    test('matches the Dart implementation, whole and in parts', () async {
      for (final MapEntry(key: algorithm, value: dart) in pairs.entries) {
        expect(algorithm, dart);
        for (final length in _lengths) {
          final data = _bytes(length);
          final expected = await dart.hash(data);
          expect(await algorithm.hash(data), expected);
          expect(await algorithm.hash(data.toList()), expected);

          final sink = algorithm.newHashSink()
            ..add(data.sublist(0, length ~/ 2))
            ..addSlice(data.toList(), length ~/ 2, length, true);
          expect(await sink.hash(), expected);
        }
      }
    });

    test('a sink hashes only once closed, and takes nothing after', () async {
      final sink = _rind.sha256().newHashSink()..add([1]);
      await expectLater(sink.hash(), throwsStateError);
      sink.close();
      expect(() => sink.add([2]), throwsStateError);
      expect(await sink.hash(), await const DartSha256().hash([1]));
    });
  });

  group('HMAC', () {
    test('matches the Dart implementation, whole and in parts', () async {
      for (final hash in [
        _rind.sha1(),
        _rind.sha256(),
        _rind.sha384(),
        _rind.sha512(),
      ]) {
        final hmac = _rind.hmac(hash);
        final dart = DartHmac(hash.toSync());
        expect(hmac, dart);
        // Keys shorter and longer than the block, which longer ones are
        // hashed down to.
        for (final keyLength in [0, 16, 200]) {
          final key = SecretKey(_bytes(keyLength, 3));
          for (final length in _lengths) {
            final data = _bytes(length);
            final expected = await dart.calculateMac(data, secretKey: key);
            expect(await hmac.calculateMac(data, secretKey: key), expected);

            final sink = await hmac.newMacSink(secretKey: key);
            sink
              ..add(data.sublist(0, length ~/ 2))
              ..addSlice(data, length ~/ 2, length, false)
              ..close();
            expect(sink.isClosed, isTrue);
            expect(await sink.mac(), expected);
          }
        }
      }
    });

    test('refuses AAD', () async {
      final hmac = _rind.hmac(_rind.sha256());
      final key = SecretKey([1]);
      await expectLater(
        hmac.calculateMac([1], secretKey: key, aad: [1]),
        throwsArgumentError,
      );
    });
  });

  group('HKDF', () {
    test('matches the Dart implementation', () async {
      for (final hash in [_rind.sha256(), _rind.sha512()]) {
        final max = 255 * hash.hashLengthInBytes;
        for (final outputLength in [1, 32, 100, max]) {
          final rindHkdf = _rind.hkdf(
            hmac: _rind.hmac(hash),
            outputLength: outputLength,
          );
          final dart = DartHkdf(
            hmac: DartHmac(hash.toSync()),
            outputLength: outputLength,
          );
          for (final salt in [<int>[], _bytes(16, 1)]) {
            final secretKey = SecretKey(_bytes(32, 2));
            final info = _bytes(10, 3);
            final expected = await dart.deriveKey(
              secretKey: secretKey,
              nonce: salt,
              info: info,
            );
            final derived = await rindHkdf.deriveKey(
              secretKey: secretKey,
              nonce: salt,
              info: info,
            );
            expect(derived.bytes, expected.bytes);
          }
        }
      }
    });

    test('refuses more than 255 blocks', () {
      expect(
        () => _rind.hkdf(hmac: _rind.hmac(_rind.sha256()), outputLength: 8161),
        throwsRangeError,
      );
    });
  });

  group('PBKDF2', () {
    test('matches the Dart implementation', () async {
      for (final hash in [_rind.sha1(), _rind.sha256(), _rind.sha512()]) {
        for (final bits in [64, 100, 256, 1024]) {
          final pbkdf2 = _rind.pbkdf2(
            macAlgorithm: _rind.hmac(hash),
            iterations: 3,
            bits: bits,
          );
          final dart = DartPbkdf2(
            macAlgorithm: DartHmac(hash.toSync()),
            iterations: 3,
            bits: bits,
          );
          final password = SecretKey(_bytes(12));
          final salt = _bytes(16, 1);
          final expected = await dart.deriveKey(
            secretKey: password,
            nonce: salt,
          );
          final derived = await pbkdf2.deriveKey(
            secretKey: password,
            nonce: salt,
          );
          expect(await derived.extractBytes(), await expected.extractBytes());
        }
      }
    });

    test('refuses no iterations', () {
      expect(
        () => _rind.pbkdf2(
          macAlgorithm: _rind.hmac(_rind.sha256()),
          iterations: 0,
          bits: 256,
        ),
        throwsRangeError,
      );
    });
  });

  group('AEAD', () {
    final pairs = <Cipher, Cipher>{
      _rind.aesGcm(secretKeyLength: 16): DartAesGcm.with128bits(),
      _rind.aesGcm(secretKeyLength: 24): DartAesGcm.with192bits(),
      _rind.aesGcm(): DartAesGcm.with256bits(),
      _rind.chacha20Poly1305Aead(): const DartChacha20.poly1305Aead(),
    };

    test('matches the Dart implementation both ways', () async {
      for (final MapEntry(key: cipher, value: dart) in pairs.entries) {
        expect(cipher, dart);
        final secretKey = await cipher.newSecretKey();
        for (final length in _lengths) {
          final clearText = _bytes(length);
          final nonce = cipher.newNonce();
          final aad = _bytes(length % 20, 5);
          final box = await cipher.encrypt(
            clearText,
            secretKey: secretKey,
            nonce: nonce,
            aad: aad,
          );
          expect(
            box,
            await dart.encrypt(
              clearText,
              secretKey: secretKey,
              nonce: nonce,
              aad: aad,
            ),
          );
          expect(
            await cipher.decrypt(box, secretKey: secretKey, aad: aad),
            clearText,
          );
        }
      }
    });

    test('refuses what does not authenticate', () async {
      for (final cipher in pairs.keys) {
        final secretKey = await cipher.newSecretKey();
        final box = await cipher.encrypt([1, 2, 3], secretKey: secretKey);
        final tampered = [
          SecretBox([1, 2, 4], nonce: box.nonce, mac: box.mac),
          SecretBox(box.cipherText, nonce: box.nonce, mac: Mac(_bytes(16))),
          SecretBox(box.cipherText, nonce: box.nonce, mac: Mac(_bytes(15))),
          // The tag's first byte moved to the ciphertext's end.
          SecretBox(
            [...box.cipherText, box.mac.bytes[0]],
            nonce: box.nonce,
            mac: Mac(box.mac.bytes.sublist(1)),
          ),
        ];
        for (final box in tampered) {
          await expectLater(
            cipher.decrypt(box, secretKey: secretKey),
            _throwsAuthentication,
          );
        }
        await expectLater(
          cipher.decrypt(box, secretKey: secretKey, aad: [1]),
          _throwsAuthentication,
        );
      }
    });

    test('refuses wrong key and nonce lengths', () async {
      final cipher = _rind.aesGcm();
      await expectLater(
        cipher.encrypt([1], secretKey: SecretKey(_bytes(16))),
        throwsArgumentError,
      );
      await expectLater(
        cipher.encrypt([1], secretKey: SecretKey(_bytes(32)), nonce: [1]),
        throwsArgumentError,
      );
    });

    test('ChaCha20-Poly1305 refuses a key stream index', () async {
      final cipher = _rind.chacha20Poly1305Aead();
      final secretKey = await cipher.newSecretKey();
      await expectLater(
        cipher.encrypt([1], secretKey: secretKey, keyStreamIndex: 64),
        _throwsUnsupported,
      );
    });

    test('streams', () async {
      final cipher = _rind.aesGcm();
      final secretKey = await cipher.newSecretKey();
      final nonce = cipher.newNonce();
      final chunks = [_bytes(10), _bytes(100, 1), _bytes(1, 2)];
      late Mac mac;
      final cipherText = await cipher
          .encryptStream(
            Stream.fromIterable(chunks),
            secretKey: secretKey,
            nonce: nonce,
            onMac: (m) => mac = m,
          )
          .expand((chunk) => chunk)
          .toList();
      final box = await DartAesGcm.with256bits().encrypt(
        chunks.expand((chunk) => chunk).toList(),
        secretKey: secretKey,
        nonce: nonce,
      );
      expect(cipherText, box.cipherText);
      expect(mac, box.mac);
    });

    test(
      'XChaCha20-Poly1305 interoperates with the Dart implementation',
      () async {
        final cipher = _rind.xchacha20Poly1305Aead();
        const dart = DartXchacha20.poly1305Aead();
        expect(cipher, dart);
        final secretKey = await cipher.newSecretKey();
        for (final length in _lengths) {
          final clearText = _bytes(length);
          final aad = _bytes(length % 20, 5);
          final box = await cipher.encrypt(
            clearText,
            secretKey: secretKey,
            aad: aad,
          );
          expect(box.nonce, hasLength(24));
          expect(
            await dart.decrypt(box, secretKey: secretKey, aad: aad),
            clearText,
          );
          final dartBox = await dart.encrypt(
            clearText,
            secretKey: secretKey,
            aad: aad,
          );
          expect(
            await cipher.decrypt(dartBox, secretKey: secretKey, aad: aad),
            clearText,
          );
          await expectLater(
            cipher.decrypt(dartBox, secretKey: secretKey),
            length % 20 == 0 ? completion(clearText) : _throwsAuthentication,
          );
        }
      },
    );

    test('XChaCha20-Poly1305 picks its own nonces', () async {
      final cipher = _rind.xchacha20Poly1305Aead();
      final secretKey = await cipher.newSecretKey();
      await expectLater(
        cipher.encrypt([1], secretKey: secretKey, nonce: cipher.newNonce()),
        _throwsUnsupported,
      );
      final first = await cipher.encrypt([1], secretKey: secretKey);
      final second = await cipher.encrypt([1], secretKey: secretKey);
      expect(first.nonce, isNot(second.nonce));
      await expectLater(
        cipher.decrypt(
          SecretBox(
            [...first.cipherText, first.mac.bytes[0]],
            nonce: first.nonce,
            mac: Mac(first.mac.bytes.sublist(1)),
          ),
          secretKey: secretKey,
        ),
        _throwsAuthentication,
      );
    });
  });

  test('a seeded random picks the keys and nonces Dart does', () async {
    final rindCipher = _rind.withRandom(Random(1)).aesGcm();
    final dartCipher = DartCryptography(random: Random(1)).aesGcm();
    expect(
      await (await rindCipher.newSecretKey()).extractBytes(),
      await (await dartCipher.newSecretKey()).extractBytes(),
    );
    expect(rindCipher.newNonce(), dartCipher.newNonce());
    expect(
      await (await _rind
              .withRandom(Random(3))
              .xchacha20Poly1305Aead()
              .newSecretKey())
          .extractBytes(),
      await (await DartCryptography(
        random: Random(3),
      ).xchacha20Poly1305Aead().newSecretKey()).extractBytes(),
    );

    final rindPair = await _rind.withRandom(Random(2)).ed25519().newKeyPair();
    final dartPair = await DartCryptography(
      random: Random(2),
    ).ed25519().newKeyPair();
    expect(await rindPair.extract(), await dartPair.extract());
  });

  group('X25519', () {
    test('matches the Dart implementation', () async {
      final algorithm = _rind.x25519();
      final dart = DartX25519();
      for (var i = 0; i < 4; i++) {
        final seed = _bytes(32, i);
        final pair = await algorithm.newKeyPairFromSeed(seed);
        final dartPair = await dart.newKeyPairFromSeed(seed);
        expect(await pair.extract(), await dartPair.extract());

        final peer = await (await dart.newKeyPair()).extractPublicKey();
        final secret = await algorithm.sharedSecretKey(
          keyPair: pair,
          remotePublicKey: peer,
        );
        final expected = await dart.sharedSecretKey(
          keyPair: dartPair,
          remotePublicKey: peer,
        );
        expect(await secret.extractBytes(), await expected.extractBytes());
      }
    });

    test('refuses a peer of small order', () async {
      final algorithm = _rind.x25519();
      final pair = await algorithm.newKeyPair();
      await expectLater(
        algorithm.sharedSecretKey(
          keyPair: pair,
          remotePublicKey: SimplePublicKey(
            Uint8List(32),
            type: KeyPairType.x25519,
          ),
        ),
        throwsArgumentError,
      );
    });
  });

  group('Ed25519', () {
    test('matches the Dart implementation', () async {
      final algorithm = _rind.ed25519();
      final dart = DartEd25519();
      for (var i = 0; i < 4; i++) {
        final seed = _bytes(32, i);
        final pair = await algorithm.newKeyPairFromSeed(seed);
        final dartPair = await dart.newKeyPairFromSeed(seed);
        expect(await pair.extract(), await dartPair.extract());

        final message = _bytes(i * 50, 9);
        final signature = await algorithm.sign(message, keyPair: pair);
        expect(signature, await dart.sign(message, keyPair: dartPair));
        expect(await algorithm.verify(message, signature: signature), isTrue);
        expect(
          await algorithm.verify([...message, 0], signature: signature),
          isFalse,
        );
        final flipped = Uint8List.fromList(signature.bytes)..[63] ^= 1;
        expect(
          await algorithm.verify(
            message,
            signature: Signature(flipped, publicKey: signature.publicKey),
          ),
          isFalse,
        );
      }
    });

    test('verifies nothing under a public key that is no point', () async {
      // y = 2 is on no point of the curve.
      final notAPoint = Uint8List(32)..[0] = 2;
      final signature = Signature(
        Uint8List(64),
        publicKey: SimplePublicKey(notAPoint, type: KeyPairType.ed25519),
      );
      expect(await _rind.ed25519().verify([1], signature: signature), isFalse);
      expect(await DartEd25519().verify([1], signature: signature), isFalse);
    });
  });

  group('ECDH', () {
    final curves = {
      _rind.ecdhP256(length: 32): rind.AgreementAlgorithm.ecdhP256,
      _rind.ecdhP384(length: 48): rind.AgreementAlgorithm.ecdhP384,
      _rind.ecdhP521(length: 66): rind.AgreementAlgorithm.ecdhP521,
    };

    test('key pairs are rind\'s, and both sides agree', () async {
      for (final MapEntry(key: algorithm, value: agreement) in curves.entries) {
        final pair = await algorithm.newKeyPair();
        final data = await pair.extract();
        final key = rind.AgreementPrivateKey.fromScalar(
          agreement,
          Uint8List.fromList(data.d),
        );
        expect(key.publicKey.bytes, [4, ...data.x, ...data.y]);

        final peer = rind.AgreementPrivateKey.generate(agreement);
        final peerBytes = peer.publicKey.bytes;
        final length = data.x.length;
        final secret = await algorithm.sharedSecretKey(
          keyPair: pair,
          remotePublicKey: EcPublicKey(
            x: peerBytes.sublist(1, 1 + length),
            y: peerBytes.sublist(1 + length),
            type: algorithm.keyPairType,
          ),
        );
        expect(await secret.extractBytes(), peer.agree(key.publicKey.bytes));
      }
    });

    test('shortens the secret to the length asked', () async {
      final full = _rind.ecdhP256(length: 32);
      final short = _rind.ecdhP256(length: 16);
      final pair = await full.newKeyPair();
      final peer = await (await full.newKeyPair()).extractPublicKey();
      final secret = await full.sharedSecretKey(
        keyPair: pair,
        remotePublicKey: peer,
      );
      final shortSecret = await short.sharedSecretKey(
        keyPair: pair,
        remotePublicKey: peer,
      );
      expect(
        await shortSecret.extractBytes(),
        (await secret.extractBytes()).sublist(0, 16),
      );
      expect(() => _rind.ecdhP256(length: 33), throwsRangeError);
    });

    test('refuses mismatched and invalid keys', () async {
      final algorithm = _rind.ecdhP256(length: 32);
      final pair = await algorithm.newKeyPair();
      final other = await algorithm.newKeyPair();
      final data = await pair.extract();
      final mismatched = EcKeyPairData(
        d: data.d,
        x: (await other.extract()).x,
        y: (await other.extract()).y,
        type: KeyPairType.p256,
      );
      final peer = await other.extractPublicKey();
      await expectLater(
        algorithm.sharedSecretKey(keyPair: mismatched, remotePublicKey: peer),
        throwsArgumentError,
      );
      final offCurve = EcPublicKey(
        x: peer.x,
        y: Uint8List.fromList(peer.y)..[31] ^= 1,
        type: KeyPairType.p256,
      );
      await expectLater(
        algorithm.sharedSecretKey(keyPair: pair, remotePublicKey: offCurve),
        throwsArgumentError,
      );
      final otherCurve = await _rind.ecdhP384(length: 48).newKeyPair();
      await expectLater(
        algorithm.sharedSecretKey(keyPair: otherCurve, remotePublicKey: peer),
        throwsArgumentError,
      );
      await expectLater(
        algorithm.newKeyPairFromSeed(_bytes(32)),
        _throwsUnsupported,
      );
    });
  });

  group('ECDSA', () {
    final curves = {
      _rind.ecdsaP256(_rind.sha256()): (
        rind.EcdsaSigningAlgorithm.p256Sha256Fixed,
        rind.VerificationAlgorithm.ecdsaP256Sha256Fixed,
      ),
      _rind.ecdsaP384(_rind.sha384()): (
        rind.EcdsaSigningAlgorithm.p384Sha384Fixed,
        rind.VerificationAlgorithm.ecdsaP384Sha384Fixed,
      ),
      _rind.ecdsaP521(_rind.sha512()): (
        rind.EcdsaSigningAlgorithm.p521Sha512Fixed,
        rind.VerificationAlgorithm.ecdsaP521Sha512Fixed,
      ),
    };

    test('interoperates with rind and the package\'s DER', () async {
      for (final MapEntry(key: algorithm, value: (signing, verification))
          in curves.entries) {
        final pair = await algorithm.newKeyPair();
        final data = await pair.extract();
        final point = Uint8List.fromList([4, ...data.x, ...data.y]);
        final message = _bytes(100);

        final signature = await algorithm.sign(message, keyPair: pair);
        rind.PublicKey(
          verification,
          point,
        ).verify(message, Uint8List.fromList(signature.bytes));
        expect(await algorithm.verify(message, signature: signature), isTrue);
        expect(
          await algorithm.verify([...message, 0], signature: signature),
          isFalse,
        );

        // The package's own PKCS#8 and SPKI encodings, which rind reads.
        final rindPair = rind.EcdsaKeyPair.fromPkcs8(signing, data.toDer());
        expect(rindPair.publicKey.bytes, point);
        expect(
          rind.PublicKey.fromSpki(verification, data.publicKey.toDer()).bytes,
          point,
        );
        final rindSignature = Signature(
          rindPair.sign(message),
          publicKey: data.publicKey,
        );
        expect(
          await algorithm.verify(message, signature: rindSignature),
          isTrue,
        );
      }
    });

    test('verifies a malformed signature as false', () async {
      final algorithm = _rind.ecdsaP256(_rind.sha256());
      final pair = await algorithm.newKeyPair();
      final publicKey = await pair.extractPublicKey();
      for (final bytes in [<int>[], _bytes(63), _bytes(64), _bytes(65)]) {
        expect(
          await algorithm.verify([
            1,
          ], signature: Signature(bytes, publicKey: publicKey)),
          isFalse,
        );
      }
    });
  });

  group('RSA', () {
    // One key for the group, since generating one takes a while.
    late RsaKeyPairData data;

    setUpAll(() async {
      final pair = await _rind
          .rsaSsaPkcs1v15(_rind.sha256())
          .newKeyPair(modulusLength: 2048);
      data = await pair.extract();
      expect(data.n, hasLength(256));
      expect(data.e, [1, 0, 1]);
      final pss = await _rind
          .rsaPss(_rind.sha256(), nonceLengthInBytes: 32)
          .newKeyPair(modulusLength: 2048);
      expect((await pss.extract()).n, isNot(data.n));
    });

    test('PKCS#1 v1.5 signs what rind verifies', () async {
      // rind checks a private key's components agree as it loads them, so a
      // signature at all means they round-tripped.
      final message = _bytes(100);
      for (final (hash, verification) in [
        (_rind.sha256(), rind.VerificationAlgorithm.rsaPkcs1Sha256),
        (_rind.sha384(), rind.VerificationAlgorithm.rsaPkcs1Sha384),
        (_rind.sha512(), rind.VerificationAlgorithm.rsaPkcs1Sha512),
      ]) {
        final pkcs1 = _rind.rsaSsaPkcs1v15(hash);
        final signature = await pkcs1.sign(message, keyPair: data);
        expect(signature.publicKey, data.publicKey);
        rind.PublicKey.fromComponents(
          verification,
          n: Uint8List.fromList(data.n),
          e: Uint8List.fromList(data.e),
        ).verify(message, Uint8List.fromList(signature.bytes));
        expect(await pkcs1.verify(message, signature: signature), isTrue);
        expect(
          await pkcs1.verify([...message, 0], signature: signature),
          isFalse,
        );
      }
    });

    test('PSS signs with a salt as long as the hash', () async {
      final message = _bytes(100);
      final pss = _rind.rsaPss(_rind.sha256(), nonceLengthInBytes: 32);
      final signature = await pss.sign(message, keyPair: data);
      expect(await pss.verify(message, signature: signature), isTrue);
      rind.PublicKey.fromComponents(
        rind.VerificationAlgorithm.rsaPssSha256,
        n: Uint8List.fromList(data.n),
        e: Uint8List.fromList(data.e),
      ).verify(message, Uint8List.fromList(signature.bytes));

      // Another salt length verifies any salt, and signs nothing.
      final salted = _rind.rsaPss(_rind.sha256(), nonceLengthInBytes: 16);
      expect(await salted.verify(message, signature: signature), isTrue);
      await expectLater(
        salted.sign(message, keyPair: data),
        _throwsUnsupported,
      );
    });

    test('SHA-1 PKCS#1 v1.5 verifies and signs nothing', () async {
      final pkcs1 = _rind.rsaSsaPkcs1v15(_rind.sha1());
      await expectLater(pkcs1.sign([1], keyPair: data), _throwsUnsupported);
      expect(
        await pkcs1.verify([
          1,
        ], signature: Signature(_bytes(256), publicKey: data.publicKey)),
        isFalse,
      );
    });

    test('refuses what rind cannot generate or load', () async {
      final pkcs1 = _rind.rsaSsaPkcs1v15(_rind.sha256());
      await expectLater(
        pkcs1.newKeyPair(modulusLength: 1024),
        _throwsUnsupported,
      );
      await expectLater(
        pkcs1.newKeyPair(modulusLength: 2048, publicExponent: [3]),
        _throwsUnsupported,
      );
      final noCrt = RsaKeyPairData(
        n: data.n,
        e: data.e,
        d: data.d,
        p: data.p,
        q: data.q,
      );
      await expectLater(pkcs1.sign([1], keyPair: noCrt), throwsArgumentError);
      final wrongD = RsaKeyPairData(
        n: data.n,
        e: data.e,
        d: Uint8List.fromList(data.d)..[10] ^= 1,
        p: data.p,
        q: data.q,
        dp: data.dp,
        dq: data.dq,
        qi: data.qi,
      );
      await expectLater(pkcs1.sign([1], keyPair: wrongD), throwsArgumentError);
      final small = RsaPublicKey(
        n: [0xc1, for (var i = 0; i < 127; i++) 0x01],
        e: [1, 0, 1],
      );
      await expectLater(
        pkcs1.verify([1], signature: Signature(_bytes(128), publicKey: small)),
        throwsArgumentError,
      );
    });
  });
}
