// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import 'dart:convert';
import 'dart:typed_data';

import 'package:rind/legacy.dart';
import 'package:rind/rind.dart';
import 'package:test/test.dart';

Uint8List hex(String s) {
  s = s.replaceAll(' ', '');
  return Uint8List.fromList([
    for (var i = 0; i < s.length; i += 2)
      int.parse(s.substring(i, i + 2), radix: 16),
  ]);
}

Uint8List ascii(String s) => Uint8List.fromList(utf8.encode(s));

Matcher throwsRind(RindError error) =>
    throwsA(isA<RindException>().having((e) => e.error, 'error', error));

Uint8List flipped(Uint8List bytes, [int index = 0]) =>
    Uint8List.fromList(bytes)..[index] ^= 1;

void main() {
  group('digest', () {
    final abc = ascii('abc');

    test('known answers', () {
      final cases = {
        DigestAlgorithm.sha256:
            'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad',
        DigestAlgorithm.sha384:
            'cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed'
            '8086072ba1e7cc2358baeca134c825a7',
        DigestAlgorithm.sha512_256:
            '53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23',
        DigestAlgorithm.sha3_256:
            '3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532',
        digestSha1: 'a9993e364706816aba3e25717850c26c9cd0d89d',
        digestMd5: '900150983cd24fb0d6963f7d28e17f72',
      };
      cases.forEach((algorithm, expected) {
        expect(digest(algorithm, abc), hex(expected), reason: '$algorithm');
      });
    });

    test('a context matches the one-shot digest, and restarts', () {
      for (final algorithm in [
        DigestAlgorithm.sha256,
        DigestAlgorithm.sha384,
        DigestAlgorithm.sha512,
        DigestAlgorithm.sha512_256,
        DigestAlgorithm.sha3_256,
        DigestAlgorithm.sha3_384,
        DigestAlgorithm.sha3_512,
      ]) {
        final context = DigestContext(algorithm)
          ..update(ascii('a'))
          ..update(ascii('bc'));
        final expected = digest(algorithm, abc);
        expect(context.finish(), expected);
        expect(expected.length, algorithm.outputLength);
        context.update(abc);
        expect(context.finish(), expected);
      }
    });
  });

  group('HMAC', () {
    // RFC 4231, test case 2.
    final key = ascii('Jefe');
    final data = ascii('what do ya want for nothing?');
    final expected = hex(
      '5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843',
    );

    test('signs and verifies', () {
      final hmacKey = HmacKey(HmacAlgorithm.sha256, key);
      expect(hmacKey.sign(data), expected);
      hmacKey.verify(data, expected);
      expect(
        () => hmacKey.verify(data, flipped(expected)),
        throwsRind(RindError.badSignature),
      );
    });

    test('a context signs once', () {
      final context = HmacContext(HmacKey(HmacAlgorithm.sha256, key))
        ..update(data.sublist(0, 5))
        ..update(data.sublist(5));
      expect(context.sign(), expected);
      expect(context.sign, throwsStateError);
      expect(() => context.update(data), throwsStateError);
    });

    test('legacy SHA-1', () {
      // RFC 2202, test case 2.
      expect(
        HmacKey(hmacSha1, key).sign(data),
        hex('effcdf6ae5eb2fa2d27416d5f184df9c259a7c79'),
      );
    });
  });

  test('HKDF', () {
    // RFC 5869, test case 1.
    final prk = HkdfSalt(
      HkdfAlgorithm.sha256,
      hex('000102030405060708090a0b0c'),
    ).extract(hex('0b' * 22));
    final okm = hex(
      '3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56'
      'ecc4c5bf34007208d5b887185865',
    );
    expect(prk.expand([hex('f0f1f2f3f4f5f6f7f8f9')], 42), okm);
    expect(prk.expand([hex('f0f1f2'), hex('f3f4f5f6f7f8f9')], 42), okm);
    expect(
      () => prk.expand([], 255 * 32 + 1),
      throwsRind(RindError.wrongLength),
    );
    expect(() => prk.expand([], 1 << 40), throwsRind(RindError.wrongLength));
  });

  group('PBKDF2', () {
    test('derives and verifies', () {
      // RFC 7914 section 11.
      final secret = Pbkdf2Secret(Pbkdf2Algorithm.hmacSha256, ascii('passwd'));
      final expected = hex(
        '55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57'
        'c20dacbc49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783',
      );
      expect(secret.derive(1, ascii('salt'), 64), expected);
      secret.verify(1, ascii('salt'), expected);
      expect(
        () => secret.verify(1, ascii('salt'), flipped(expected)),
        throwsRind(RindError.badSignature),
      );
      expect(
        () => secret.verify(1, ascii('salt'), expected.sublist(0, 16)),
        throwsRind(RindError.wrongLength),
      );
      expect(() => secret.derive(0, ascii('salt'), 32), throwsRangeError);
    });

    test('legacy SHA-1', () {
      // RFC 6070.
      expect(
        Pbkdf2Secret(
          pbkdf2HmacSha1,
          ascii('password'),
        ).derive(2, ascii('salt'), 20),
        hex('ea6c014dc72d6f8ccd1ed92ace1d41f0d8de8957'),
      );
    });
  });

  group('AEAD', () {
    test('AES-128-GCM known answer', () {
      // The GCM specification's test case 2.
      final key = AeadKey(AeadAlgorithm.aes128Gcm, Uint8List(16));
      final nonce = Nonce.assumeUniqueForKey(Uint8List(12));
      final sealed = key.seal(nonce, Uint8List(16));
      expect(
        sealed,
        hex('0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf'),
      );
      expect(key.open(nonce, sealed), Uint8List(16));
    });

    test('every algorithm round-trips and refuses tampering', () {
      for (final algorithm in AeadAlgorithm.values) {
        final key = AeadKey(algorithm, Uint8List(algorithm.keyLength)..[0] = 7);
        final nonce = Nonce.assumeUniqueForKey(Uint8List(12)..[0] = 1);
        final aad = ascii('header');
        final sealed = key.seal(nonce, ascii('hello'), aad: aad);
        expect(sealed.length, 5 + algorithm.tagLength);
        expect(key.open(nonce, sealed, aad: aad), ascii('hello'));
        expect(
          () => key.open(nonce, flipped(sealed), aad: aad),
          throwsRind(RindError.decryptFailed),
        );
        expect(
          () => key.open(nonce, sealed),
          throwsRind(RindError.decryptFailed),
        );
        expect(
          () => key.open(nonce, Uint8List(15)),
          throwsRind(RindError.decryptFailed),
        );
        expect(key.open(nonce, key.seal(nonce, Uint8List(0))), isEmpty);
      }
    });

    test('refuses wrong lengths', () {
      expect(
        () => AeadKey(AeadAlgorithm.aes256Gcm, Uint8List(16)),
        throwsRind(RindError.wrongLength),
      );
      final key = AeadKey(AeadAlgorithm.chacha20Poly1305, Uint8List(32));
      expect(
        () => key.seal(Nonce.assumeUniqueForKey(Uint8List(8)), Uint8List(1)),
        throwsRind(RindError.wrongLength),
      );
    });

    test('a randomized nonce key picks fresh nonces', () {
      final key = RandomizedNonceKey(Uint8List(32));
      final first = key.seal(ascii('hello'), aad: ascii('a'));
      final second = key.seal(ascii('hello'), aad: ascii('a'));
      expect(first.nonce, isNot(second.nonce));
      expect(
        key.open(first.nonce, first.sealed, aad: ascii('a')),
        ascii('hello'),
      );
      expect(
        () => key.open(second.nonce, first.sealed, aad: ascii('a')),
        throwsRind(RindError.decryptFailed),
      );
      expect(
        () => RandomizedNonceKey(Uint8List(16)),
        throwsRind(RindError.wrongLength),
      );
    });
  });

  group('cipher', () {
    // NIST SP 800-38A's AES-128 key and first two plaintext blocks.
    final key = hex('2b7e151628aed2a6abf7158809cf4f3c');
    final plaintext = hex(
      '6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e51',
    );

    test('AES-CBC known answer, with and without padding', () {
      // SP 800-38A F.2.1, and the full padding block it implies.
      final iv = hex('000102030405060708090a0b0c0d0e0f');
      final blocks = hex(
        '7649abac8119b246cee98e9b12e9197d5086cb9b507219ee95db113a917678b2',
      );
      final encrypting = AesCbcEncryptingKey(CipherAlgorithm.aes128, key);
      final decrypting = AesCbcDecryptingKey(CipherAlgorithm.aes128, key);
      expect(
        encrypting.encryptBlocks(CbcIv.assumeUnpredictable(iv), plaintext),
        blocks,
      );
      expect(decrypting.decryptBlocks(iv, blocks), plaintext);

      final padded = encrypting.encrypt(
        CbcIv.assumeUnpredictable(iv),
        plaintext,
      );
      expect(padded, [...blocks, ...hex('55e21d7100b988ffec32feeafaf23538')]);
      expect(decrypting.decrypt(iv, padded), plaintext);
    });

    test('AES-CBC pads every length and refuses malformed input', () {
      for (final algorithm in CipherAlgorithm.values) {
        final keyBytes = Uint8List(algorithm.keyLength)..[0] = 7;
        final encrypting = AesCbcEncryptingKey(algorithm, keyBytes);
        final decrypting = AesCbcDecryptingKey(algorithm, keyBytes);
        for (final length in [0, 1, 15, 16, 17, 32]) {
          final iv = CbcIv.random();
          final message = Uint8List(length)..fillRange(0, length, 9);
          final ciphertext = encrypting.encrypt(iv, message);
          expect(ciphertext.length, length ~/ 16 * 16 + 16);
          expect(decrypting.decrypt(iv.bytes, ciphertext), message);
        }
      }
      final encrypting = AesCbcEncryptingKey(CipherAlgorithm.aes128, key);
      final decrypting = AesCbcDecryptingKey(CipherAlgorithm.aes128, key);
      final iv = Uint8List(16);
      // A last block that decrypts to a zero padding byte.
      final badPadding = encrypting.encryptBlocks(
        CbcIv.assumeUnpredictable(iv),
        Uint8List(16),
      );
      for (final ciphertext in [Uint8List(0), Uint8List(15), badPadding]) {
        expect(
          () => decrypting.decrypt(iv, ciphertext),
          throwsRind(RindError.decryptFailed),
        );
      }
      expect(
        () => decrypting.decryptBlocks(iv, Uint8List(17)),
        throwsRind(RindError.decryptFailed),
      );
      expect(
        () => encrypting.encryptBlocks(
          CbcIv.assumeUnpredictable(iv),
          Uint8List(17),
        ),
        throwsRind(RindError.wrongLength),
      );
      expect(
        () => decrypting.decrypt(Uint8List(8), Uint8List(16)),
        throwsRind(RindError.wrongLength),
      );
      expect(
        () => CbcIv.assumeUnpredictable(Uint8List(8)),
        throwsRind(RindError.wrongLength),
      );
      expect(
        () => AesCbcEncryptingKey(CipherAlgorithm.aes256, key),
        throwsRind(RindError.wrongLength),
      );
    });

    test('AES-CTR known answer, and refuses a counter that wraps', () {
      // SP 800-38A F.5.1.
      final counterBlock = hex('f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff');
      final ciphertext = hex(
        '874d6191b620e3261bef6864990db6ce9806f66b7970fdff8617187bb9fffdff',
      );
      final ctr = AesCtr(CipherAlgorithm.aes128, key, 128);
      expect(ctr.applyKeystream(counterBlock, plaintext), ciphertext);
      expect(ctr.applyKeystream(counterBlock, ciphertext), plaintext);

      // One counter bit counts two blocks.
      final narrow = AesCtr(CipherAlgorithm.aes128, key, 1);
      expect(narrow.applyKeystream(counterBlock, Uint8List(32)), hasLength(32));
      expect(
        () => narrow.applyKeystream(counterBlock, Uint8List(33)),
        throwsRind(RindError.wrongLength),
      );
      for (final bits in [0, 129, 256 + 64]) {
        expect(
          () => AesCtr(CipherAlgorithm.aes128, key, bits),
          throwsRind(RindError.wrongLength),
        );
      }
      expect(
        () => AesCtr(CipherAlgorithm.aes128, key, 1 << 32 | 64),
        throwsRangeError,
      );
      expect(
        () => ctr.applyKeystream(Uint8List(12), plaintext),
        throwsRind(RindError.wrongLength),
      );
    });

    test('ChaCha20 known answer, and refuses a counter that wraps', () {
      // RFC 8439, section 2.4.2.
      final chacha = ChaCha20(Uint8List.fromList(List.generate(32, (i) => i)));
      final nonce = hex('000000000000004a00000000');
      final message = ascii(
        "Ladies and Gentlemen of the class of '99: If I could offer you only "
        'one tip for the future, sunscreen would be it.',
      );
      final ciphertext = hex(
        '6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0b'
        'f91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d8'
        '07ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab7793736'
        '5af90bbf74a35be6b40b8eedf2785e42874d',
      );
      expect(chacha.applyKeystream(nonce, 1, message), ciphertext);
      expect(chacha.applyKeystream(nonce, 1, ciphertext), message);

      expect(
        chacha.applyKeystream(nonce, 0xffffffff, Uint8List(64)),
        hasLength(64),
      );
      expect(
        () => chacha.applyKeystream(nonce, 0xffffffff, Uint8List(65)),
        throwsRind(RindError.wrongLength),
      );
      expect(
        () => chacha.applyKeystream(nonce, 1 << 32, Uint8List(1)),
        throwsRangeError,
      );
      expect(
        () => chacha.applyKeystream(Uint8List(8), 0, Uint8List(1)),
        throwsRind(RindError.wrongLength),
      );
      expect(() => ChaCha20(Uint8List(16)), throwsRind(RindError.wrongLength));
    });
  });

  group('agreement', () {
    test('X25519 known answer', () {
      // RFC 7748 section 6.1.
      final alice = AgreementPrivateKey.fromScalar(
        AgreementAlgorithm.x25519,
        hex('77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a'),
      );
      final bobPublic = hex(
        'de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f',
      );
      expect(
        alice.publicKey.bytes,
        hex('8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a'),
      );
      expect(
        alice.agree(bobPublic),
        hex('4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742'),
      );
    });

    test('every algorithm agrees and round-trips its encodings', () {
      for (final algorithm in AgreementAlgorithm.values) {
        final alice = AgreementPrivateKey.generate(algorithm);
        final bob = AgreementPrivateKey.generate(algorithm);
        final secret = alice.agree(bob.publicKey.bytes);
        expect(bob.agree(alice.publicKey.bytes), secret);

        final reloaded = AgreementPrivateKey.fromPkcs8(
          algorithm,
          alice.toPkcs8(),
        );
        expect(reloaded.agree(bob.publicKey.bytes), secret);
        expect(
          AgreementPrivateKey.fromScalar(
            algorithm,
            alice.toScalar(),
          ).publicKey.bytes,
          alice.publicKey.bytes,
        );
        expect(
          AgreementPublicKey.fromSpki(
            algorithm,
            alice.publicKey.toSpki(),
          ).bytes,
          alice.publicKey.bytes,
        );
      }
    });

    test('refuses a point off the curve, saying why', () {
      final key = AgreementPrivateKey.generate(AgreementAlgorithm.ecdhP256);
      final point = flipped(key.publicKey.bytes, 64);
      expect(
        () => key.agree(point),
        throwsA(
          isA<RindException>()
              .having((e) => e.error, 'error', RindError.keyRejected)
              .having((e) => e.reason, 'reason', isNotEmpty),
        ),
      );
      expect(
        () => AgreementPublicKey(AgreementAlgorithm.ecdhP256, point),
        throwsRind(RindError.keyRejected),
      );
    });
  });

  group('signatures', () {
    test('Ed25519 known answer', () {
      // RFC 8032 section 7.1, test 1.
      final pair = Ed25519KeyPair.fromSeed(
        hex('9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60'),
      );
      final publicKey = hex(
        'd75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a',
      );
      final signature = hex(
        'e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065'
        '224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b',
      );
      expect(pair.publicKey.bytes, publicKey);
      expect(pair.sign(Uint8List(0)), signature);
      final verifier = PublicKey(VerificationAlgorithm.ed25519, publicKey);
      verifier.verify(Uint8List(0), signature);
      expect(
        () => verifier.verify(Uint8List(1), signature),
        throwsRind(RindError.badSignature),
      );

      expect(
        Ed25519KeyPair.fromPkcs8(pair.toPkcs8()).publicKey.bytes,
        publicKey,
      );
      expect(
        Ed25519KeyPair.fromPkcs8(pair.toPkcs8v1()).publicKey.bytes,
        publicKey,
      );
      expect(
        Ed25519KeyPair.fromSeedAndPublicKey(pair.toSeed(), publicKey).toSeed(),
        pair.toSeed(),
      );
      expect(
        () => Ed25519KeyPair.fromSeedAndPublicKey(
          pair.toSeed(),
          flipped(publicKey),
        ),
        throwsRind(RindError.keyRejected),
      );
      expect(
        PublicKey.fromSpki(VerificationAlgorithm.ed25519, pair.toSpki()).bytes,
        publicKey,
      );
    });

    test('ECDSA signs and round-trips its encodings', () {
      final verifiers = {
        EcdsaSigningAlgorithm.p256Sha256Asn1:
            VerificationAlgorithm.ecdsaP256Sha256Asn1,
        EcdsaSigningAlgorithm.p256Sha256Fixed:
            VerificationAlgorithm.ecdsaP256Sha256Fixed,
        EcdsaSigningAlgorithm.p384Sha384Asn1:
            VerificationAlgorithm.ecdsaP384Sha384Asn1,
        EcdsaSigningAlgorithm.p384Sha384Fixed:
            VerificationAlgorithm.ecdsaP384Sha384Fixed,
        EcdsaSigningAlgorithm.p521Sha512Asn1:
            VerificationAlgorithm.ecdsaP521Sha512Asn1,
        EcdsaSigningAlgorithm.p521Sha512Fixed:
            VerificationAlgorithm.ecdsaP521Sha512Fixed,
      };
      final message = ascii('hello');
      verifiers.forEach((algorithm, verification) {
        final pair = EcdsaKeyPair.generate(algorithm);
        final signature = pair.sign(message);
        pair.publicKey.verify(message, signature);
        final verifier = PublicKey(verification, pair.publicKey.bytes);
        verifier.verify(message, signature);
        expect(
          () => verifier.verify(flipped(message), signature),
          throwsRind(RindError.badSignature),
        );

        for (final reloaded in [
          EcdsaKeyPair.fromPkcs8(algorithm, pair.toPkcs8()),
          EcdsaKeyPair.fromSec1(algorithm, pair.toSec1()),
          EcdsaKeyPair.fromScalarAndPublicKey(
            algorithm,
            pair.toScalar(),
            pair.publicKey.bytes,
          ),
        ]) {
          expect(reloaded.publicKey.bytes, pair.publicKey.bytes);
        }
        expect(
          PublicKey.fromSpki(verification, pair.toSpki()).bytes,
          pair.publicKey.bytes,
        );
      });
      expect(
        () => EcdsaKeyPair.fromPkcs8(
          EcdsaSigningAlgorithm.p384Sha384Asn1,
          EcdsaKeyPair.generate(EcdsaSigningAlgorithm.p256Sha256Asn1).toPkcs8(),
        ),
        throwsRind(RindError.keyRejected),
      );
    });

    test('RSA signs, verifies, and round-trips its encodings', () {
      final pair = RsaKeyPair.generate(RsaKeySize.rsa2048);
      final message = ascii('hello');
      final verifiers = {
        RsaSigningAlgorithm.pkcs1Sha256: VerificationAlgorithm.rsaPkcs1Sha256,
        RsaSigningAlgorithm.pkcs1Sha384: VerificationAlgorithm.rsaPkcs1Sha384,
        RsaSigningAlgorithm.pkcs1Sha512: VerificationAlgorithm.rsaPkcs1Sha512,
        RsaSigningAlgorithm.pssSha256: VerificationAlgorithm.rsaPssSha256,
        RsaSigningAlgorithm.pssSha384: VerificationAlgorithm.rsaPssSha384,
        RsaSigningAlgorithm.pssSha512: VerificationAlgorithm.rsaPssSha512,
      };
      final (:n, :e) = rsaComponents(
        pair.publicKey(RsaSigningAlgorithm.pkcs1Sha256).bytes,
      );
      verifiers.forEach((algorithm, verification) {
        final signature = pair.sign(algorithm, message);
        expect(signature.length, 256);
        pair.publicKey(algorithm).verify(message, signature);
        PublicKey.fromSpki(
          verification,
          pair.toSpki(),
        ).verify(message, signature);
        PublicKey.fromComponents(
          verification,
          n: n,
          e: e,
        ).verify(message, signature);
        expect(
          () => pair.publicKey(algorithm).verify(flipped(message), signature),
          throwsRind(RindError.badSignature),
        );
      });
      PublicKey.fromSpki(
        VerificationAlgorithm.rsaPssSha256AnySalt,
        pair.toSpki(),
      ).verify(message, pair.sign(RsaSigningAlgorithm.pssSha256, message));

      final reloaded = RsaKeyPair.fromPkcs8(pair.toPkcs8());
      expect(reloaded.toSpki(), pair.toSpki());
      expect(
        () => RsaKeyPair.fromPkcs8(flipped(pair.toPkcs8(), 1)),
        throwsRind(RindError.keyRejected),
      );
      // Legacy verification takes the same keys.
      PublicKey.fromSpki(rsaPkcs1Sha1, pair.toSpki());
    });
  });

  test('ML-KEM-768', () {
    final decapsulationKey = DecapsulationKey.generate(KemAlgorithm.mlKem768);
    final encapsulationKey = EncapsulationKey(
      KemAlgorithm.mlKem768,
      decapsulationKey.publicKey.bytes,
    );
    final (:ciphertext, :sharedSecret) = encapsulationKey.encapsulate();
    expect(decapsulationKey.decapsulate(ciphertext), sharedSecret);
    expect(
      decapsulationKey.decapsulate(flipped(ciphertext)),
      isNot(sharedSecret),
    );
    expect(
      () => decapsulationKey.decapsulate(ciphertext.sublist(1)),
      throwsRind(RindError.wrongLength),
    );
    expect(
      () => EncapsulationKey(KemAlgorithm.mlKem768, Uint8List(10)),
      throwsRind(RindError.keyRejected),
    );
  });

  test('RSA-OAEP', () {
    final key = RsaDecryptingKey.generate(
      OaepAlgorithm.sha256,
      RsaKeySize.rsa2048,
    );
    final label = ascii('label');
    final encrypting = RsaEncryptingKey(OaepAlgorithm.sha256, key.toSpki());
    expect(encrypting.maxMessageLength, 256 - 2 * 32 - 2);
    final ciphertext = encrypting.encrypt(ascii('hello'), label: label);
    expect(key.decrypt(ciphertext, label: label), ascii('hello'));
    expect(() => key.decrypt(ciphertext), throwsRind(RindError.decryptFailed));
    expect(
      () => encrypting.encrypt(Uint8List(encrypting.maxMessageLength + 1)),
      throwsRind(RindError.wrongLength),
    );

    final (:n, :e) = rsaComponents(key.publicKey.bytes);
    final fromComponents = RsaEncryptingKey.fromComponents(
      OaepAlgorithm.sha256,
      n: n,
      e: e,
    );
    expect(fromComponents.toSpki(), key.toSpki());
    final reloaded = RsaDecryptingKey.fromPkcs8(
      OaepAlgorithm.sha256,
      key.toPkcs8(),
    );
    expect(reloaded.decrypt(fromComponents.encrypt(ascii('hi'))), ascii('hi'));

    final legacy = RsaDecryptingKey.fromPkcs8(oaepSha1, key.toPkcs8());
    expect(legacy.decrypt(legacy.publicKey.encrypt(ascii('hi'))), ascii('hi'));
  });

  test('randomness, comparison, and CPU support', () {
    final a = Uint8List(32);
    final b = Uint8List(32);
    fillRandom(a);
    fillRandom(b);
    expect(a, isNot(b));
    constantTimeVerify(a, Uint8List.fromList(a));
    expect(() => constantTimeVerify(a, b), throwsRind(RindError.notEqual));
    expect(
      () => constantTimeVerify(a, Uint8List(31)),
      throwsRind(RindError.wrongLength),
    );
    expect(hasAesHardware(), isA<bool>());
  });
}

/// The modulus and exponent of a PKCS#1 `RSAPublicKey`.
({Uint8List n, Uint8List e}) rsaComponents(Uint8List der) {
  var offset = 0;
  int length() {
    final first = der[offset++];
    if (first < 0x80) return first;
    var len = 0;
    for (var i = 0; i < (first & 0x7f); i++) {
      len = len << 8 | der[offset++];
    }
    return len;
  }

  Uint8List integer() {
    expect(der[offset++], 0x02);
    final len = length();
    var value = der.sublist(offset, offset + len);
    offset += len;
    while (value.length > 1 && value[0] == 0) {
      value = value.sublist(1);
    }
    return value;
  }

  expect(der[offset++], 0x30);
  length();
  return (n: integer(), e: integer());
}
