// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import 'dart:convert';
import 'dart:typed_data';

import 'package:rind/ecdsa.dart' as ecdsa;
import 'package:rind/ed25519.dart' as ed25519;
import 'package:rind/legacy.dart';
import 'package:rind/rind.dart';
import 'package:rind/rsa.dart' as rsa;
import 'package:pointycastle/export.dart' as pc;
import 'package:rind/rsa_legacy.dart' as rsa;
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

    test('AES-GCM takes IVs of any length', () {
      // WebCrypto's seals, which the cryptography package's tests carry, and
      // the GCM specification's test case 2 under a 12-byte IV.
      final key = GcmKey(
        CipherAlgorithm.aes256,
        Uint8List(32)..fillRange(0, 32, 2),
      );
      final iv = GcmIv.assumeUniqueForKey(Uint8List(16)..fillRange(0, 16, 1));
      expect(
        key.seal(iv, Uint8List(0)),
        hex('5d7416b36a2a3c98d340bac56cc5a449'),
      );
      final sealed = key.seal(iv, Uint8List.fromList([1, 2, 3]));
      expect(sealed, hex('a31b4d 8b0891c9dd0af06b1cd1b3604042909f'));
      expect(key.open(iv, sealed), [1, 2, 3]);
      expect(
        () => key.open(iv, flipped(sealed)),
        throwsRind(RindError.decryptFailed),
      );
      expect(
        () => key.open(GcmIv.assumeUniqueForKey(Uint8List(12)), sealed),
        throwsRind(RindError.decryptFailed),
      );
      final nonce = Uint8List(12);
      expect(
        GcmKey(
          CipherAlgorithm.aes128,
          Uint8List(16),
        ).seal(GcmIv.assumeUniqueForKey(nonce), Uint8List(16), aad: ascii('a')),
        AeadKey(
          AeadAlgorithm.aes128Gcm,
          Uint8List(16),
        ).seal(Nonce.assumeUniqueForKey(nonce), Uint8List(16), aad: ascii('a')),
      );
      expect(
        () => key.seal(GcmIv.assumeUniqueForKey(Uint8List(0)), Uint8List(1)),
        throwsRind(RindError.wrongLength),
      );
      expect(
        () => GcmKey(CipherAlgorithm.aes192, Uint8List(16)),
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
      final pair = ed25519.KeyPair.fromSeed(
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
      final verifier = ed25519.PublicKey(publicKey);
      verifier.verify(Uint8List(0), signature);
      expect(
        () => verifier.verify(Uint8List(1), signature),
        throwsRind(RindError.badSignature),
      );

      expect(
        ed25519.KeyPair.fromPkcs8(pair.toPkcs8()).publicKey.bytes,
        publicKey,
      );
      expect(
        ed25519.KeyPair.fromPkcs8(pair.toPkcs8v1()).publicKey.bytes,
        publicKey,
      );
      expect(
        ed25519.KeyPair.fromSeedAndPublicKey(pair.toSeed(), publicKey).toSeed(),
        pair.toSeed(),
      );
      expect(
        () => ed25519.KeyPair.fromSeedAndPublicKey(
          pair.toSeed(),
          flipped(publicKey),
        ),
        throwsRind(RindError.keyRejected),
      );
      expect(
        ed25519.PublicKey.fromSpki(pair.publicKey.toSpki()).bytes,
        publicKey,
      );
    });

    test('Ed25519 public keys refuse another encoding', () {
      final pair = ed25519.KeyPair.generate();
      final spki = pair.publicKey.toSpki();
      for (final bytes in [
        spki,
        Uint8List(0),
        pair.publicKey.bytes.sublist(1),
      ]) {
        expect(
          () => ed25519.PublicKey(bytes),
          throwsRind(RindError.keyRejected),
        );
      }
      final ecdsaSpki = ecdsa.KeyPair.generate(
        ecdsa.SigningAlgorithm.p256Sha256Asn1,
      ).publicKey.toSpki();
      for (final der in [
        pair.publicKey.bytes,
        ecdsaSpki,
        spki.sublist(0, spki.length - 1),
      ]) {
        expect(
          () => ed25519.PublicKey.fromSpki(der),
          throwsRind(RindError.keyRejected),
        );
      }
      // The identity, a point of small order.
      expect(
        () => ed25519.PublicKey(
          hex(
            '01000000000000000000000000000000'
            '00000000000000000000000000000000',
          ),
        ),
        throwsA(
          isA<ed25519.RindException>().having(
            (e) => e.error,
            'error',
            ed25519.RindError.keyRejected,
          ),
        ),
      );
    });

    test('ECDSA signs and round-trips its encodings', () {
      final verifiers = {
        ecdsa.SigningAlgorithm.p256Sha256Asn1:
            ecdsa.VerificationAlgorithm.p256Sha256Asn1,
        ecdsa.SigningAlgorithm.p256Sha256Fixed:
            ecdsa.VerificationAlgorithm.p256Sha256Fixed,
        ecdsa.SigningAlgorithm.p384Sha384Asn1:
            ecdsa.VerificationAlgorithm.p384Sha384Asn1,
        ecdsa.SigningAlgorithm.p384Sha384Fixed:
            ecdsa.VerificationAlgorithm.p384Sha384Fixed,
        ecdsa.SigningAlgorithm.p521Sha512Asn1:
            ecdsa.VerificationAlgorithm.p521Sha512Asn1,
        ecdsa.SigningAlgorithm.p521Sha512Fixed:
            ecdsa.VerificationAlgorithm.p521Sha512Fixed,
      };
      final message = ascii('hello');
      expect(
        ecdsa.SigningAlgorithm.p256Sha256Asn1.toString(),
        'ecdsa.SigningAlgorithm.p256Sha256Asn1',
      );
      expect(
        ecdsa.VerificationAlgorithm.p256Sha256Asn1.toString(),
        'ecdsa.VerificationAlgorithm.p256Sha256Asn1',
      );
      verifiers.forEach((algorithm, verification) {
        final pair = ecdsa.KeyPair.generate(algorithm);
        final signature = pair.sign(message);
        pair.publicKey.verify(message, signature);
        final verifier = ecdsa.PublicKey(verification, pair.publicKey.bytes);
        expect(pair.publicKey.algorithm, verification);
        expect(verifier.algorithm, verification);
        verifier.verify(message, signature);
        expect(
          () => verifier.verify(flipped(message), signature),
          throwsRind(RindError.badSignature),
        );

        for (final reloaded in [
          ecdsa.KeyPair.fromPkcs8(algorithm, pair.toPkcs8()),
          ecdsa.KeyPair.fromSec1(algorithm, pair.toSec1()),
          ecdsa.KeyPair.fromScalarAndPublicKey(
            algorithm,
            pair.toScalar(),
            pair.publicKey.bytes,
          ),
        ]) {
          expect(reloaded.publicKey.bytes, pair.publicKey.bytes);
        }
        final fromSpki = ecdsa.PublicKey.fromSpki(
          verification,
          pair.publicKey.toSpki(),
        );
        expect(fromSpki.bytes, pair.publicKey.bytes);
        expect(fromSpki.toSpki(), pair.publicKey.toSpki());
        expect(fromSpki.algorithm, verification);
      });
      expect(
        () => ecdsa.KeyPair.fromPkcs8(
          ecdsa.SigningAlgorithm.p384Sha384Asn1,
          ecdsa.KeyPair.generate(
            ecdsa.SigningAlgorithm.p256Sha256Asn1,
          ).toPkcs8(),
        ),
        throwsRind(RindError.keyRejected),
      );
    });

    test('ECDSA verifies the hash each id names, on each curve', () {
      // pointycastle signs with every hash, which no rind signer does.
      final curves = {
        ecdsa.SigningAlgorithm.p256Sha256Asn1: (
          pc.ECCurve_secp256r1(),
          [
            ecdsa.VerificationAlgorithm.p256Sha256Asn1,
            ecdsa.VerificationAlgorithm.p256Sha384Asn1,
            ecdsa.VerificationAlgorithm.p256Sha512Asn1,
          ],
        ),
        ecdsa.SigningAlgorithm.p384Sha384Asn1: (
          pc.ECCurve_secp384r1(),
          [
            ecdsa.VerificationAlgorithm.p384Sha256Asn1,
            ecdsa.VerificationAlgorithm.p384Sha384Asn1,
            ecdsa.VerificationAlgorithm.p384Sha512Asn1,
          ],
        ),
        ecdsa.SigningAlgorithm.p521Sha512Asn1: (
          pc.ECCurve_secp521r1(),
          [
            ecdsa.VerificationAlgorithm.p521Sha256Asn1,
            ecdsa.VerificationAlgorithm.p521Sha384Asn1,
            ecdsa.VerificationAlgorithm.p521Sha512Asn1,
          ],
        ),
      };
      final digests = [
        pc.SHA256Digest.new,
        pc.SHA384Digest.new,
        pc.SHA512Digest.new,
      ];
      final random = pc.FortunaRandom()..seed(pc.KeyParameter(Uint8List(32)));
      final message = ascii('hello');
      for (final MapEntry(key: signing, value: (curve, verifications))
          in curves.entries) {
        final pair = ecdsa.KeyPair.generate(signing);
        final private = pc.ECPrivateKey(bigInt(pair.toScalar()), curve);
        for (var hash = 0; hash < digests.length; hash++) {
          final signer = pc.ECDSASigner(digests[hash]())
            ..init(
              true,
              pc.ParametersWithRandom(pc.PrivateKeyParameter(private), random),
            );
          final ecSignature =
              signer.generateSignature(message) as pc.ECSignature;
          final signature = der(0x30, [
            ...derInteger(ecSignature.r),
            ...derInteger(ecSignature.s),
          ]);
          for (var id = 0; id < verifications.length; id++) {
            final key = ecdsa.PublicKey(
              verifications[id],
              pair.publicKey.bytes,
            );
            if (id == hash) {
              key.verify(message, signature);
            } else {
              expect(
                () => key.verify(message, signature),
                throwsRind(RindError.badSignature),
                reason: '${verifications[id]} took ${verifications[hash]}',
              );
            }
          }
        }
      }
    });

    test('ECDSA public keys refuse another encoding or curve', () {
      const p256 = ecdsa.VerificationAlgorithm.p256Sha256Asn1;
      final pair = ecdsa.KeyPair.generate(
        ecdsa.SigningAlgorithm.p256Sha256Asn1,
      );
      final point = pair.publicKey.bytes;
      final spki = pair.publicKey.toSpki();
      final compressed = Uint8List.fromList([
        2 + (point.last & 1),
        ...point.sublist(1, 33),
      ]);
      for (final bytes in [spki, compressed, Uint8List(0), flipped(point, 1)]) {
        expect(
          () => ecdsa.PublicKey(p256, bytes),
          throwsRind(RindError.keyRejected),
        );
      }
      for (final der in [point, spki.sublist(0, spki.length - 1)]) {
        expect(
          () => ecdsa.PublicKey.fromSpki(p256, der),
          throwsRind(RindError.keyRejected),
        );
      }
      expect(
        () => ecdsa.PublicKey.fromSpki(
          ecdsa.VerificationAlgorithm.p384Sha384Asn1,
          spki,
        ),
        throwsRind(RindError.keyRejected),
      );
      expect(
        () => ecdsa.PublicKey.fromSpki(
          p256,
          ed25519.KeyPair.generate().publicKey.toSpki(),
        ),
        throwsRind(RindError.keyRejected),
      );
      final p384Point = ecdsa.KeyPair.generate(
        ecdsa.SigningAlgorithm.p384Sha384Asn1,
      ).publicKey.bytes;
      expect(
        () =>
            ecdsa.PublicKey(ecdsa.VerificationAlgorithm.p384Sha384Asn1, point),
        throwsA(
          isA<ecdsa.RindException>().having(
            (e) => e.error,
            'error',
            ecdsa.RindError.keyRejected,
          ),
        ),
      );
      expect(
        () => ecdsa.PublicKey(p256, p384Point),
        throwsA(
          isA<ecdsa.RindException>().having(
            (e) => e.error,
            'error',
            ecdsa.RindError.keyRejected,
          ),
        ),
      );
    });

    test('RSA signs, verifies, and round-trips its encodings', () {
      final pair = rsa.KeyPair.generate(rsa.KeySize.rsa2048);
      final message = ascii('hello');
      final verifiers = {
        rsa.SigningAlgorithm.pkcs1Sha256: rsa.VerificationAlgorithm.pkcs1Sha256,
        rsa.SigningAlgorithm.pkcs1Sha384: rsa.VerificationAlgorithm.pkcs1Sha384,
        rsa.SigningAlgorithm.pkcs1Sha512: rsa.VerificationAlgorithm.pkcs1Sha512,
        rsa.SigningAlgorithm.pssSha256: rsa.VerificationAlgorithm.pssSha256,
        rsa.SigningAlgorithm.pssSha384: rsa.VerificationAlgorithm.pssSha384,
        rsa.SigningAlgorithm.pssSha512: rsa.VerificationAlgorithm.pssSha512,
      };
      expect(
        rsa.SigningAlgorithm.pssSha256.toString(),
        'rsa.SigningAlgorithm.pssSha256',
      );
      expect(
        rsa.VerificationAlgorithm.pkcs1Sha256.toString(),
        'rsa.VerificationAlgorithm.pkcs1Sha256',
      );
      expect(
        rsa.VerificationAlgorithm.pssSha256AnySalt.toString(),
        'rsa.VerificationAlgorithm.pssSha256AnySalt',
      );
      expect(rsa.pkcs1Sha1.toString(), 'rsa.pkcs1Sha1');
      expect(rsa.OaepAlgorithm.sha256.toString(), 'rsa.OaepAlgorithm.sha256');
      expect(rsa.OaepAlgorithm.sha384.toString(), 'rsa.OaepAlgorithm.sha384');
      expect(rsa.OaepAlgorithm.sha512.toString(), 'rsa.OaepAlgorithm.sha512');
      expect(rsa.oaepSha1.toString(), 'rsa.oaepSha1');
      expect(rsa.KeySize.rsa2048.toString(), 'rsa.KeySize.rsa2048');
      expect(rsa.KeySize.rsa8192.toString(), 'rsa.KeySize.rsa8192');
      final publicKey = pair.publicKey;
      expect(publicKey.modulusLength, 256);
      final (:n, :e) = rsaComponents(publicKey.bytes);
      // One key verifies with every algorithm.
      final keys = [
        publicKey,
        rsa.PublicKey(publicKey.bytes),
        rsa.PublicKey.fromSpki(publicKey.toSpki()),
        rsa.PublicKey.fromComponents(n: n, e: e),
      ];
      for (final key in keys) {
        expect(key.bytes, publicKey.bytes);
        expect(key.toSpki(), publicKey.toSpki());
      }
      verifiers.forEach((algorithm, verification) {
        final signature = pair.sign(algorithm, message);
        expect(signature.length, publicKey.modulusLength);
        for (final key in keys) {
          key.verify(verification, message, signature);
        }
        expect(
          () => publicKey.verify(verification, flipped(message), signature),
          throwsRind(RindError.badSignature),
        );
      });
      publicKey.verify(
        rsa.VerificationAlgorithm.pssSha256AnySalt,
        message,
        pair.sign(rsa.SigningAlgorithm.pssSha256, message),
      );

      // A custom salt length verifies only with that length.
      for (final (signing, verification, hash, anySalt) in [
        (
          rsa.PssSigningAlgorithm.sha256,
          rsa.PssVerificationAlgorithm.sha256,
          rsa.VerificationAlgorithm.pssSha256,
          rsa.VerificationAlgorithm.pssSha256AnySalt,
        ),
        (
          rsa.PssSigningAlgorithm.sha384,
          rsa.PssVerificationAlgorithm.sha384,
          rsa.VerificationAlgorithm.pssSha384,
          rsa.VerificationAlgorithm.pssSha384AnySalt,
        ),
        (
          rsa.PssSigningAlgorithm.sha512,
          rsa.PssVerificationAlgorithm.sha512,
          rsa.VerificationAlgorithm.pssSha512,
          rsa.VerificationAlgorithm.pssSha512AnySalt,
        ),
      ]) {
        final algorithm = signing(16);
        expect(algorithm.saltLength, 16);
        expect(verification(16).saltLength, 16);
        final signature = pair.sign(algorithm, message);
        publicKey.verify(verification(16), message, signature);
        publicKey.verify(anySalt, message, signature);
        for (final other in [verification(17), verification(0), hash]) {
          expect(
            () => publicKey.verify(other, message, signature),
            throwsRind(RindError.badSignature),
          );
        }
        // A salt of none is deterministic.
        expect(pair.sign(signing(0), message), pair.sign(signing(0), message));
        expect(() => signing(-1), throwsRangeError);
        expect(() => verification(0x10000), throwsRangeError);
      }
      publicKey.verify(
        rsa.VerificationAlgorithm.pssSha256,
        message,
        pair.sign(rsa.PssSigningAlgorithm.sha256(32), message),
      );
      // 2048 bits hold a SHA-256 salt of at most 222 bytes.
      pair.sign(rsa.PssSigningAlgorithm.sha256(222), message);
      expect(
        () => pair.sign(rsa.PssSigningAlgorithm.sha256(223), message),
        throwsRind(RindError.keyRejected),
      );

      // A PKCS#1 v1.5 signature is no PSS signature.
      expect(
        () => publicKey.verify(
          rsa.VerificationAlgorithm.pssSha256,
          message,
          pair.sign(rsa.SigningAlgorithm.pkcs1Sha256, message),
        ),
        throwsRind(RindError.badSignature),
      );

      final reloaded = rsa.KeyPair.fromPkcs8(pair.toPkcs8());
      expect(reloaded.publicKey.toSpki(), publicKey.toSpki());
      expect(
        () => rsa.KeyPair.fromPkcs8(flipped(pair.toPkcs8(), 1)),
        throwsRind(RindError.keyRejected),
      );
      // Legacy verification takes the same keys.
      publicKey.verify(
        rsa.pkcs1Min1024Sha256,
        message,
        pair.sign(rsa.SigningAlgorithm.pkcs1Sha256, message),
      );
    });

    test('RSA exports the longest public key it parses', () {
      // An 8192-bit modulus and a 33-bit exponent, the largest rind takes.
      final n = Uint8List(1024)
        ..[0] = 0x80
        ..[1023] = 1;
      final e = hex('01ffffffff');
      final key = rsa.PublicKey.fromComponents(n: n, e: e);
      final encrypting = rsa.EncryptingKey.fromComponents(
        rsa.OaepAlgorithm.sha256,
        n: n,
        e: e,
      );
      expect(key.modulusLength, 1024);
      for (final (bytes, spki) in [
        (key.bytes, key.toSpki()),
        (encrypting.bytes, encrypting.toSpki()),
      ]) {
        expect(bytes.length, 1040);
        expect(spki.length, 1064);
        final components = rsaComponents(bytes);
        expect(components.n, n);
        expect(components.e, e);
        expect(rsa.PublicKey.fromSpki(spki).bytes, bytes);
      }
    });

    test('RSA public keys refuse another encoding', () {
      final publicKey = rsa.KeyPair.generate(rsa.KeySize.rsa2048).publicKey;
      final pkcs1 = publicKey.bytes;
      final spki = publicKey.toSpki();
      for (final der in [spki, Uint8List(0), pkcs1.sublist(1)]) {
        expect(
          () => rsa.PublicKey(der),
          throwsA(
            isA<rsa.RindException>().having(
              (e) => e.error,
              'error',
              rsa.RindError.keyRejected,
            ),
          ),
        );
      }
      final ecdsaSpki = ecdsa.KeyPair.generate(
        ecdsa.SigningAlgorithm.p256Sha256Asn1,
      ).publicKey.toSpki();
      for (final der in [pkcs1, ecdsaSpki, spki.sublist(1)]) {
        expect(
          () => rsa.PublicKey.fromSpki(der),
          throwsRind(RindError.keyRejected),
        );
      }
      expect(
        () => rsa.PublicKey.fromComponents(n: Uint8List(0), e: Uint8List(0)),
        throwsRind(RindError.keyRejected),
      );
    });

    test('RSA legacy algorithms verify the hash each names', () {
      final pair = rsa.KeyPair.generate(rsa.KeySize.rsa2048);
      final message = ascii('hello');
      // rind signs no SHA-1, so pointycastle signs with the same key.
      final pkcs8 = derSequence(pair.toPkcs8());
      final [_, n, _, d, p, q, ...] = derSequence(
        pkcs8[2],
      ).map(bigInt).toList();
      final sha1 =
          (pc.RSASigner(pc.SHA1Digest(), '06052b0e03021a')..init(
                true,
                pc.PrivateKeyParameter<pc.RSAPrivateKey>(
                  pc.RSAPrivateKey(n, d, p, q),
                ),
              ))
              .generateSignature(message)
              .bytes;
      final sha256 = pair.sign(rsa.SigningAlgorithm.pkcs1Sha256, message);
      final sha512 = pair.sign(rsa.SigningAlgorithm.pkcs1Sha512, message);
      final signatures = {
        rsa.pkcs1Sha1: sha1,
        rsa.pkcs1Min1024Sha1: sha1,
        rsa.pkcs1Min1024Sha256: sha256,
        rsa.pkcs1Min1024Sha512: sha512,
      };
      signatures.forEach((algorithm, signature) {
        for (final other in {sha1, sha256, sha512}) {
          if (identical(other, signature)) {
            pair.publicKey.verify(algorithm, message, signature);
          } else {
            expect(
              () => pair.publicKey.verify(algorithm, message, other),
              throwsRind(RindError.badSignature),
              reason: '$algorithm',
            );
          }
        }
      });
    });

    test('RSA refuses a modulus below the algorithm floor at verify', () {
      final pair = rsa.KeyPair.generate(rsa.KeySize.rsa2048);
      final message = ascii('hello');
      final signature = pair.sign(rsa.SigningAlgorithm.pkcs1Sha384, message);
      pair.publicKey.verify(
        rsa.VerificationAlgorithm.pkcs1Sha384,
        message,
        signature,
      );
      expect(
        () => pair.publicKey.verify(rsa.pkcs1Min3072Sha384, message, signature),
        throwsRind(RindError.keyRejected),
      );

      // A 1024-bit key parses, verifies nothing under a 2048-bit floor, and
      // reaches the signature check under a 1024-bit one.
      final small = rsa.PublicKey.fromComponents(
        n: Uint8List(128)
          ..[0] = 0xc0
          ..[127] = 1,
        e: hex('010001'),
      );
      expect(small.modulusLength, 128);
      final forged = Uint8List(128)..[127] = 2;
      for (final algorithm in [
        rsa.VerificationAlgorithm.pkcs1Sha256,
        rsa.VerificationAlgorithm.pssSha256,
        rsa.VerificationAlgorithm.pssSha256AnySalt,
        rsa.pkcs1Sha1,
        rsa.pkcs1Min3072Sha384,
      ]) {
        expect(
          () => small.verify(algorithm, message, forged),
          throwsRind(RindError.keyRejected),
          reason: '$algorithm',
        );
      }
      for (final algorithm in [
        rsa.pkcs1Min1024Sha1,
        rsa.pkcs1Min1024Sha256,
        rsa.pkcs1Min1024Sha512,
      ]) {
        expect(
          () => small.verify(algorithm, message, forged),
          throwsRind(RindError.badSignature),
          reason: '$algorithm',
        );
      }
    });

    test('a key pair returns the same public key each time', () {
      final ecdsaPair = ecdsa.KeyPair.generate(
        ecdsa.SigningAlgorithm.p256Sha256Asn1,
      );
      final ed25519Pair = ed25519.KeyPair.generate();
      final rsaPair = rsa.KeyPair.generate(rsa.KeySize.rsa2048);
      final oaep = rsa.DecryptingKey.fromPkcs8(
        rsa.OaepAlgorithm.sha256,
        rsaPair.toPkcs8(),
      );
      final agreement = AgreementPrivateKey.generate(
        AgreementAlgorithm.ecdhP256,
      );
      final kem = DecapsulationKey.generate(KemAlgorithm.mlKem768);
      expect(identical(ecdsaPair.publicKey, ecdsaPair.publicKey), isTrue);
      expect(ecdsaPair.publicKey.runtimeType, ecdsa.PublicKey);
      expect(ecdsaPair.runtimeType, ecdsa.KeyPair);
      expect(identical(ed25519Pair.publicKey, ed25519Pair.publicKey), isTrue);
      expect(ed25519Pair.publicKey.runtimeType, ed25519.PublicKey);
      expect(ed25519Pair.runtimeType, ed25519.KeyPair);
      expect(identical(rsaPair.publicKey, rsaPair.publicKey), isTrue);
      expect(rsaPair.publicKey.runtimeType, rsa.PublicKey);
      expect(rsaPair.runtimeType, rsa.KeyPair);
      expect(identical(oaep.publicKey, oaep.publicKey), isTrue);
      expect(identical(agreement.publicKey, agreement.publicKey), isTrue);
      expect(identical(kem.publicKey, kem.publicKey), isTrue);

      // The object is cached. Its bytes are not: a caller who wipes the list
      // it was given must not change the next read or the encoding.
      void keepsItsBytes(
        Uint8List Function() read, [
        Uint8List Function()? encoded,
      ]) {
        final returned = read();
        final original = Uint8List.fromList(returned);
        final copy = encoded == null ? null : Uint8List.fromList(encoded());
        returned.fillRange(0, returned.length, 0);
        expect(read(), original);
        if (copy != null) expect(encoded!(), copy);
      }

      keepsItsBytes(
        () => agreement.publicKey.bytes,
        () => agreement.publicKey.toSpki(),
      );
      keepsItsBytes(
        () => ecdsaPair.publicKey.bytes,
        () => ecdsaPair.publicKey.toSpki(),
      );
      keepsItsBytes(
        () => ed25519Pair.publicKey.bytes,
        () => ed25519Pair.publicKey.toSpki(),
      );
      keepsItsBytes(
        () => rsaPair.publicKey.bytes,
        () => rsaPair.publicKey.toSpki(),
      );
      keepsItsBytes(() => oaep.publicKey.bytes, () => oaep.publicKey.toSpki());
      keepsItsBytes(() => kem.publicKey.bytes);
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
    final key = rsa.DecryptingKey.generate(
      rsa.OaepAlgorithm.sha256,
      rsa.KeySize.rsa2048,
    );
    final label = ascii('label');
    final encrypting = rsa.EncryptingKey(
      rsa.OaepAlgorithm.sha256,
      key.publicKey.bytes,
    );
    expect(encrypting.maxMessageLength, 256 - 2 * 32 - 2);
    final ciphertext = encrypting.encrypt(ascii('hello'), label: label);
    expect(key.decrypt(ciphertext, label: label), ascii('hello'));
    expect(() => key.decrypt(ciphertext), throwsRind(RindError.decryptFailed));
    expect(
      () => encrypting.encrypt(Uint8List(encrypting.maxMessageLength + 1)),
      throwsRind(RindError.wrongLength),
    );

    final spki = key.publicKey.toSpki();
    final fromSpki = rsa.EncryptingKey.fromSpki(rsa.OaepAlgorithm.sha256, spki);
    expect(fromSpki.bytes, key.publicKey.bytes);
    final (:n, :e) = rsaComponents(key.publicKey.bytes);
    final fromComponents = rsa.EncryptingKey.fromComponents(
      rsa.OaepAlgorithm.sha256,
      n: n,
      e: e,
    );
    expect(fromComponents.toSpki(), spki);
    final reloaded = rsa.DecryptingKey.fromPkcs8(
      rsa.OaepAlgorithm.sha256,
      key.toPkcs8(),
    );
    expect(reloaded.decrypt(fromComponents.encrypt(ascii('hi'))), ascii('hi'));
    expect(reloaded.decrypt(fromSpki.encrypt(ascii('hi'))), ascii('hi'));

    final legacy = rsa.DecryptingKey.fromPkcs8(rsa.oaepSha1, key.toPkcs8());
    expect(legacy.decrypt(legacy.publicKey.encrypt(ascii('hi'))), ascii('hi'));
  });

  test('RSA-OAEP encrypting keys refuse another encoding', () {
    final key = rsa.DecryptingKey.generate(
      rsa.OaepAlgorithm.sha256,
      rsa.KeySize.rsa2048,
    );
    final pkcs1 = key.publicKey.bytes;
    final spki = key.publicKey.toSpki();
    for (final der in [spki, Uint8List(0), pkcs1.sublist(1)]) {
      expect(
        () => rsa.EncryptingKey(rsa.OaepAlgorithm.sha256, der),
        throwsRind(RindError.keyRejected),
      );
    }
    for (final der in [pkcs1, spki.sublist(1)]) {
      expect(
        () => rsa.EncryptingKey.fromSpki(rsa.OaepAlgorithm.sha256, der),
        throwsRind(RindError.keyRejected),
      );
    }
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
  Uint8List unsigned(Uint8List integer) =>
      integer.length > 1 && integer[0] == 0 ? integer.sublist(1) : integer;
  final [n, e] = derSequence(der);
  return (n: unsigned(n), e: unsigned(e));
}

/// The contents of each element of the DER SEQUENCE [der].
List<Uint8List> derSequence(Uint8List der) {
  var at = 0;
  (int, Uint8List) element(Uint8List bytes) {
    final tag = bytes[at++];
    var length = bytes[at++];
    if (length >= 0x80) {
      final count = length & 0x7f;
      length = 0;
      for (var i = 0; i < count; i++) {
        length = length << 8 | bytes[at++];
      }
    }
    at += length;
    return (tag, bytes.sublist(at - length, at));
  }

  final (tag, contents) = element(der);
  expect((tag, at), (0x30, der.length));
  at = 0;
  return [for (; at < contents.length;) element(contents).$2];
}

/// A DER element of [tag] around [contents], shorter than 256 bytes.
Uint8List der(int tag, List<int> contents) => Uint8List.fromList([
  tag,
  if (contents.length >= 0x80) 0x81,
  contents.length,
  ...contents,
]);

/// A non-negative [value] as a DER INTEGER.
Uint8List derInteger(BigInt value) {
  final bytes = [
    for (var v = value; v > BigInt.zero; v >>= 8)
      (v & BigInt.from(0xff)).toInt(),
  ].reversed.toList();
  return der(0x02, [if (bytes.isEmpty || bytes[0] >= 0x80) 0, ...bytes]);
}

/// The unsigned big-endian [bytes] as a number.
BigInt bigInt(Uint8List bytes) =>
    bytes.fold(BigInt.zero, (n, b) => n << 8 | BigInt.from(b));
