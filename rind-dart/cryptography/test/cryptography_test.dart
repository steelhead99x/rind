// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import 'dart:typed_data';

import 'package:crypto/crypto.dart' as google;
import 'package:cryptography/cryptography.dart';
import 'package:cryptography_test/algorithms/aes_cbc.dart';
import 'package:cryptography_test/algorithms/aes_ctr.dart';
import 'package:cryptography_test/algorithms/chacha20.dart';
import 'package:cryptography_test/algorithms/ecdh.dart';
import 'package:cryptography_test/algorithms/ecdsa.dart';
import 'package:cryptography_test/algorithms/ed25519.dart';
import 'package:cryptography_test/algorithms/hkdf.dart';
import 'package:cryptography_test/algorithms/pbkdf2.dart';
import 'package:cryptography_test/algorithms/rsa_pss.dart';
import 'package:cryptography_test/algorithms/rsa_ssa_pkcs5v15.dart';
import 'package:cryptography_test/algorithms/sha256.dart';
import 'package:cryptography_test/algorithms/sha384.dart';
import 'package:cryptography_test/algorithms/sha512.dart';
import 'package:cryptography_test/algorithms/x25519.dart';
import 'package:cryptography_test/cipher.dart';
import 'package:rind_cryptography/rind_cryptography.dart';
import 'package:test/test.dart';

void main() {
  // Builders in the suite run as the tests are registered, so rind has to
  // be installed before those calls, not only in setUp.
  Cryptography.instance = const RindCryptography();
  setUp(() {
    Cryptography.instance = const RindCryptography();
  });

  test('SHA-1 of abc', () async {
    final hash = await Sha1().hash('abc'.codeUnits);
    expect(hash.bytes, [
      0xa9, 0x99, 0x3e, 0x36, 0x47, 0x06, 0x81, 0x6a, //
      0xba, 0x3e, 0x25, 0x71, 0x78, 0x50, 0xc2, 0x6c, //
      0x9c, 0xd0, 0xd8, 0x9d,
    ]);
  });

  testSha256();
  testSha384();
  testSha512();
  testAesCbc();
  testAesCtr();
  // testAesGcm also runs 1 000-cycle examples that start from a 16-byte
  // nonce. rind's AES-GCM takes 12-byte nonces only, so those examples are
  // not this backend's suite. The cipher tests cover 12-byte nonces.
  testCipher(builder: () => AesGcm.with128bits());
  testCipher(builder: () => AesGcm.with192bits());
  testCipher(builder: () => AesGcm.with256bits());
  testChacha20();
  testCipher(builder: () => Xchacha20.poly1305Aead());
  // cryptography_test's HMAC file also vectors SHA-224, which rind does not
  // implement. These are its RFC 4231 vectors for the hashes rind has.
  test('RFC 4231 HMAC', () async {
    final input = [0x48, 0x69, 0x20, 0x54, 0x68, 0x65, 0x72, 0x65];
    final key = SecretKey([
      0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, //
      0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
    ]);
    Future<void> check(Hmac hmac, List<int> expected) async {
      final mac = await hmac.calculateMac(input, secretKey: key);
      expect(mac.bytes, expected);
      final sink = await hmac.newMacSink(secretKey: key);
      sink.addSlice(input, 0, input.length ~/ 2, false);
      sink.addSlice(input, input.length ~/ 2, input.length, true);
      expect((await sink.mac()).bytes, expected);
    }

    await check(Hmac.sha256(), [
      0xb0, 0x34, 0x4c, 0x61, 0xd8, 0xdb, 0x38, 0x53, 0x5c, 0xa8, 0xaf, 0xce, 0xaf, 0x0b, 0xf1, 0x2b, //
      0x88, 0x1d, 0xc2, 0x00, 0xc9, 0x83, 0x3d, 0xa7, 0x26, 0xe9, 0x37, 0x6c, 0x2e, 0x32, 0xcf, 0xf7,
    ]);
    await check(Hmac.sha384(), [
      0xaf, 0xd0, 0x39, 0x44, 0xd8, 0x48, 0x95, 0x62, 0x6b, 0x08, 0x25, 0xf4, 0xab, 0x46, 0x90, 0x7f, //
      0x15, 0xf9, 0xda, 0xdb, 0xe4, 0x10, 0x1e, 0xc6, 0x82, 0xaa, 0x03, 0x4c, 0x7c, 0xeb, 0xc5, 0x9c, //
      0xfa, 0xea, 0x9e, 0xa9, 0x07, 0x6e, 0xde, 0x7f, 0x4a, 0xf1, 0x52, 0xe8, 0xb2, 0xfa, 0x9c, 0xb6,
    ]);
    for (var n = 0; n < 80; n++) {
      final data = Uint8List.fromList([for (var i = 0; i < n; i++) i]);
      final key = Uint8List.fromList([for (var i = 0; i < n + 1; i++) 255 - (i & 255)]);
      final mac = await Hmac.sha256().calculateMac(data, secretKey: SecretKey(key));
      expect(mac.bytes, google.Hmac(google.sha256, key).convert(data).bytes, reason: 'length $n');
    }

    await check(Hmac.sha512(), [
      0x87, 0xaa, 0x7c, 0xde, 0xa5, 0xef, 0x61, 0x9d, 0x4f, 0xf0, 0xb4, 0x24, 0x1a, 0x1d, 0x6c, 0xb0, //
      0x23, 0x79, 0xf4, 0xe2, 0xce, 0x4e, 0xc2, 0x78, 0x7a, 0xd0, 0xb3, 0x05, 0x45, 0xe1, 0x7c, 0xde, //
      0xda, 0xa8, 0x33, 0xb7, 0xd6, 0xb8, 0xa7, 0x02, 0x03, 0x8b, 0x27, 0x4e, 0xae, 0xa3, 0xf4, 0xe4, //
      0xbe, 0x9d, 0x91, 0x4e, 0xeb, 0x61, 0xf1, 0x70, 0x2e, 0x69, 0x6c, 0x20, 0x3a, 0x12, 0x68, 0x54,
    ]);
  });
  testHkdf();
  testPbkdf2();
  testEcdh();
  testX25519();
  testEcdsa();
  testEd25519();
  testRsaPss();
  testRsaSsaPkcs5v1();

  test('algorithms rind lacks throw UnsupportedError', () {
    expect(() => Blake2b(), throwsUnsupportedError);
    expect(() => Blake2s(), throwsUnsupportedError);
    expect(() => Sha224(), throwsUnsupportedError);
    expect(() => Poly1305(), throwsUnsupportedError);
    expect(() => Hchacha20(), throwsUnsupportedError);
    expect(
      () => Argon2id(memory: 8, parallelism: 1, iterations: 1, hashLength: 32),
      throwsUnsupportedError,
    );
    expect(
      () => Xchacha20(macAlgorithm: MacAlgorithm.empty),
      throwsUnsupportedError,
    );
  });
}
