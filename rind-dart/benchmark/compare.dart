// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Times rind against pointycastle and the `cryptography` package's pure-Dart
// implementations, the libraries a Flutter app would otherwise use, and
// prints microseconds per operation. Run it with `dart run
// benchmark/compare.dart`, or in a Flutter app on a phone.

import 'dart:typed_data';

import 'package:cryptography/dart.dart' as cr;
import 'package:cryptography/cryptography.dart'
    as cr
    show SecretKey, SecretKeyData;
import 'package:pointycastle/export.dart' as pc;
import 'package:rind/ecdsa.dart' as ecdsa;
import 'package:rind/ed25519.dart' as ed25519;
import 'package:rind/rind.dart';

Future<void> main() async {
  final kib = Uint8List(1024);
  final packet = Uint8List(1350);
  final key = Uint8List(32);
  final nonce = Uint8List(12);
  final message = Uint8List(64);

  print('operation, library, µs/op');

  await bench('SHA-256 1 KiB', {
    'rind': () => digest(DigestAlgorithm.sha256, kib),
    'pointycastle': () => pc.SHA256Digest().process(kib),
    'cryptography': () => const cr.DartSha256().hashSync(kib),
  });

  final hmacKey = HmacKey(HmacAlgorithm.sha256, key);
  final cryptoHmac = cr.DartHmac.sha256();
  final cryptoKey = cr.SecretKey(key);
  await bench('HMAC-SHA256 64 B', {
    'rind': () => hmacKey.sign(message),
    'pointycastle': () => (pc.HMac(
      pc.SHA256Digest(),
      64,
    )..init(pc.KeyParameter(key))).process(message),
    'cryptography': () =>
        cryptoHmac.calculateMac(message, secretKey: cryptoKey),
  });

  final gcm = AeadKey(AeadAlgorithm.aes256Gcm, key);
  final cryptoGcm = cr.DartAesGcm.with256bits();
  await bench('AES-256-GCM seal 1350 B', {
    'rind': () => gcm.seal(Nonce.assumeUniqueForKey(nonce), packet),
    'pointycastle': () =>
        (pc.GCMBlockCipher(pc.AESEngine())..init(
              true,
              pc.AEADParameters(pc.KeyParameter(key), 128, nonce, Uint8List(0)),
            ))
            .process(packet),
    'cryptography': () => cryptoGcm.encryptSync(
      packet,
      secretKeyData: cr.SecretKeyData(key),
      nonce: nonce,
    ),
  });

  final chacha = AeadKey(AeadAlgorithm.chacha20Poly1305, key);
  final cryptoChacha = cr.DartChacha20.poly1305Aead();
  await bench('ChaCha20-Poly1305 seal 1350 B', {
    'rind': () => chacha.seal(Nonce.assumeUniqueForKey(nonce), packet),
    'pointycastle': () =>
        (pc.ChaCha20Poly1305(pc.ChaCha7539Engine(), pc.Poly1305())..init(
              true,
              pc.AEADParameters(pc.KeyParameter(key), 128, nonce, Uint8List(0)),
            ))
            .process(packet),
    'cryptography': () =>
        cryptoChacha.encrypt(packet, secretKey: cryptoKey, nonce: nonce),
  });

  final x25519 = AgreementPrivateKey.generate(AgreementAlgorithm.x25519);
  final peer = AgreementPrivateKey.generate(
    AgreementAlgorithm.x25519,
  ).publicKey;
  final cryptoX25519 = cr.DartX25519();
  final cryptoPair = await cryptoX25519.newKeyPair();
  final cryptoPeer = await (await cryptoX25519.newKeyPair()).extractPublicKey();
  await bench('X25519 agree', {
    'rind': () => x25519.agree(peer.bytes),
    'cryptography': () => cryptoX25519.sharedSecretKey(
      keyPair: cryptoPair,
      remotePublicKey: cryptoPeer,
    ),
  });

  final ed25519Pair = ed25519.KeyPair.generate();
  final cryptoEd25519 = cr.DartEd25519();
  final cryptoEdPair = await cryptoEd25519.newKeyPair();
  await bench('Ed25519 sign 64 B', {
    'rind': () => ed25519Pair.sign(message),
    'cryptography': () => cryptoEd25519.sign(message, keyPair: cryptoEdPair),
  });
  final edVerifier = ed25519Pair.publicKey;
  final edSignature = ed25519Pair.sign(message);
  final cryptoEdSignature = await cryptoEd25519.sign(
    message,
    keyPair: cryptoEdPair,
  );
  await bench('Ed25519 verify 64 B', {
    'rind': () => edVerifier.verify(message, edSignature),
    'cryptography': () =>
        cryptoEd25519.verify(message, signature: cryptoEdSignature),
  });

  final ecdsaPair = ecdsa.KeyPair.generate(
    ecdsa.SigningAlgorithm.p256Sha256Asn1,
  );
  final curve = pc.ECCurve_secp256r1();
  final pcPrivate = pc.ECPrivateKey(_bigInt(ecdsaPair.toScalar()), curve);
  final pcPublic = pc.ECPublicKey(
    curve.curve.decodePoint(ecdsaPair.publicKey.bytes),
    curve,
  );
  final random = pc.FortunaRandom()..seed(pc.KeyParameter(Uint8List(32)));
  pc.ECDSASigner signer() => pc.ECDSASigner(pc.SHA256Digest());
  await bench('ECDSA P-256 sign 64 B', {
    'rind': () => ecdsaPair.sign(message),
    'pointycastle': () =>
        (signer()..init(
              true,
              pc.ParametersWithRandom(
                pc.PrivateKeyParameter(pcPrivate),
                random,
              ),
            ))
            .generateSignature(message),
  });
  final ecdsaVerifier = ecdsaPair.publicKey;
  final ecdsaSignature = ecdsaPair.sign(message);
  final pcSignature =
      (signer()..init(
                true,
                pc.ParametersWithRandom(
                  pc.PrivateKeyParameter(pcPrivate),
                  random,
                ),
              ))
              .generateSignature(message)
          as pc.ECSignature;
  await bench('ECDSA P-256 verify 64 B', {
    'rind': () => ecdsaVerifier.verify(message, ecdsaSignature),
    'pointycastle': () =>
        (signer()..init(false, pc.PublicKeyParameter(pcPublic)))
            .verifySignature(message, pcSignature),
  });
}

BigInt _bigInt(Uint8List bytes) =>
    bytes.fold(BigInt.zero, (n, b) => n << 8 | BigInt.from(b));

/// Times each library's [operations] for about a second, after a warm-up.
Future<void> bench(
  String name,
  Map<String, Object? Function()> operations,
) async {
  final results = <String, double>{};
  for (final MapEntry(key: library, value: operation) in operations.entries) {
    Future<void> run(int n) async {
      for (var i = 0; i < n; i++) {
        final result = operation();
        if (result is Future) await result;
      }
    }

    await run(10);
    var n = 1;
    final watch = Stopwatch();
    while (true) {
      watch
        ..reset()
        ..start();
      await run(n);
      watch.stop();
      if (watch.elapsedMilliseconds > 1000) break;
      n *= 2;
    }
    results[library] = watch.elapsedMicroseconds / n;
  }
  final rind = results['rind']!;
  results.forEach((library, micros) {
    final ratio = library == 'rind'
        ? ''
        : ', ${(micros / rind).toStringAsFixed(1)}x slower';
    print('$name, $library, ${micros.toStringAsFixed(2)}$ratio');
  });
}
