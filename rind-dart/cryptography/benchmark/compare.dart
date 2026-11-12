// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Times the cryptography package's API on RindCryptography against its
// pure-Dart implementation, and against rind's own API, which shows what the
// package's API costs, and prints microseconds per operation. Run it with
// `dart run benchmark/compare.dart`.

import 'dart:typed_data';

import 'package:cryptography/cryptography.dart';
import 'package:cryptography/dart.dart';
import 'package:rind/rind.dart' as rind;
import 'package:rind_cryptography/rind_cryptography.dart';

Future<void> main() async {
  final kib = Uint8List(1024);
  final packet = Uint8List(1350);
  final key = Uint8List(32);
  final secretKey = SecretKey(key);
  final nonce = Uint8List(12);
  final message = Uint8List(64);
  final rindCryptography = RindCryptography();
  final dart = DartCryptography();
  final backends = {'rind_cryptography': rindCryptography, 'dart': dart};

  print('operation, library, µs/op');

  await bench('SHA-256 1 KiB', {
    for (final MapEntry(:key, :value) in backends.entries)
      key: () => value.sha256().hash(kib),
    'rind': () => rind.digest(rind.DigestAlgorithm.sha256, kib),
  });

  final hmacKey = rind.HmacKey(rind.HmacAlgorithm.sha256, key);
  await bench('HMAC-SHA256 64 B', {
    for (final MapEntry(:key, :value) in backends.entries)
      key: () => value
          .hmac(value.sha256())
          .calculateMac(message, secretKey: secretKey),
    'rind': () => hmacKey.sign(message),
  });

  final gcm = rind.AeadKey(rind.AeadAlgorithm.aes256Gcm, key);
  await bench('AES-256-GCM seal 1350 B', {
    for (final MapEntry(:key, :value) in backends.entries)
      key: () =>
          value.aesGcm().encrypt(packet, secretKey: secretKey, nonce: nonce),
    'rind': () => gcm.seal(rind.Nonce.assumeUniqueForKey(nonce), packet),
  });

  final chacha = rind.AeadKey(rind.AeadAlgorithm.chacha20Poly1305, key);
  await bench('ChaCha20-Poly1305 seal 1350 B', {
    for (final MapEntry(:key, :value) in backends.entries)
      key: () => value.chacha20Poly1305Aead().encrypt(
        packet,
        secretKey: secretKey,
        nonce: nonce,
      ),
    'rind': () => chacha.seal(rind.Nonce.assumeUniqueForKey(nonce), packet),
  });

  final x25519Pair = await dart.x25519().newKeyPair();
  final x25519Peer = await (await dart.x25519().newKeyPair())
      .extractPublicKey();
  final x25519 = rind.AgreementPrivateKey.generate(
    rind.AgreementAlgorithm.x25519,
  );
  await bench('X25519 agree', {
    for (final MapEntry(:key, :value) in backends.entries)
      key: () => value.x25519().sharedSecretKey(
        keyPair: x25519Pair,
        remotePublicKey: x25519Peer,
      ),
    'rind': () => x25519.agree(Uint8List.fromList(x25519Peer.bytes)),
  });

  final edPair = await dart.ed25519().newKeyPair();
  final ed25519 = rind.Ed25519KeyPair.generate();
  await bench('Ed25519 sign 64 B', {
    for (final MapEntry(:key, :value) in backends.entries)
      key: () => value.ed25519().sign(message, keyPair: edPair),
    'rind': () => ed25519.sign(message),
  });

  final edSignature = await dart.ed25519().sign(message, keyPair: edPair);
  final edVerifier = ed25519.publicKey;
  final edRindSignature = ed25519.sign(message);
  await bench('Ed25519 verify 64 B', {
    for (final MapEntry(:key, :value) in backends.entries)
      key: () => value.ed25519().verify(message, signature: edSignature),
    'rind': () => edVerifier.verify(message, edRindSignature),
  });

  // The Dart implementation has no ECDSA.
  final ecdsa = rindCryptography.ecdsaP256(rindCryptography.sha256());
  final ecdsaPair = await ecdsa.newKeyPair();
  final ecdsaRind = rind.EcdsaKeyPair.generate(
    rind.EcdsaSigningAlgorithm.p256Sha256Fixed,
  );
  await bench('ECDSA P-256 sign 64 B', {
    'rind_cryptography': () => ecdsa.sign(message, keyPair: ecdsaPair),
    'rind': () => ecdsaRind.sign(message),
  });

  final ecdsaSignature = await ecdsa.sign(message, keyPair: ecdsaPair);
  final ecdsaVerifier = ecdsaRind.publicKey;
  final ecdsaRindSignature = ecdsaRind.sign(message);
  await bench('ECDSA P-256 verify 64 B', {
    'rind_cryptography': () => ecdsa.verify(message, signature: ecdsaSignature),
    'rind': () => ecdsaVerifier.verify(message, ecdsaRindSignature),
  });
}

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
  final baseline = results['rind_cryptography']!;
  results.forEach((library, micros) {
    final ratio = library == 'rind_cryptography'
        ? ''
        : ', ${(micros / baseline).toStringAsFixed(2)}x';
    print('$name, $library, ${micros.toStringAsFixed(2)}$ratio');
  });
}
