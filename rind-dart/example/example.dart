// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import 'dart:convert';
import 'dart:typed_data';

import 'package:rind/ecdsa.dart' as ecdsa;
import 'package:rind/ed25519.dart' as ed25519;
import 'package:rind/rind.dart';
import 'package:rind/rsa.dart' as rsa;

void main() {
  final key = Uint8List(32);
  fillRandom(key);

  final aead = AeadKey(AeadAlgorithm.chacha20Poly1305, key);
  // Never reuse a nonce with one key; RandomizedNonceKey picks its own.
  final nonce = Nonce.assumeUniqueForKey(Uint8List(12));
  final sealed = aead.seal(nonce, utf8.encode('hello'));
  print(utf8.decode(aead.open(nonce, sealed)));

  // Each signature algorithm has a key pair and a public key; the peer
  // parses the public key from its encoding or its SubjectPublicKeyInfo.
  final ecdsaPair = ecdsa.KeyPair.generate(
    ecdsa.SigningAlgorithm.p256Sha256Asn1,
  );
  ecdsa.PublicKey(
    ecdsa.VerificationAlgorithm.p256Sha256Asn1,
    ecdsaPair.publicKey.bytes,
  ).verify(utf8.encode('hello'), ecdsaPair.sign(utf8.encode('hello')));

  final ed25519Pair = ed25519.KeyPair.generate();
  ed25519.PublicKey.fromSpki(
    ed25519Pair.publicKey.toSpki(),
  ).verify(utf8.encode('hello'), ed25519Pair.sign(utf8.encode('hello')));

  // An RSA public key verifies with any algorithm whose modulus floor it
  // meets.
  final rsaPair = rsa.KeyPair.generate(rsa.KeySize.rsa2048);
  rsa.PublicKey(rsaPair.publicKey.bytes).verify(
    rsa.VerificationAlgorithm.pssSha256,
    utf8.encode('hello'),
    rsaPair.sign(rsa.SigningAlgorithm.pssSha256, utf8.encode('hello')),
  );

  final oaep = rsa.DecryptingKey.generate(
    rsa.OaepAlgorithm.sha256,
    rsa.KeySize.rsa2048,
  );
  final ciphertext = rsa.EncryptingKey.fromSpki(
    rsa.OaepAlgorithm.sha256,
    oaep.publicKey.toSpki(),
  ).encrypt(utf8.encode('hello'));
  print(utf8.decode(oaep.decrypt(ciphertext)));
}
