// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Natives resolve against the one code asset `hook/build.dart` registers.
// The default would be this library's URI, which is not registered.
@DefaultAsset(nativeAssetId)
library;

import 'dart:ffi';
import 'dart:typed_data';

import 'error.dart';
import 'handle.dart';
import 'status.dart';

/// An Ed25519 public key.
final class PublicKey extends Handle {
  PublicKey._(Pointer<Void> pointer)
    : super(pointer, _ed25519PublicKeyFinalizer);

  PublicKey._parse(int spki, Uint8List bytes)
    : this._(
        newHandle(
          (out) => _ed25519PublicKeyNew(spki, bytes.address, bytes.length, out),
        ),
      );

  /// Parses a key's 32 [bytes], throwing [RindError.keyRejected] for
  /// another length, a point off the curve, or one of small order.
  PublicKey(Uint8List bytes) : this._parse(0, bytes);

  /// Parses a `SubjectPublicKeyInfo`, throwing [RindError.keyRejected] for a
  /// malformed one or one naming another algorithm.
  PublicKey.fromSpki(Uint8List der) : this._parse(1, der);

  /// Checks that [signature] is the key's signature of [message], throwing
  /// [RindError.badSignature] if not.
  void verify(Uint8List message, Uint8List signature) {
    check(
      _ed25519PublicKeyVerify(
        pointer,
        message.address,
        message.length,
        signature.address,
        signature.length,
      ),
    );
  }

  /// The key's 32 bytes, as [PublicKey.new] takes them.
  Uint8List get bytes => _export(0);

  /// Encodes the key as a `SubjectPublicKeyInfo`.
  Uint8List toSpki() => _export(1);

  Uint8List _export(int spki) => output(
    spki == 0 ? _rawPublicKeyLength : _spkiLength,
    (out) => _ed25519PublicKeyExport(pointer, spki, out.address, out.length),
  );
}

/// An Ed25519 key pair.
final class KeyPair extends Handle {
  KeyPair._(int source, Uint8List bytes, [Uint8List? publicKey])
    : super(
        _new(source, bytes, publicKey ?? Uint8List(0)),
        _ed25519KeyPairFinalizer,
      );

  static Pointer<Void> _new(int source, Uint8List bytes, Uint8List publicKey) =>
      newHandle(
        (out) => _ed25519KeyPairNew(
          source,
          bytes.address,
          bytes.length,
          publicKey.address,
          publicKey.length,
          out,
        ),
      );

  /// Generates a random key pair.
  KeyPair.generate() : this._(0, Uint8List(0));

  /// Parses a PKCS#8 v1 or v2 private key, throwing [RindError.keyRejected]
  /// for a malformed one.
  KeyPair.fromPkcs8(Uint8List der) : this._(1, der);

  /// Loads a key pair from its 32-byte seed.
  KeyPair.fromSeed(Uint8List seed) : this._(2, seed);

  /// Loads a key pair from its 32-byte seed, refused unless [publicKey] is
  /// its public key.
  KeyPair.fromSeedAndPublicKey(Uint8List seed, Uint8List publicKey)
    : this._(3, seed, publicKey);

  /// The public key, which verifies the key pair's signatures.
  late final PublicKey publicKey = PublicKey._(
    newHandle((out) => _ed25519KeyPairPublicKey(pointer, out)),
  );

  /// Signs [message].
  Uint8List sign(Uint8List message) => output(
    64,
    (out) => _ed25519Sign(
      pointer,
      message.address,
      message.length,
      out.address,
      out.length,
    ),
  );

  Uint8List _export(int what) => output(
    exportLength,
    (out) => _ed25519KeyPairExport(pointer, what, out.address, out.length),
  );

  /// Encodes the private key as PKCS#8 v2, with its public key.
  Uint8List toPkcs8() => _export(1);

  /// Encodes the private key as PKCS#8 v1, without its public key.
  Uint8List toPkcs8v1() => _export(2);

  /// The private key's 32-byte seed.
  Uint8List toSeed() => _export(3);
}

// --- Native functions ---

@Native<HandleFree>(symbol: 'rind_dart_ed25519_key_pair_free')
external void _ed25519KeyPairFree(Pointer<Void> pair);
final _ed25519KeyPairFinalizer = finalizer(
  Native.addressOf(_ed25519KeyPairFree),
);

@Native<
  IntPtr Function(
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Pointer<Void>>,
  )
>(symbol: 'rind_dart_ed25519_key_pair_new', isLeaf: true)
external int _ed25519KeyPairNew(
  int source,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Uint8> publicKey,
  int publicKeyLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_ed25519_sign', isLeaf: true)
external int _ed25519Sign(
  Pointer<Void> pair,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_ed25519_key_pair_export',
  isLeaf: true,
)
external int _ed25519KeyPairExport(
  Pointer<Void> pair,
  int what,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_ed25519_key_pair_public_key',
  isLeaf: true,
)
external int _ed25519KeyPairPublicKey(
  Pointer<Void> pair,
  Pointer<Pointer<Void>> out,
);

@Native<HandleFree>(symbol: 'rind_dart_ed25519_public_key_free')
external void _ed25519PublicKeyFree(Pointer<Void> key);
final _ed25519PublicKeyFinalizer = finalizer(
  Native.addressOf(_ed25519PublicKeyFree),
);

@Native<IntPtr Function(Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_ed25519_public_key_new',
  isLeaf: true,
)
external int _ed25519PublicKeyNew(
  int spki,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_ed25519_public_key_verify', isLeaf: true)
external int _ed25519PublicKeyVerify(
  Pointer<Void> key,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> signature,
  int signatureLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_ed25519_public_key_export',
  isLeaf: true,
)
external int _ed25519PublicKeyExport(
  Pointer<Void> key,
  int spki,
  Pointer<Uint8> out,
  int outLen,
);

// Ed25519's public key is 32 bytes. Its SubjectPublicKeyInfo is 44: a
// 12-byte AlgorithmIdentifier for id-Ed25519 and a BIT STRING of those
// 32 bytes.
const _rawPublicKeyLength = 32;
const _spkiLength = 44;
