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

/// An algorithm a [KeyPair] signs with: a curve, a hash, and a signature
/// encoding, ASN.1 DER or fixed-length `r || s`.
enum SigningAlgorithm {
  /// ECDSA on P-256 with SHA-256, DER-encoded.
  p256Sha256Asn1(0, VerificationAlgorithm.p256Sha256Asn1),

  /// ECDSA on P-256 with SHA-256, fixed-length, as JWS's ES256.
  p256Sha256Fixed(1, VerificationAlgorithm.p256Sha256Fixed),

  /// ECDSA on P-384 with SHA-384, DER-encoded.
  p384Sha384Asn1(2, VerificationAlgorithm.p384Sha384Asn1),

  /// ECDSA on P-384 with SHA-384, fixed-length, as JWS's ES384.
  p384Sha384Fixed(3, VerificationAlgorithm.p384Sha384Fixed),

  /// ECDSA on P-521 with SHA-512, DER-encoded.
  p521Sha512Asn1(4, VerificationAlgorithm.p521Sha512Asn1),

  /// ECDSA on P-521 with SHA-512, fixed-length, as JWS's ES512.
  p521Sha512Fixed(5, VerificationAlgorithm.p521Sha512Fixed);

  const SigningAlgorithm(this._id, this._verification);

  final int _id;

  // The verification algorithm of the same curve, hash, and encoding.
  final VerificationAlgorithm _verification;

  @override
  String toString() => 'ecdsa.SigningAlgorithm.$name';
}

/// An algorithm a [PublicKey] verifies with: a curve, a hash, and a
/// signature encoding.
///
/// A value verifies what the [SigningAlgorithm] of the same name signs.
/// The other hashes verify a signature over that hash; no signer here
/// produces one.
enum VerificationAlgorithm {
  /// ECDSA on P-256 with SHA-256, DER-encoded.
  p256Sha256Asn1(0),

  /// ECDSA on P-256 with SHA-384, DER-encoded.
  p256Sha384Asn1(1),

  /// ECDSA on P-256 with SHA-512, DER-encoded.
  p256Sha512Asn1(2),

  /// ECDSA on P-384 with SHA-256, DER-encoded.
  p384Sha256Asn1(3),

  /// ECDSA on P-384 with SHA-384, DER-encoded.
  p384Sha384Asn1(4),

  /// ECDSA on P-384 with SHA-512, DER-encoded.
  p384Sha512Asn1(5),

  /// ECDSA on P-521 with SHA-256, DER-encoded.
  p521Sha256Asn1(6),

  /// ECDSA on P-521 with SHA-384, DER-encoded.
  p521Sha384Asn1(7),

  /// ECDSA on P-521 with SHA-512, DER-encoded.
  p521Sha512Asn1(8),

  /// ECDSA on P-256 with SHA-256, fixed-length.
  p256Sha256Fixed(9),

  /// ECDSA on P-384 with SHA-384, fixed-length.
  p384Sha384Fixed(10),

  /// ECDSA on P-521 with SHA-512, fixed-length.
  p521Sha512Fixed(11);

  const VerificationAlgorithm(this._id);

  final int _id;

  @override
  String toString() => 'ecdsa.VerificationAlgorithm.$name';
}

/// An ECDSA public key, bound to the one algorithm it verifies with.
final class PublicKey extends Handle {
  PublicKey._(this.algorithm, Pointer<Void> pointer)
    : super(pointer, _ecdsaPublicKeyFinalizer);

  PublicKey._parse(VerificationAlgorithm algorithm, int spki, Uint8List bytes)
    : this._(
        algorithm,
        newHandle(
          (out) => _ecdsaPublicKeyNew(
            algorithm._id,
            spki,
            bytes.address,
            bytes.length,
            out,
          ),
        ),
      );

  /// Parses an X9.62 uncompressed [point] for [algorithm], throwing
  /// [RindError.keyRejected] for a malformed one, a compressed one, or one
  /// off the curve.
  PublicKey(VerificationAlgorithm algorithm, Uint8List point)
    : this._parse(algorithm, 0, point);

  /// Parses a `SubjectPublicKeyInfo` for [algorithm], throwing
  /// [RindError.keyRejected] for a malformed one or one naming another
  /// algorithm or curve.
  PublicKey.fromSpki(VerificationAlgorithm algorithm, Uint8List der)
    : this._parse(algorithm, 1, der);

  /// The algorithm the key verifies with.
  final VerificationAlgorithm algorithm;

  /// Checks that [signature] is the key's signature of [message], throwing
  /// [RindError.badSignature] if not.
  void verify(Uint8List message, Uint8List signature) {
    check(
      _ecdsaPublicKeyVerify(
        pointer,
        message.address,
        message.length,
        signature.address,
        signature.length,
      ),
    );
  }

  /// The key's X9.62 uncompressed point, as [PublicKey.new] takes it.
  Uint8List get bytes => _export(0);

  /// Encodes the key as a `SubjectPublicKeyInfo`.
  Uint8List toSpki() => _export(1);

  Uint8List _export(int spki) => output(
    spki == 0 ? maxEcPointLength : maxEcSpkiLength,
    (out) => _ecdsaPublicKeyExport(pointer, spki, out.address, out.length),
  );
}

/// An ECDSA key pair, bound to the one algorithm it signs with.
final class KeyPair extends Handle {
  KeyPair._(this.algorithm, int source, Uint8List bytes, [Uint8List? publicKey])
    : super(
        _new(algorithm, source, bytes, publicKey ?? Uint8List(0)),
        _ecdsaKeyPairFinalizer,
      );

  static Pointer<Void> _new(
    SigningAlgorithm algorithm,
    int source,
    Uint8List bytes,
    Uint8List publicKey,
  ) => newHandle(
    (out) => _ecdsaKeyPairNew(
      algorithm._id,
      source,
      bytes.address,
      bytes.length,
      publicKey.address,
      publicKey.length,
      out,
    ),
  );

  /// Generates a random key pair for [algorithm].
  KeyPair.generate(SigningAlgorithm algorithm)
    : this._(algorithm, 0, Uint8List(0));

  /// Parses a PKCS#8 private key for [algorithm]'s curve, throwing
  /// [RindError.keyRejected] for a malformed one or one on another curve.
  KeyPair.fromPkcs8(SigningAlgorithm algorithm, Uint8List der)
    : this._(algorithm, 1, der);

  /// Parses a SEC1 `ECPrivateKey` for [algorithm]'s curve, throwing
  /// [RindError.keyRejected] for a malformed one or one on another curve.
  KeyPair.fromSec1(SigningAlgorithm algorithm, Uint8List der)
    : this._(algorithm, 2, der);

  /// Loads a fixed-length big-endian [scalar], refused unless [publicKey],
  /// an X9.62 point, is its public key, as a JWK's `d` and `x`/`y` carry
  /// them.
  KeyPair.fromScalarAndPublicKey(
    SigningAlgorithm algorithm,
    Uint8List scalar,
    Uint8List publicKey,
  ) : this._(algorithm, 3, scalar, publicKey);

  /// The algorithm the key pair signs with.
  final SigningAlgorithm algorithm;

  /// The public key, which verifies the key pair's signatures.
  late final PublicKey publicKey = PublicKey._(
    algorithm._verification,
    newHandle((out) => _ecdsaKeyPairPublicKey(pointer, out)),
  );

  /// Signs [message].
  Uint8List sign(Uint8List message) => output(
    _maxSignatureLength,
    (out) => _ecdsaSign(
      pointer,
      message.address,
      message.length,
      out.address,
      out.length,
    ),
  );

  Uint8List _export(int what) => output(
    exportLength,
    (out) => _ecdsaKeyPairExport(pointer, what, out.address, out.length),
  );

  /// Encodes the private key as PKCS#8.
  Uint8List toPkcs8() => _export(1);

  /// Encodes the private key as a SEC1 `ECPrivateKey`.
  Uint8List toSec1() => _export(2);

  /// The private key's fixed-length big-endian scalar.
  Uint8List toScalar() => _export(3);
}

// --- Native functions ---

@Native<HandleFree>(symbol: 'rind_dart_ecdsa_key_pair_free')
external void _ecdsaKeyPairFree(Pointer<Void> pair);
final _ecdsaKeyPairFinalizer = finalizer(Native.addressOf(_ecdsaKeyPairFree));

@Native<
  IntPtr Function(
    Uint32,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Pointer<Void>>,
  )
>(symbol: 'rind_dart_ecdsa_key_pair_new', isLeaf: true)
external int _ecdsaKeyPairNew(
  int algorithm,
  int source,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Uint8> publicKey,
  int publicKeyLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_ecdsa_sign', isLeaf: true)
external int _ecdsaSign(
  Pointer<Void> pair,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_ecdsa_key_pair_export',
  isLeaf: true,
)
external int _ecdsaKeyPairExport(
  Pointer<Void> pair,
  int what,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_ecdsa_key_pair_public_key',
  isLeaf: true,
)
external int _ecdsaKeyPairPublicKey(
  Pointer<Void> pair,
  Pointer<Pointer<Void>> out,
);

@Native<HandleFree>(symbol: 'rind_dart_ecdsa_public_key_free')
external void _ecdsaPublicKeyFree(Pointer<Void> key);
final _ecdsaPublicKeyFinalizer = finalizer(
  Native.addressOf(_ecdsaPublicKeyFree),
);

@Native<
  IntPtr Function(Uint32, Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)
>(symbol: 'rind_dart_ecdsa_public_key_new', isLeaf: true)
external int _ecdsaPublicKeyNew(
  int algorithm,
  int spki,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_ecdsa_public_key_verify', isLeaf: true)
external int _ecdsaPublicKeyVerify(
  Pointer<Void> key,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> signature,
  int signatureLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_ecdsa_public_key_export',
  isLeaf: true,
)
external int _ecdsaPublicKeyExport(
  Pointer<Void> key,
  int spki,
  Pointer<Uint8> out,
  int outLen,
);

// The longest ECDSA signature, a P-521 DER value: rind's `SIGNATURE_MAX_LEN`.
// A sequence length of two bytes plus two INTEGERs, each a sign byte and a
// 66-byte scalar. Fixed-length signatures are shorter.
const _maxSignatureLength = 3 + 2 * (2 + 66 + 1);
