// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'bindings.dart';

/// A key agreement algorithm.
enum AgreementAlgorithm {
  /// X25519 (RFC 7748).
  x25519(0, 32),

  /// ECDH on P-256.
  ecdhP256(1, 32),

  /// ECDH on P-384.
  ecdhP384(2, 48),

  /// ECDH on P-521.
  ecdhP521(3, 66);

  const AgreementAlgorithm(this._id, this._secretLength);

  final int _id;
  final int _secretLength;
}

/// A private key for key agreement.
final class AgreementPrivateKey extends Handle {
  AgreementPrivateKey._(this.algorithm, int source, Uint8List bytes)
    : super(
        newHandle(
          (out) => _agreementPrivateKeyNew(
            algorithm._id,
            source,
            bytes.address,
            bytes.length,
            out,
          ),
        ),
        _agreementPrivateKeyFinalizer,
      );

  /// Generates a random key for [algorithm].
  AgreementPrivateKey.generate(AgreementAlgorithm algorithm)
    : this._(algorithm, 0, Uint8List(0));

  /// Loads a fixed-length big-endian scalar, or X25519's 32 bytes, as a
  /// JWK's `d` carries it.
  AgreementPrivateKey.fromScalar(AgreementAlgorithm algorithm, Uint8List scalar)
    : this._(algorithm, 1, scalar);

  /// Parses a PKCS#8 private key for [algorithm].
  AgreementPrivateKey.fromPkcs8(AgreementAlgorithm algorithm, Uint8List der)
    : this._(algorithm, 2, der);

  /// Parses a SEC1 `ECPrivateKey` for a NIST curve [algorithm].
  AgreementPrivateKey.fromSec1(AgreementAlgorithm algorithm, Uint8List der)
    : this._(algorithm, 3, der);

  /// The algorithm the key is for.
  final AgreementAlgorithm algorithm;

  Uint8List _export(int what) => output(
    what == 0 ? maxEcPointLength : exportLength,
    (out) => _agreementPrivateKeyExport(pointer, what, out.address, out.length),
  );

  /// The public key to send to the peer.
  late final AgreementPublicKey publicKey = AgreementPublicKey._(
    algorithm,
    _export(0),
  );

  /// Agrees on a shared secret with [peer], the peer's public key bytes as
  /// [AgreementPublicKey.new] parses them, throwing [RindError.keyRejected]
  /// for a key it refuses.
  Uint8List agree(Uint8List peer) => output(
    algorithm._secretLength,
    (out) => _agreementAgree(
      pointer,
      peer.address,
      peer.length,
      out.address,
      out.length,
    ),
  );

  /// Encodes the key as PKCS#8.
  Uint8List toPkcs8() => _export(1);

  /// The key's big-endian scalar, or X25519's 32 bytes.
  Uint8List toScalar() => _export(2);
}

/// A public key for key agreement.
final class AgreementPublicKey {
  AgreementPublicKey._(this.algorithm, this._bytes);

  /// Parses a peer's public key for [algorithm]: X25519's 32 bytes, any
  /// value, or a NIST curve's X9.62 point, uncompressed or compressed,
  /// refused off the curve.
  factory AgreementPublicKey(AgreementAlgorithm algorithm, Uint8List bytes) =>
      AgreementPublicKey._(algorithm, _parse(algorithm, 0, bytes, 0));

  /// Parses a public key for [algorithm] from its `SubjectPublicKeyInfo`.
  factory AgreementPublicKey.fromSpki(
    AgreementAlgorithm algorithm,
    Uint8List der,
  ) => AgreementPublicKey._(algorithm, _parse(algorithm, 1, der, 0));

  /// The algorithm the key is for.
  final AgreementAlgorithm algorithm;

  /// The key as [AgreementPrivateKey.agree] takes it: X25519's 32 bytes, or
  /// a NIST curve's uncompressed point.
  ///
  /// Each read is a new list. The key keeps its own copy, so changing the
  /// list a caller holds leaves the key, and [toSpki], as they were.
  Uint8List get bytes => Uint8List.fromList(_bytes);

  final Uint8List _bytes;

  /// Encodes the key as a `SubjectPublicKeyInfo`.
  Uint8List toSpki() => _parse(algorithm, 0, _bytes, 1);

  static Uint8List _parse(
    AgreementAlgorithm algorithm,
    int spki,
    Uint8List bytes,
    int export,
  ) => output(
    // X25519's 32 bytes and 44-byte SPKI fit the NIST curves' bounds.
    export == 0 ? maxEcPointLength : maxEcSpkiLength,
    (out) => _agreementPublicKey(
      algorithm._id,
      spki,
      bytes.address,
      bytes.length,
      export,
      out.address,
      out.length,
    ),
  );
}
