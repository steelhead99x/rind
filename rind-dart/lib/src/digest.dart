// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'bindings.dart';

/// A hash function.
final class DigestAlgorithm {
  const DigestAlgorithm._(this._id, this.outputLength, this._name);

  final int _id;
  final String _name;

  /// The length of a digest, in bytes.
  final int outputLength;

  /// SHA-256.
  static const sha256 = DigestAlgorithm._(0, 32, 'SHA-256');

  /// SHA-384.
  static const sha384 = DigestAlgorithm._(1, 48, 'SHA-384');

  /// SHA-512.
  static const sha512 = DigestAlgorithm._(2, 64, 'SHA-512');

  /// SHA-512/256.
  static const sha512_256 = DigestAlgorithm._(3, 32, 'SHA-512/256');

  /// SHA3-256.
  static const sha3_256 = DigestAlgorithm._(4, 32, 'SHA3-256');

  /// SHA3-384.
  static const sha3_384 = DigestAlgorithm._(5, 48, 'SHA3-384');

  /// SHA3-512.
  static const sha3_512 = DigestAlgorithm._(6, 64, 'SHA3-512');

  @override
  String toString() => _name;
}

/// SHA-1, which only legacy protocols should use.
const digestSha1 = DigestAlgorithm._(100, 20, 'SHA-1');

/// MD5, which only legacy protocols should use.
const digestMd5 = DigestAlgorithm._(101, 16, 'MD5');

/// Hashes [data] with [algorithm].
Uint8List digest(DigestAlgorithm algorithm, Uint8List data) => output(
  algorithm.outputLength,
  (out) => _digest(
    algorithm._id,
    data.address,
    data.length,
    out.address,
    out.length,
  ),
);

/// A hash of a message given in parts.
final class DigestContext extends Handle {
  /// Starts hashing a message with [algorithm].
  DigestContext(this.algorithm)
    : super(
        newHandle((out) => _digestContextNew(algorithm._id, out)),
        _digestContextFinalizer,
      );

  /// The hash function.
  final DigestAlgorithm algorithm;

  /// Adds [data] to the message.
  void update(Uint8List data) {
    check(_digestContextUpdate(pointer, data.address, data.length));
  }

  /// Returns the message's digest, and starts a new message.
  Uint8List finish() => output(
    algorithm.outputLength,
    (out) => _digestContextFinish(pointer, out.address, out.length),
  );
}
