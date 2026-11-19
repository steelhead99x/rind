// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

library;

/// Why a rind call failed, one kind per kind of call, as rind's `Error`.
enum RindError {
  /// An input or output of fixed length, such as a key, a nonce, or a
  /// derived key, was another length.
  wrongLength,

  /// A private, public, or peer's key was refused, for any reason including
  /// its length; [RindException.reason] says why.
  keyRejected,

  /// A signature, MAC tag, or PBKDF2 output did not verify.
  badSignature,

  /// An AEAD ciphertext, its tag, or its associated data did not
  /// authenticate, or an RSA-OAEP ciphertext did not decrypt.
  decryptFailed,

  /// The system random source failed.
  rngFailed,

  /// Values compared in constant time were not equal.
  notEqual,

  /// An internal consistency check failed, from a hardware fault or a rind
  /// bug, which the caller cannot fix.
  fault,

  /// A call was given an algorithm it does not take.
  unsupported,
}

/// A failed rind call.
final class RindException implements Exception {
  /// Makes the exception for [error], with the [reason] a refused key gives.
  const RindException(this.error, [this.reason]);

  /// What failed.
  final RindError error;

  /// Why a key was refused, for [RindError.keyRejected].
  final String? reason;

  @override
  String toString() => reason == null
      ? 'RindException: ${error.name}'
      : 'RindException: ${error.name}: $reason';
}
