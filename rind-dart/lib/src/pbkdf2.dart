// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'bindings.dart';

/// A PBKDF2 algorithm.
final class Pbkdf2Algorithm {
  const Pbkdf2Algorithm._(this._hmac);

  final HmacAlgorithm _hmac;

  /// PBKDF2 with HMAC-SHA256.
  static const hmacSha256 = Pbkdf2Algorithm._(HmacAlgorithm.sha256);

  /// PBKDF2 with HMAC-SHA384.
  static const hmacSha384 = Pbkdf2Algorithm._(HmacAlgorithm.sha384);

  /// PBKDF2 with HMAC-SHA512.
  static const hmacSha512 = Pbkdf2Algorithm._(HmacAlgorithm.sha512);

  @override
  String toString() => 'PBKDF2-$_hmac';
}

/// PBKDF2 with HMAC-SHA1, which only legacy formats should use.
const pbkdf2HmacSha1 = Pbkdf2Algorithm._(hmacSha1);

/// A password keyed into HMAC once, which then derives or checks keys.
///
/// Deriving takes as long as its iteration count asks, so run it off the
/// UI isolate, as with `Isolate.run`.
final class Pbkdf2Secret extends Handle {
  /// Keys [algorithm] with [secret], which may be any length.
  Pbkdf2Secret(Pbkdf2Algorithm algorithm, Uint8List secret)
    : super(
        newHandle(
          (out) => _pbkdf2SecretNew(
            algorithm._hmac._id,
            secret.address,
            secret.length,
            out,
          ),
        ),
        _pbkdf2SecretFinalizer,
      );

  /// Derives a [length]-byte key from [salt] over [iterations] rounds,
  /// throwing [RindError.wrongLength] if [length] is zero or longer than
  /// PBKDF2 allows.
  Uint8List derive(int iterations, Uint8List salt, int length) {
    _checkIterations(iterations);
    return nativeCopy(salt, (saltPointer) {
      return nativeCopy(Uint8List(length), (out) {
        check(
          _pbkdf2Derive(
            pointer,
            iterations,
            saltPointer,
            salt.length,
            out,
            length,
          ),
        );
        return Uint8List.fromList(out.asTypedList(length));
      });
    });
  }

  /// Checks in constant time that [previouslyDerived] is what [derive] makes
  /// for [salt] and [iterations], throwing [RindError.badSignature] if not.
  ///
  /// Throws [RindError.wrongLength] if [previouslyDerived] is shorter than
  /// the HMAC output, which is easier to match.
  void verify(int iterations, Uint8List salt, Uint8List previouslyDerived) {
    _checkIterations(iterations);
    nativeCopy(salt, (saltPointer) {
      nativeCopy(previouslyDerived, (previous) {
        check(
          _pbkdf2Verify(
            pointer,
            iterations,
            saltPointer,
            salt.length,
            previous,
            previouslyDerived.length,
          ),
        );
      });
    });
  }

  static void _checkIterations(int iterations) {
    if (iterations < 1 || iterations > 0xffffffff) {
      throw RangeError.range(iterations, 1, 0xffffffff, 'iterations');
    }
  }
}
