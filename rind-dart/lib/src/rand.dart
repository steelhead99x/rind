// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'bindings.dart';

/// Fills [out] with random bytes from the system's secure random source.
void fillRandom(Uint8List out) {
  check(_randFill(out.address, out.length));
}

/// Checks in constant time that [a] and [b] hold the same bytes, throwing
/// [RindError.wrongLength] if their lengths differ and [RindError.notEqual]
/// if their contents do.
void constantTimeVerify(Uint8List a, Uint8List b) {
  check(_constantTimeVerify(a.address, a.length, b.address, b.length));
}

/// Whether rind runs AES on CPU instructions. Where it doesn't,
/// ChaCha20-Poly1305 is faster than AES-GCM, so a protocol that negotiates
/// between them should prefer it.
bool hasAesHardware() => check(_hasAesHardware()) == 1;
