// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'bindings.dart';

/// An AEAD algorithm, which fixes the key length a key must have.
enum AeadAlgorithm {
  /// AES-128-GCM.
  aes128Gcm(0, 16),

  /// AES-192-GCM.
  aes192Gcm(1, 24),

  /// AES-256-GCM.
  aes256Gcm(2, 32),

  /// ChaCha20-Poly1305 (RFC 8439).
  chacha20Poly1305(3, 32);

  const AeadAlgorithm(this._id, this.keyLength);

  final int _id;

  /// The length of a key, in bytes.
  final int keyLength;

  /// The length of a nonce, in bytes.
  int get nonceLength => 12;

  /// The length of a tag, in bytes.
  int get tagLength => 16;
}

/// A 96-bit nonce the caller promises never to use twice with one key.
final class Nonce {
  /// Takes [bytes], which must be 12 bytes long and never repeat under one
  /// key: derive them from protocol state that never repeats, such as a
  /// record sequence number, or use [RandomizedNonceKey].
  Nonce.assumeUniqueForKey(Uint8List bytes)
    : _bytes = Uint8List.fromList(bytes);

  final Uint8List _bytes;
}

/// An AEAD key, which seals with the caller's nonces.
///
/// Sealing two messages with one nonce and key loses confidentiality and
/// lets anyone forge messages.
final class AeadKey extends _Handle {
  /// Expands [key] for [algorithm], throwing [RindError.wrongLength] unless
  /// it is [AeadAlgorithm.keyLength] bytes.
  AeadKey(AeadAlgorithm algorithm, Uint8List key)
    : super(
        _newHandle(
          (out) => _aeadKeyNew(algorithm._id, key.address, key.length, out),
        ),
        _aeadKeyFinalizer,
      );

  /// Encrypts [plaintext] and returns it followed by its 16-byte tag.
  Uint8List seal(Nonce nonce, Uint8List plaintext, {Uint8List? aad}) {
    aad ??= Uint8List(0);
    final inOut = Uint8List(plaintext.length + 16)..setAll(0, plaintext);
    _check(
      _aeadSeal(
        _pointer,
        nonce._bytes.address,
        nonce._bytes.length,
        aad.address,
        aad.length,
        inOut.address,
        inOut.length,
      ),
    );
    return inOut;
  }

  /// Decrypts and verifies [sealed], a ciphertext followed by its tag, and
  /// returns the plaintext, throwing [RindError.decryptFailed] if it does
  /// not verify.
  Uint8List open(Nonce nonce, Uint8List sealed, {Uint8List? aad}) {
    aad ??= Uint8List(0);
    final inOut = Uint8List.fromList(sealed);
    final len = _check(
      _aeadOpen(
        _pointer,
        nonce._bytes.address,
        nonce._bytes.length,
        aad.address,
        aad.length,
        inOut.address,
        inOut.length,
      ),
    );
    return Uint8List.sublistView(inOut, 0, len);
  }
}

/// An XChaCha20-Poly1305 key that picks a random 192-bit nonce for every
/// seal, long enough that random nonces never collide in practice.
final class RandomizedNonceKey extends _Handle {
  /// Makes a key from 32 bytes of key material.
  RandomizedNonceKey(Uint8List key)
    : super(
        _newHandle(
          (out) => _randomizedNonceKeyNew(key.address, key.length, out),
        ),
        _randomizedNonceKeyFinalizer,
      );

  /// Encrypts [plaintext] under a fresh random nonce, returning the nonce,
  /// which the opener needs, and the ciphertext followed by its tag.
  ({Uint8List nonce, Uint8List sealed}) seal(
    Uint8List plaintext, {
    Uint8List? aad,
  }) {
    aad ??= Uint8List(0);
    final inOut = Uint8List(plaintext.length + 16)..setAll(0, plaintext);
    final nonce = Uint8List(24);
    _check(
      _randomizedNonceKeySeal(
        _pointer,
        aad.address,
        aad.length,
        inOut.address,
        inOut.length,
        nonce.address,
      ),
    );
    return (nonce: nonce, sealed: inOut);
  }

  /// Encrypts [plaintext] under [nonce], which must be 24 bytes and never
  /// repeat with this key, and returns the ciphertext followed by its tag.
  ///
  /// Repeating a nonce loses confidentiality and lets anyone forge messages.
  /// [seal] picks a random nonce instead.
  Uint8List sealWithNonce(
    Uint8List nonce,
    Uint8List plaintext, {
    Uint8List? aad,
  }) {
    aad ??= Uint8List(0);
    final inOut = Uint8List(plaintext.length + 16)..setAll(0, plaintext);
    _check(
      _randomizedNonceKeySealWithNonce(
        _pointer,
        nonce.address,
        nonce.length,
        aad.address,
        aad.length,
        inOut.address,
        inOut.length,
      ),
    );
    return inOut;
  }

  /// Decrypts and verifies [sealed], sealed under [nonce], and returns the
  /// plaintext, throwing [RindError.decryptFailed] if it does not verify.
  Uint8List open(Uint8List nonce, Uint8List sealed, {Uint8List? aad}) {
    aad ??= Uint8List(0);
    final inOut = Uint8List.fromList(sealed);
    final len = _check(
      _randomizedNonceKeyOpen(
        _pointer,
        nonce.address,
        nonce.length,
        aad.address,
        aad.length,
        inOut.address,
        inOut.length,
      ),
    );
    return Uint8List.sublistView(inOut, 0, len);
  }
}
