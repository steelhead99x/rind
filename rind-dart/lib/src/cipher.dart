// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'bindings.dart';

// Unauthenticated ciphers, for protocols that specify one alongside their own
// integrity protection. Prefer an AEAD unless a protocol requires one of
// these.

/// An AES key size, which fixes the key length a key must have.
enum CipherAlgorithm {
  /// AES with a 16-byte key.
  aes128(0, 16),

  /// AES with a 24-byte key.
  aes192(1, 24),

  /// AES with a 32-byte key.
  aes256(2, 32);

  const CipherAlgorithm(this._id, this.keyLength);

  final int _id;

  /// The length of a key, in bytes.
  final int keyLength;
}

/// A CBC IV that encrypts one message: random, or one the caller promises an
/// attacker cannot predict.
final class CbcIv {
  /// Draws an IV from the system's secure random source.
  CbcIv.random() : bytes = Uint8List(16) {
    fillRandom(bytes);
  }

  /// Takes [bytes], which the caller promises an attacker cannot predict:
  /// never a constant, zero, or counter. Throws [RindError.wrongLength]
  /// unless it is 16 bytes.
  CbcIv.assumeUnpredictable(Uint8List bytes)
    : bytes = bytes.length == 16
          ? Uint8List.fromList(bytes)
          : throw const RindException(RindError.wrongLength);

  /// The IV's bytes, which the receiver needs to decrypt.
  final Uint8List bytes;
}

/// An AES key that encrypts in CBC mode.
///
/// CBC is unauthenticated, so anyone who can alter a ciphertext and learn
/// whether it decrypted can decrypt it: Vaudenay's padding oracle needs only
/// that error, however it surfaces. Send a MAC over the IV and ciphertext
/// with each message, or use [AeadKey] instead.
final class AesCbcEncryptingKey extends _Handle {
  /// Expands [key] for [algorithm], throwing [RindError.wrongLength] unless
  /// it is [CipherAlgorithm.keyLength] bytes.
  AesCbcEncryptingKey(CipherAlgorithm algorithm, Uint8List key)
    : super(
        _newHandle(
          (out) => _aesCbcEncryptingKeyNew(
            algorithm._id,
            key.address,
            key.length,
            out,
          ),
        ),
        _aesCbcEncryptingKeyFinalizer,
      );

  /// Pads [plaintext] with PKCS#7, 1 to 16 bytes each holding the count, and
  /// returns it encrypted under [iv].
  Uint8List encrypt(CbcIv iv, Uint8List plaintext) =>
      _encrypt(iv, plaintext, plaintext.length ~/ 16 * 16 + 16, 1);

  /// Returns [plaintext] encrypted under [iv], without padding, throwing
  /// [RindError.wrongLength] unless it is a whole number of 16-byte blocks.
  Uint8List encryptBlocks(CbcIv iv, Uint8List plaintext) =>
      _encrypt(iv, plaintext, plaintext.length, 0);

  Uint8List _encrypt(CbcIv iv, Uint8List plaintext, int length, int pad) {
    final inOut = Uint8List(length)..setAll(0, plaintext);
    _check(
      _aesCbcEncrypt(
        _pointer,
        iv.bytes.address,
        iv.bytes.length,
        pad,
        inOut.address,
        inOut.length,
        plaintext.length,
      ),
    );
    return inOut;
  }
}

/// An AES key that decrypts in CBC mode.
///
/// Decryption is unauthenticated: check the MAC over the IV and ciphertext
/// before decrypting, and never let a sender learn that decryption failed,
/// or the error is a padding oracle. See [AesCbcEncryptingKey].
final class AesCbcDecryptingKey extends _Handle {
  /// Expands [key] for [algorithm], throwing [RindError.wrongLength] unless
  /// it is [CipherAlgorithm.keyLength] bytes.
  AesCbcDecryptingKey(CipherAlgorithm algorithm, Uint8List key)
    : super(
        _newHandle(
          (out) => _aesCbcDecryptingKeyNew(
            algorithm._id,
            key.address,
            key.length,
            out,
          ),
        ),
        _aesCbcDecryptingKeyFinalizer,
      );

  /// Decrypts [ciphertext] under the 16-byte [iv], checks and removes its
  /// PKCS#7 padding in constant time, and returns the plaintext.
  ///
  /// Throws [RindError.decryptFailed] if [ciphertext] is empty, is not a
  /// whole number of 16-byte blocks, or has malformed padding.
  Uint8List decrypt(Uint8List iv, Uint8List ciphertext) =>
      _decrypt(iv, ciphertext, 1);

  /// Returns [ciphertext] decrypted under the 16-byte [iv], without padding,
  /// throwing [RindError.decryptFailed] unless it is a whole number of
  /// 16-byte blocks.
  Uint8List decryptBlocks(Uint8List iv, Uint8List ciphertext) =>
      _decrypt(iv, ciphertext, 0);

  Uint8List _decrypt(Uint8List iv, Uint8List ciphertext, int pad) {
    final inOut = Uint8List.fromList(ciphertext);
    final len = _check(
      _aesCbcDecrypt(
        _pointer,
        iv.address,
        iv.length,
        pad,
        inOut.address,
        inOut.length,
      ),
    );
    return Uint8List.sublistView(inOut, 0, len);
  }
}

/// An AES key in counter mode.
final class AesCtr extends _Handle {
  /// Expands [key] for [algorithm], counting over the rightmost
  /// [counterBits] bits of each counter block.
  ///
  /// Throws [RindError.wrongLength] unless [key] is
  /// [CipherAlgorithm.keyLength] bytes and [counterBits] is 1 to 128, and
  /// [RangeError] for a [counterBits] that is negative or over 32 bits.
  AesCtr(CipherAlgorithm algorithm, Uint8List key, int counterBits)
    : super(
        _newHandle(
          (out) => _aesCtrNew(
            algorithm._id,
            key.address,
            key.length,
            _uint32(counterBits, 'counterBits'),
            out,
          ),
        ),
        _aesCtrFinalizer,
      );

  /// Returns [data] XORed with the keystream from the 16-byte
  /// [counterBlock]; encryption and decryption are the same operation.
  ///
  /// Throws [RindError.wrongLength] if [data] needs more than
  /// 2^counterBits blocks: the counter would wrap onto a block already used,
  /// repeating keystream.
  Uint8List applyKeystream(Uint8List counterBlock, Uint8List data) {
    final inOut = Uint8List.fromList(data);
    _check(
      _aesCtrApplyKeystream(
        _pointer,
        counterBlock.address,
        counterBlock.length,
        inOut.address,
        inOut.length,
      ),
    );
    return inOut;
  }
}

/// A ChaCha20 key, for the bare stream cipher with a 96-bit nonce and a
/// 32-bit block counter (RFC 8439).
final class ChaCha20 extends _Handle {
  /// Makes a key from 32 bytes of key material.
  ChaCha20(Uint8List key)
    : super(
        _newHandle((out) => _chacha20New(key.address, key.length, out)),
        _chacha20Finalizer,
      );

  /// Returns [data] XORed with the keystream for the 12-byte [nonce],
  /// starting at block [counter]; encryption and decryption are the same
  /// operation.
  ///
  /// Throws [RindError.wrongLength] if [data] needs more blocks than remain
  /// before the counter wraps, since wrapping would repeat keystream, and
  /// [RangeError] unless [counter] fits in 32 bits.
  Uint8List applyKeystream(Uint8List nonce, int counter, Uint8List data) {
    final inOut = Uint8List.fromList(data);
    _check(
      _chacha20ApplyKeystream(
        _pointer,
        nonce.address,
        nonce.length,
        _uint32(counter, 'counter'),
        inOut.address,
        inOut.length,
      ),
    );
    return inOut;
  }
}

// [value], refused if a native Uint32 would truncate it.
int _uint32(int value, String name) {
  if (value < 0 || value > 0xffffffff) {
    throw RangeError.range(value, 0, 0xffffffff, name);
  }
  return value;
}
