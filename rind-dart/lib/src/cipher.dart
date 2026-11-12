// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'bindings.dart';

/// AES-CBC without authentication.
///
/// CBC is unauthenticated. Send a MAC over the IV and ciphertext, or use
/// [AeadKey]. The caller applies padding and promises the IV is
/// unpredictable.
final class AesCbc {
  /// Encrypts [blocks], a whole number of 16-byte blocks, under [iv].
  static Uint8List encryptBlocks(
    Uint8List key,
    Uint8List iv,
    Uint8List blocks,
  ) => _apply(0, key, iv, blocks);

  /// Decrypts [blocks], a whole number of 16-byte blocks, under [iv].
  static Uint8List decryptBlocks(
    Uint8List key,
    Uint8List iv,
    Uint8List blocks,
  ) => _apply(1, key, iv, blocks);

  static Uint8List _apply(
    int decrypt,
    Uint8List key,
    Uint8List iv,
    Uint8List blocks,
  ) {
    final out = Uint8List.fromList(blocks);
    _check(
      _aesCbc(
        decrypt,
        key.address,
        key.length,
        iv.address,
        iv.length,
        out.address,
        out.length,
      ),
    );
    return out;
  }
}

/// AES-CTR without authentication.
///
/// Counter mode is unauthenticated, so pair it with a MAC. [counterBits] is
/// how many low bits of the 16-byte counter block count, from 1 to 128.
final class AesCtr {
  /// XORs the keystream from [counterBlock] into a copy of [data].
  static Uint8List apply(
    Uint8List key,
    Uint8List counterBlock,
    Uint8List data, {
    int counterBits = 64,
  }) {
    final out = Uint8List.fromList(data);
    _check(
      _aesCtr(
        key.address,
        key.length,
        counterBits,
        counterBlock.address,
        counterBlock.length,
        out.address,
        out.length,
      ),
    );
    return out;
  }
}

/// ChaCha20 with a 12-byte nonce and a 32-bit block counter, without Poly1305.
///
/// Use [AeadKey] for ChaCha20-Poly1305. Each call starts at a whole block.
final class ChaCha20 {
  /// XORs the keystream for [nonce], from block [counter], into a copy of
  /// [data].
  static Uint8List apply(
    Uint8List key,
    Uint8List nonce,
    Uint8List data, {
    int counter = 0,
  }) {
    final out = Uint8List.fromList(data);
    _check(
      _chacha20(
        key.address,
        key.length,
        nonce.address,
        nonce.length,
        counter,
        out.address,
        out.length,
      ),
    );
    return out;
  }
}
