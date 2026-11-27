// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Natives resolve against the one code asset `hook/build.dart` registers.
// The default would be this library's URI, which is not registered.
@DefaultAsset(nativeAssetId)
library;

import 'dart:ffi';
import 'dart:typed_data';

import 'package:ffi/ffi.dart';

import 'error.dart';
import 'handle.dart';
import 'status.dart';

/// The modulus size of a generated RSA key.
enum KeySize {
  /// A 2048-bit modulus.
  rsa2048,

  /// A 3072-bit modulus.
  rsa3072,

  /// A 4096-bit modulus.
  rsa4096,

  /// A 6144-bit modulus.
  rsa6144,

  /// An 8192-bit modulus.
  rsa8192;

  @override
  String toString() => 'rsa.KeySize.$name';
}

/// What a [KeyPair] signs with: a [SigningAlgorithm], or a
/// [PssSigningAlgorithm] of a salt length the caller picks.
sealed class SigningScheme {
  int get _id;
}

/// An algorithm a [KeyPair] signs with: a padding and a hash.
enum SigningAlgorithm implements SigningScheme {
  /// RSASSA-PKCS1-v1_5 with SHA-256.
  pkcs1Sha256(0),

  /// RSASSA-PKCS1-v1_5 with SHA-384.
  pkcs1Sha384(1),

  /// RSASSA-PKCS1-v1_5 with SHA-512.
  pkcs1Sha512(2),

  /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a salt as long as the hash.
  pssSha256(3),

  /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a salt as long as the hash.
  pssSha384(4),

  /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a salt as long as the hash.
  pssSha512(5);

  const SigningAlgorithm(this._id);

  @override
  final int _id;

  @override
  String toString() => 'rsa.SigningAlgorithm.$name';
}

/// RSASSA-PSS with a salt of [saltLength] bytes, beside the hash's length
/// that [SigningAlgorithm]'s PSS algorithms use. A signature verifies only
/// with the salt length it was made with, as the [PssVerificationAlgorithm]
/// of the same hash and length does, or with an `AnySalt`
/// [VerificationAlgorithm].
///
/// A modulus too short for the salt refuses to sign with it.
final class PssSigningAlgorithm implements SigningScheme {
  /// RSASSA-PSS with SHA-256 and MGF1-SHA-256, throwing [RangeError] unless
  /// [saltLength] is 0 to 65535.
  PssSigningAlgorithm.sha256(this.saltLength)
    : _id = _pss(3, saltLength),
      _name = 'sha256';

  /// RSASSA-PSS with SHA-384 and MGF1-SHA-384, throwing [RangeError] unless
  /// [saltLength] is 0 to 65535.
  PssSigningAlgorithm.sha384(this.saltLength)
    : _id = _pss(4, saltLength),
      _name = 'sha384';

  /// RSASSA-PSS with SHA-512 and MGF1-SHA-512, throwing [RangeError] unless
  /// [saltLength] is 0 to 65535.
  PssSigningAlgorithm.sha512(this.saltLength)
    : _id = _pss(5, saltLength),
      _name = 'sha512';

  /// The length of the salt, in bytes.
  final int saltLength;

  @override
  final int _id;

  final String _name;

  @override
  String toString() => 'rsa.PssSigningAlgorithm.$_name($saltLength)';
}

// The id of PSS with the hash of PSS id [pss] and a salt of [saltLength]
// bytes, as `rind_dart_rsa_sign` and `rind_dart_rsa_public_key_verify`
// decode it.
int _pss(int pss, int saltLength) {
  if (saltLength < 0 || saltLength > 0xffff) {
    throw RangeError.range(saltLength, 0, 0xffff, 'saltLength');
  }
  return 1 << 24 | saltLength << 8 | pss;
}

/// An algorithm a [PublicKey] verifies with: a padding, a hash, and the
/// smallest modulus it accepts.
///
/// [pkcs1Sha256], [pkcs1Sha384], [pkcs1Sha512], [pssSha256], [pssSha384],
/// and [pssSha512] verify what the [SigningAlgorithm] of the same name
/// signs. [pssSha256AnySalt], [pssSha384AnySalt], and [pssSha512AnySalt]
/// verify a PSS signature of that hash with a salt of any length, which
/// includes the salt the signer of that hash produces. These accept a
/// modulus of 2048 to 8192 bits; the algorithms in
/// `package:rind/rsa_legacy.dart` state their own floors.
final class VerificationAlgorithm {
  const VerificationAlgorithm._(this._id, this._name);

  final int _id;
  final String _name;

  /// RSASSA-PKCS1-v1_5 with SHA-256.
  static const pkcs1Sha256 = VerificationAlgorithm._(
    0,
    'rsa.VerificationAlgorithm.pkcs1Sha256',
  );

  /// RSASSA-PKCS1-v1_5 with SHA-384.
  static const pkcs1Sha384 = VerificationAlgorithm._(
    1,
    'rsa.VerificationAlgorithm.pkcs1Sha384',
  );

  /// RSASSA-PKCS1-v1_5 with SHA-512.
  static const pkcs1Sha512 = VerificationAlgorithm._(
    2,
    'rsa.VerificationAlgorithm.pkcs1Sha512',
  );

  /// RSASSA-PSS with SHA-256 and a salt as long as the hash.
  static const pssSha256 = VerificationAlgorithm._(
    3,
    'rsa.VerificationAlgorithm.pssSha256',
  );

  /// RSASSA-PSS with SHA-384 and a salt as long as the hash.
  static const pssSha384 = VerificationAlgorithm._(
    4,
    'rsa.VerificationAlgorithm.pssSha384',
  );

  /// RSASSA-PSS with SHA-512 and a salt as long as the hash.
  static const pssSha512 = VerificationAlgorithm._(
    5,
    'rsa.VerificationAlgorithm.pssSha512',
  );

  /// RSASSA-PSS with SHA-256 and a salt of any length.
  static const pssSha256AnySalt = VerificationAlgorithm._(
    6,
    'rsa.VerificationAlgorithm.pssSha256AnySalt',
  );

  /// RSASSA-PSS with SHA-384 and a salt of any length.
  static const pssSha384AnySalt = VerificationAlgorithm._(
    7,
    'rsa.VerificationAlgorithm.pssSha384AnySalt',
  );

  /// RSASSA-PSS with SHA-512 and a salt of any length.
  static const pssSha512AnySalt = VerificationAlgorithm._(
    8,
    'rsa.VerificationAlgorithm.pssSha512AnySalt',
  );

  @override
  String toString() => _name;
}

/// RSASSA-PSS with a salt of exactly [saltLength] bytes, as the
/// [PssSigningAlgorithm] of the same hash and length signs, for keys of 2048
/// to 8192 bits.
final class PssVerificationAlgorithm extends VerificationAlgorithm {
  /// RSASSA-PSS with SHA-256 and MGF1-SHA-256, throwing [RangeError] unless
  /// [saltLength] is 0 to 65535.
  PssVerificationAlgorithm.sha256(this.saltLength)
    : super._(
        _pss(3, saltLength),
        'rsa.PssVerificationAlgorithm.sha256($saltLength)',
      );

  /// RSASSA-PSS with SHA-384 and MGF1-SHA-384, throwing [RangeError] unless
  /// [saltLength] is 0 to 65535.
  PssVerificationAlgorithm.sha384(this.saltLength)
    : super._(
        _pss(4, saltLength),
        'rsa.PssVerificationAlgorithm.sha384($saltLength)',
      );

  /// RSASSA-PSS with SHA-512 and MGF1-SHA-512, throwing [RangeError] unless
  /// [saltLength] is 0 to 65535.
  PssVerificationAlgorithm.sha512(this.saltLength)
    : super._(
        _pss(5, saltLength),
        'rsa.PssVerificationAlgorithm.sha512($saltLength)',
      );

  /// The length of the salt, in bytes.
  final int saltLength;
}

/// RSASSA-PKCS1-v1_5 with SHA-1, for old signatures by keys of 2048 to 8192
/// bits.
const pkcs1Sha1 = VerificationAlgorithm._(100, 'rsa.pkcs1Sha1');

/// RSASSA-PKCS1-v1_5 with SHA-1, for old keys of 1024 to 8192 bits.
const pkcs1Min1024Sha1 = VerificationAlgorithm._(101, 'rsa.pkcs1Min1024Sha1');

/// RSASSA-PKCS1-v1_5 with SHA-256, for old keys of 1024 to 8192 bits.
const pkcs1Min1024Sha256 = VerificationAlgorithm._(
  102,
  'rsa.pkcs1Min1024Sha256',
);

/// RSASSA-PKCS1-v1_5 with SHA-512, for old keys of 1024 to 8192 bits.
const pkcs1Min1024Sha512 = VerificationAlgorithm._(
  103,
  'rsa.pkcs1Min1024Sha512',
);

/// RSASSA-PKCS1-v1_5 with SHA-384, for keys of 3072 to 8192 bits only.
const pkcs1Min3072Sha384 = VerificationAlgorithm._(
  104,
  'rsa.pkcs1Min3072Sha384',
);

/// An RSA public key, which verifies with any [VerificationAlgorithm]
/// whose modulus floor it meets.
final class PublicKey extends Handle {
  PublicKey._(Pointer<Void> pointer) : super(pointer, _rsaPublicKeyFinalizer);

  PublicKey._parse(int source, Uint8List bytes, [Uint8List? exponent])
    : this._(_new(source, bytes, exponent ?? Uint8List(0)));

  static Pointer<Void> _new(int source, Uint8List bytes, Uint8List exponent) =>
      newHandle(
        (out) => _rsaPublicKeyNew(
          source,
          bytes.address,
          bytes.length,
          exponent.address,
          exponent.length,
          out,
        ),
      );

  /// Parses a PKCS#1 `RSAPublicKey`, throwing [RindError.keyRejected] for a
  /// malformed one or a `SubjectPublicKeyInfo`, which
  /// [PublicKey.fromSpki] takes.
  PublicKey(Uint8List der) : this._parse(0, der);

  /// Parses a `SubjectPublicKeyInfo`, throwing [RindError.keyRejected] for a
  /// malformed one or one naming another algorithm.
  PublicKey.fromSpki(Uint8List der) : this._parse(1, der);

  /// Loads a key from its big-endian modulus [n] and exponent [e], as a JWK
  /// carries them, throwing [RindError.keyRejected] for a malformed one.
  PublicKey.fromComponents({required Uint8List n, required Uint8List e})
    : this._parse(2, n, e);

  /// Checks that [signature] is the key's signature of [message] under
  /// [algorithm], throwing [RindError.badSignature] if not, or
  /// [RindError.keyRejected] if the modulus is below [algorithm]'s floor.
  void verify(
    VerificationAlgorithm algorithm,
    Uint8List message,
    Uint8List signature,
  ) {
    check(
      _rsaPublicKeyVerify(
        pointer,
        algorithm._id,
        message.address,
        message.length,
        signature.address,
        signature.length,
      ),
    );
  }

  /// The modulus's length in bytes, which is also its signatures' length.
  int get modulusLength => check(_rsaPublicKeyModulusLen(pointer));

  /// The key's PKCS#1 `RSAPublicKey` encoding, as [PublicKey.new] takes
  /// it.
  Uint8List get bytes => _export(0);

  /// Encodes the key as a `SubjectPublicKeyInfo`.
  Uint8List toSpki() => _export(1);

  Uint8List _export(int spki) => output(
    _maxPublicKeyLength,
    (out) => _rsaPublicKeyExport(pointer, spki, out.address, out.length),
  );
}

/// An RSA key pair.
///
/// Generating a key and signing take milliseconds to seconds, so run them
/// off the UI isolate, as with `Isolate.run`.
final class KeyPair extends Handle {
  KeyPair._(Pointer<Void> pointer) : super(pointer, _rsaKeyPairFinalizer);

  static Pointer<Void> _parse(int source, Uint8List der) => nativeCopy(
    der,
    (bytes) =>
        newHandle((out) => _rsaKeyPairNew(source, 0, bytes, der.length, out)),
  );

  /// Generates a random key pair of [size].
  KeyPair.generate(KeySize size)
    : this._(
        newHandle((out) => _rsaKeyPairNew(0, size.index, nullptr, 0, out)),
      );

  /// Parses a PKCS#8 private key, throwing [RindError.keyRejected] for a
  /// malformed one.
  KeyPair.fromPkcs8(Uint8List der) : this._(_parse(1, der));

  /// Parses a PKCS#1 `RSAPrivateKey`, throwing [RindError.keyRejected] for a
  /// malformed one.
  KeyPair.fromPkcs1(Uint8List der) : this._(_parse(2, der));

  /// The public key, which verifies the key pair's signatures.
  late final PublicKey publicKey = PublicKey._(
    newHandle((out) => _rsaKeyPairPublicKey(pointer, out)),
  );

  /// Signs [message] with [algorithm].
  Uint8List sign(SigningScheme algorithm, Uint8List message) =>
      nativeCopy(message, (input) {
        return _modulusOut(
          (out) => _rsaSign(
            pointer,
            algorithm._id,
            input,
            message.length,
            out,
            _maxModulusLength,
          ),
        );
      });

  /// Encodes the private key as PKCS#8.
  Uint8List toPkcs8() => output(
    exportLength,
    (out) => _rsaKeyPairExport(pointer, 1, out.address, out.length),
  );
}

/// An RSA-OAEP algorithm: its hash, which MGF1 uses too.
final class OaepAlgorithm {
  const OaepAlgorithm._(this._id, this._name);

  final int _id;
  final String _name;

  /// RSA-OAEP with SHA-256.
  static const sha256 = OaepAlgorithm._(0, 'rsa.OaepAlgorithm.sha256');

  /// RSA-OAEP with SHA-384.
  static const sha384 = OaepAlgorithm._(1, 'rsa.OaepAlgorithm.sha384');

  /// RSA-OAEP with SHA-512.
  static const sha512 = OaepAlgorithm._(2, 'rsa.OaepAlgorithm.sha512');

  @override
  String toString() => _name;
}

/// RSA-OAEP with SHA-1, for protocols that still require it.
const oaepSha1 = OaepAlgorithm._(100, 'rsa.oaepSha1');

/// An RSA private key that decrypts RSA-OAEP ciphertexts.
///
/// Generating a key and decrypting take milliseconds to seconds, so run
/// them off the UI isolate, as with `Isolate.run`.
final class DecryptingKey extends Handle {
  DecryptingKey._(this.algorithm, int source, int size, Uint8List der)
    : super(
        nativeCopy(
          der,
          (bytes) => newHandle(
            (out) => _decryptingKeyNew(
              algorithm._id,
              source,
              size,
              bytes,
              der.length,
              out,
            ),
          ),
        ),
        _decryptingKeyFinalizer,
      );

  /// Generates a random key of [size] for [algorithm].
  DecryptingKey.generate(OaepAlgorithm algorithm, KeySize size)
    : this._(algorithm, 0, size.index, Uint8List(0));

  /// Parses a PKCS#8 private key for [algorithm], throwing
  /// [RindError.keyRejected] for a malformed one.
  DecryptingKey.fromPkcs8(OaepAlgorithm algorithm, Uint8List der)
    : this._(algorithm, 1, 0, der);

  /// Parses a PKCS#1 `RSAPrivateKey` for [algorithm], throwing
  /// [RindError.keyRejected] for a malformed one.
  DecryptingKey.fromPkcs1(OaepAlgorithm algorithm, Uint8List der)
    : this._(algorithm, 2, 0, der);

  /// The algorithm the key decrypts with.
  final OaepAlgorithm algorithm;

  /// The public key, which encrypts to this key.
  late final EncryptingKey publicKey = EncryptingKey._(
    algorithm,
    newHandle((out) => _decryptingKeyPublicKey(pointer, out)),
  );

  /// Decrypts [ciphertext] sealed with [label], throwing
  /// [RindError.decryptFailed] if it does not decrypt.
  Uint8List decrypt(Uint8List ciphertext, {Uint8List? label}) {
    label ??= Uint8List(0);
    return nativeCopy(ciphertext, (input) {
      return nativeCopy(label!, (labelPointer) {
        return _modulusOut(
          (out) => _decrypt(
            pointer,
            input,
            ciphertext.length,
            labelPointer,
            label!.length,
            out,
            _maxModulusLength,
          ),
        );
      });
    });
  }

  /// Encodes the private key as PKCS#8.
  Uint8List toPkcs8() => output(
    exportLength,
    (out) => _decryptingKeyExport(pointer, 1, out.address, out.length),
  );
}

/// An RSA public key that encrypts with RSA-OAEP.
final class EncryptingKey extends Handle {
  EncryptingKey._(this.algorithm, Pointer<Void> pointer)
    : super(pointer, _encryptingKeyFinalizer);

  EncryptingKey._parse(
    this.algorithm,
    int source,
    Uint8List bytes, [
    Uint8List? exponent,
  ]) : super(
         _new(algorithm, source, bytes, exponent ?? Uint8List(0)),
         _encryptingKeyFinalizer,
       );

  static Pointer<Void> _new(
    OaepAlgorithm algorithm,
    int source,
    Uint8List bytes,
    Uint8List exponent,
  ) => newHandle(
    (out) => _encryptingKeyNew(
      algorithm._id,
      source,
      bytes.address,
      bytes.length,
      exponent.address,
      exponent.length,
      out,
    ),
  );

  /// Parses a PKCS#1 `RSAPublicKey` for [algorithm], throwing
  /// [RindError.keyRejected] for a malformed one, a modulus below 2048 bits,
  /// or a `SubjectPublicKeyInfo`, which [EncryptingKey.fromSpki] takes.
  EncryptingKey(OaepAlgorithm algorithm, Uint8List der)
    : this._parse(algorithm, 0, der);

  /// Parses a `SubjectPublicKeyInfo` for [algorithm], throwing
  /// [RindError.keyRejected] for a malformed one, one naming another
  /// algorithm, or a modulus below 2048 bits.
  EncryptingKey.fromSpki(OaepAlgorithm algorithm, Uint8List der)
    : this._parse(algorithm, 1, der);

  /// Loads a key for [algorithm] from its big-endian modulus [n] and
  /// exponent [e], as a JWK carries them, throwing [RindError.keyRejected]
  /// for a malformed one or a modulus below 2048 bits.
  EncryptingKey.fromComponents(
    OaepAlgorithm algorithm, {
    required Uint8List n,
    required Uint8List e,
  }) : this._parse(algorithm, 2, n, e);

  /// The algorithm the key encrypts with.
  final OaepAlgorithm algorithm;

  /// Encrypts [message] with [label], returning a ciphertext as long as the
  /// modulus, and throwing [RindError.wrongLength] for a message longer
  /// than [maxMessageLength].
  Uint8List encrypt(Uint8List message, {Uint8List? label}) {
    label ??= Uint8List(0);
    return output(
      _maxModulusLength,
      (out) => _encrypt(
        pointer,
        message.address,
        message.length,
        label!.address,
        label.length,
        out.address,
        out.length,
      ),
    );
  }

  /// The longest message the key encrypts, in bytes.
  int get maxMessageLength => check(_encryptingKeyMaxMessageLen(pointer));

  /// The key's PKCS#1 `RSAPublicKey` encoding, as [EncryptingKey.new]
  /// takes it.
  Uint8List get bytes => _export(0);

  /// Encodes the key as a `SubjectPublicKeyInfo`.
  Uint8List toSpki() => _export(1);

  Uint8List _export(int spki) => output(
    _maxPublicKeyLength,
    (out) => _encryptingKeyExport(pointer, spki, out.address, out.length),
  );
}

// --- Native functions ---

@Native<HandleFree>(symbol: 'rind_dart_rsa_key_pair_free')
external void _rsaKeyPairFree(Pointer<Void> pair);
final _rsaKeyPairFinalizer = finalizer(Native.addressOf(_rsaKeyPairFree));

// Not a leaf call: generating a key takes up to seconds.
@Native<
  IntPtr Function(Uint32, Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)
>(symbol: 'rind_dart_rsa_key_pair_new')
external int _rsaKeyPairNew(
  int source,
  int size,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_rsa_sign')
external int _rsaSign(
  Pointer<Void> pair,
  int algorithm,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_rsa_key_pair_export',
  isLeaf: true,
)
external int _rsaKeyPairExport(
  Pointer<Void> pair,
  int what,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_rsa_key_pair_public_key',
  isLeaf: true,
)
external int _rsaKeyPairPublicKey(
  Pointer<Void> pair,
  Pointer<Pointer<Void>> out,
);

@Native<HandleFree>(symbol: 'rind_dart_rsa_public_key_free')
external void _rsaPublicKeyFree(Pointer<Void> key);
final _rsaPublicKeyFinalizer = finalizer(Native.addressOf(_rsaPublicKeyFree));

@Native<
  IntPtr Function(
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Pointer<Void>>,
  )
>(symbol: 'rind_dart_rsa_public_key_new', isLeaf: true)
external int _rsaPublicKeyNew(
  int source,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Uint8> exponent,
  int exponentLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_rsa_public_key_verify', isLeaf: true)
external int _rsaPublicKeyVerify(
  Pointer<Void> key,
  int algorithm,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> signature,
  int signatureLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_rsa_public_key_export',
  isLeaf: true,
)
external int _rsaPublicKeyExport(
  Pointer<Void> key,
  int spki,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>)>(
  symbol: 'rind_dart_rsa_public_key_modulus_len',
  isLeaf: true,
)
external int _rsaPublicKeyModulusLen(Pointer<Void> key);

@Native<HandleFree>(symbol: 'rind_dart_decrypting_key_free')
external void _decryptingKeyFree(Pointer<Void> key);
final _decryptingKeyFinalizer = finalizer(Native.addressOf(_decryptingKeyFree));

// Not a leaf call: generating a key takes up to seconds.
@Native<
  IntPtr Function(
    Uint32,
    Uint32,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Pointer<Void>>,
  )
>(symbol: 'rind_dart_decrypting_key_new')
external int _decryptingKeyNew(
  int algorithm,
  int source,
  int size,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Pointer<Void>> out,
);

@Native<IntPtr Function(Pointer<Void>, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_decrypting_key_public_key',
  isLeaf: true,
)
external int _decryptingKeyPublicKey(
  Pointer<Void> key,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_decrypt')
external int _decrypt(
  Pointer<Void> key,
  Pointer<Uint8> ciphertext,
  int ciphertextLen,
  Pointer<Uint8> label,
  int labelLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_decrypting_key_export',
  isLeaf: true,
)
external int _decryptingKeyExport(
  Pointer<Void> key,
  int what,
  Pointer<Uint8> out,
  int outLen,
);

@Native<HandleFree>(symbol: 'rind_dart_encrypting_key_free')
external void _encryptingKeyFree(Pointer<Void> key);
final _encryptingKeyFinalizer = finalizer(Native.addressOf(_encryptingKeyFree));

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
>(symbol: 'rind_dart_encrypting_key_new', isLeaf: true)
external int _encryptingKeyNew(
  int algorithm,
  int source,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Uint8> exponent,
  int exponentLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_encrypt', isLeaf: true)
external int _encrypt(
  Pointer<Void> key,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> label,
  int labelLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_encrypting_key_export',
  isLeaf: true,
)
external int _encryptingKeyExport(
  Pointer<Void> key,
  int spki,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>)>(
  symbol: 'rind_dart_encrypting_key_max_message_len',
  isLeaf: true,
)
external int _encryptingKeyMaxMessageLen(Pointer<Void> key);

// The modulus-sized output of a signature or a decryption. Zeroed: Rust
// borrows it as `&mut [u8]`, which has to already be initialized.
Uint8List _modulusOut(int Function(Pointer<Uint8> out) write) {
  final out = calloc<Uint8>(_maxModulusLength);
  try {
    final len = check(write(out));
    return Uint8List.fromList(out.asTypedList(len));
  } finally {
    calloc.free(out);
  }
}

// RSA-8192's modulus, which bounds RSA's signatures, ciphertexts, and
// plaintexts. Not a key's own modulus length.
const _maxModulusLength = 1024;

// The longest public key encoding, an RSA-8192 SubjectPublicKeyInfo. Its
// PKCS#1 `RSAPublicKey` is a 4-byte SEQUENCE header, the modulus as an
// INTEGER (a 4-byte header and a sign byte), and an exponent of at most 33
// bits, rind's limit, as a 7-byte INTEGER: the modulus and 16 bytes. The
// SubjectPublicKeyInfo adds a 4-byte SEQUENCE header, the 15-byte
// rsaEncryption AlgorithmIdentifier, and a BIT STRING's 4-byte header and
// unused-bits byte.
const _maxPublicKeyLength = _maxModulusLength + 16 + 24;
