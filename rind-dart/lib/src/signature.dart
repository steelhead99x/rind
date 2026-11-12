// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'bindings.dart';

/// An algorithm an [EcdsaKeyPair] signs with: a curve, a hash, and a
/// signature encoding, ASN.1 DER or fixed-length `r || s`.
enum EcdsaSigningAlgorithm {
  /// ECDSA on P-256 with SHA-256, DER-encoded.
  p256Sha256Asn1(0),

  /// ECDSA on P-256 with SHA-256, fixed-length, as JWS's ES256.
  p256Sha256Fixed(1),

  /// ECDSA on P-384 with SHA-384, DER-encoded.
  p384Sha384Asn1(2),

  /// ECDSA on P-384 with SHA-384, fixed-length, as JWS's ES384.
  p384Sha384Fixed(3),

  /// ECDSA on P-521 with SHA-512, DER-encoded.
  p521Sha512Asn1(4),

  /// ECDSA on P-521 with SHA-512, fixed-length, as JWS's ES512.
  p521Sha512Fixed(5);

  const EcdsaSigningAlgorithm(this._id);

  final int _id;
}

/// An algorithm an [RsaKeyPair] signs with: a padding and a hash.
enum RsaSigningAlgorithm {
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

  const RsaSigningAlgorithm(this._id);

  final int _id;
}

/// The modulus size of a generated RSA key.
enum RsaKeySize {
  /// A 2048-bit modulus.
  rsa2048,

  /// A 3072-bit modulus.
  rsa3072,

  /// A 4096-bit modulus.
  rsa4096,

  /// A 6144-bit modulus.
  rsa6144,

  /// An 8192-bit modulus.
  rsa8192,
}

/// An algorithm a [PublicKey] verifies with.
///
/// Each verifies what the signing algorithm of the same name signs. RSA
/// algorithms accept moduli of 2048 to 8192 bits.
final class VerificationAlgorithm {
  const VerificationAlgorithm._(this._id, this._name);

  final int _id;
  final String _name;

  /// ECDSA on P-256 with SHA-256, DER-encoded.
  static const ecdsaP256Sha256Asn1 = VerificationAlgorithm._(
    20,
    'ECDSA_P256_SHA256_ASN1',
  );

  /// ECDSA on P-256 with SHA-384, DER-encoded.
  static const ecdsaP256Sha384Asn1 = VerificationAlgorithm._(
    21,
    'ECDSA_P256_SHA384_ASN1',
  );

  /// ECDSA on P-256 with SHA-512, DER-encoded.
  static const ecdsaP256Sha512Asn1 = VerificationAlgorithm._(
    22,
    'ECDSA_P256_SHA512_ASN1',
  );

  /// ECDSA on P-384 with SHA-256, DER-encoded.
  static const ecdsaP384Sha256Asn1 = VerificationAlgorithm._(
    23,
    'ECDSA_P384_SHA256_ASN1',
  );

  /// ECDSA on P-384 with SHA-384, DER-encoded.
  static const ecdsaP384Sha384Asn1 = VerificationAlgorithm._(
    24,
    'ECDSA_P384_SHA384_ASN1',
  );

  /// ECDSA on P-384 with SHA-512, DER-encoded.
  static const ecdsaP384Sha512Asn1 = VerificationAlgorithm._(
    25,
    'ECDSA_P384_SHA512_ASN1',
  );

  /// ECDSA on P-521 with SHA-256, DER-encoded.
  static const ecdsaP521Sha256Asn1 = VerificationAlgorithm._(
    26,
    'ECDSA_P521_SHA256_ASN1',
  );

  /// ECDSA on P-521 with SHA-384, DER-encoded.
  static const ecdsaP521Sha384Asn1 = VerificationAlgorithm._(
    27,
    'ECDSA_P521_SHA384_ASN1',
  );

  /// ECDSA on P-521 with SHA-512, DER-encoded.
  static const ecdsaP521Sha512Asn1 = VerificationAlgorithm._(
    28,
    'ECDSA_P521_SHA512_ASN1',
  );

  /// ECDSA on P-256 with SHA-256, fixed-length.
  static const ecdsaP256Sha256Fixed = VerificationAlgorithm._(
    29,
    'ECDSA_P256_SHA256_FIXED',
  );

  /// ECDSA on P-384 with SHA-384, fixed-length.
  static const ecdsaP384Sha384Fixed = VerificationAlgorithm._(
    30,
    'ECDSA_P384_SHA384_FIXED',
  );

  /// ECDSA on P-521 with SHA-512, fixed-length.
  static const ecdsaP521Sha512Fixed = VerificationAlgorithm._(
    31,
    'ECDSA_P521_SHA512_FIXED',
  );

  /// Ed25519.
  static const ed25519 = VerificationAlgorithm._(32, 'ED25519');

  /// RSASSA-PKCS1-v1_5 with SHA-256.
  static const rsaPkcs1Sha256 = RsaVerificationAlgorithm._(
    0,
    'RSA_PKCS1_SHA256',
  );

  /// RSASSA-PKCS1-v1_5 with SHA-384.
  static const rsaPkcs1Sha384 = RsaVerificationAlgorithm._(
    1,
    'RSA_PKCS1_SHA384',
  );

  /// RSASSA-PKCS1-v1_5 with SHA-512.
  static const rsaPkcs1Sha512 = RsaVerificationAlgorithm._(
    2,
    'RSA_PKCS1_SHA512',
  );

  /// RSASSA-PSS with SHA-256 and a salt as long as the hash.
  static const rsaPssSha256 = RsaVerificationAlgorithm._(3, 'RSA_PSS_SHA256');

  /// RSASSA-PSS with SHA-384 and a salt as long as the hash.
  static const rsaPssSha384 = RsaVerificationAlgorithm._(4, 'RSA_PSS_SHA384');

  /// RSASSA-PSS with SHA-512 and a salt as long as the hash.
  static const rsaPssSha512 = RsaVerificationAlgorithm._(5, 'RSA_PSS_SHA512');

  /// RSASSA-PSS with SHA-256 and a salt of any length.
  static const rsaPssSha256AnySalt = RsaVerificationAlgorithm._(
    6,
    'RSA_PSS_SHA256_ANY_SALT',
  );

  /// RSASSA-PSS with SHA-384 and a salt of any length.
  static const rsaPssSha384AnySalt = RsaVerificationAlgorithm._(
    7,
    'RSA_PSS_SHA384_ANY_SALT',
  );

  /// RSASSA-PSS with SHA-512 and a salt of any length.
  static const rsaPssSha512AnySalt = RsaVerificationAlgorithm._(
    8,
    'RSA_PSS_SHA512_ANY_SALT',
  );

  @override
  String toString() => _name;
}

/// An RSA verification algorithm, which [PublicKey.fromComponents] takes.
final class RsaVerificationAlgorithm extends VerificationAlgorithm {
  const RsaVerificationAlgorithm._(super._id, super._name) : super._();
}

/// RSASSA-PKCS1-v1_5 with SHA-1, for old signatures.
const rsaPkcs1Sha1 = RsaVerificationAlgorithm._(100, 'RSA_PKCS1_SHA1');

/// RSASSA-PKCS1-v1_5 with SHA-1, for old keys of 1024 bits or more.
const rsaPkcs1Min1024Sha1 = RsaVerificationAlgorithm._(
  101,
  'RSA_PKCS1_1024_SHA1',
);

/// RSASSA-PKCS1-v1_5 with SHA-256, for old keys of 1024 bits or more.
const rsaPkcs1Min1024Sha256 = RsaVerificationAlgorithm._(
  102,
  'RSA_PKCS1_1024_SHA256',
);

/// RSASSA-PKCS1-v1_5 with SHA-512, for old keys of 1024 bits or more.
const rsaPkcs1Min1024Sha512 = RsaVerificationAlgorithm._(
  103,
  'RSA_PKCS1_1024_SHA512',
);

/// RSASSA-PKCS1-v1_5 with SHA-384, for keys of 3072 bits or more only.
const rsaPkcs1Min3072Sha384 = RsaVerificationAlgorithm._(
  104,
  'RSA_PKCS1_3072_SHA384',
);

/// A public key that verifies signatures with one algorithm.
final class PublicKey extends _Handle {
  PublicKey._(Pointer<Void> pointer) : super(pointer, _publicKeyFinalizer);

  PublicKey._parse(
    int algorithm,
    int source,
    Uint8List bytes, [
    Uint8List? exponent,
  ]) : this._(_new(algorithm, source, bytes, exponent ?? Uint8List(0)));

  static Pointer<Void> _new(
    int algorithm,
    int source,
    Uint8List bytes,
    Uint8List exponent,
  ) => _newHandle(
    (out) => _publicKeyNew(
      algorithm,
      source,
      bytes.address,
      bytes.length,
      exponent.address,
      exponent.length,
      out,
    ),
  );

  /// Parses a public key for [algorithm], refusing a malformed key before
  /// any signature arrives.
  ///
  /// ECDSA keys are X9.62 uncompressed points, RSA keys PKCS#1
  /// `RSAPublicKey` or `SubjectPublicKeyInfo` DER, and Ed25519 keys their 32
  /// bytes.
  PublicKey(VerificationAlgorithm algorithm, Uint8List bytes)
    : this._parse(algorithm._id, 0, bytes);

  /// Parses a public key for [algorithm] from its `SubjectPublicKeyInfo`,
  /// refusing one that names another algorithm or curve.
  PublicKey.fromSpki(VerificationAlgorithm algorithm, Uint8List der)
    : this._parse(algorithm._id, 1, der);

  /// Loads an RSA key from its big-endian modulus [n] and exponent [e], as a
  /// JWK carries them.
  PublicKey.fromComponents(
    RsaVerificationAlgorithm algorithm, {
    required Uint8List n,
    required Uint8List e,
  }) : this._parse(algorithm._id, 2, n, e);

  /// Checks that [signature] is the key's signature of [message], throwing
  /// [RindError.badSignature] if not.
  void verify(Uint8List message, Uint8List signature) {
    _check(
      _publicKeyVerify(
        _pointer,
        message.address,
        message.length,
        signature.address,
        signature.length,
      ),
    );
  }

  /// The key's encoding, as [PublicKey.new] takes it.
  Uint8List get bytes => _export(0);

  /// Encodes the key as a `SubjectPublicKeyInfo`.
  Uint8List toSpki() => _export(1);

  Uint8List _export(int spki) => _output(
    _exportLength,
    (out) => _publicKeyExport(_pointer, spki, out.address, out.length),
  );
}

/// An ECDSA key pair.
final class EcdsaKeyPair extends _Handle {
  EcdsaKeyPair._(
    this.algorithm,
    int source,
    Uint8List bytes, [
    Uint8List? publicKey,
  ]) : super(
         _new(algorithm, source, bytes, publicKey ?? Uint8List(0)),
         _ecdsaKeyPairFinalizer,
       );

  static Pointer<Void> _new(
    EcdsaSigningAlgorithm algorithm,
    int source,
    Uint8List bytes,
    Uint8List publicKey,
  ) => _newHandle(
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
  EcdsaKeyPair.generate(EcdsaSigningAlgorithm algorithm)
    : this._(algorithm, 0, Uint8List(0));

  /// Parses a PKCS#8 private key for [algorithm]'s curve.
  EcdsaKeyPair.fromPkcs8(EcdsaSigningAlgorithm algorithm, Uint8List der)
    : this._(algorithm, 1, der);

  /// Parses a SEC1 `ECPrivateKey` for [algorithm]'s curve.
  EcdsaKeyPair.fromSec1(EcdsaSigningAlgorithm algorithm, Uint8List der)
    : this._(algorithm, 2, der);

  /// Loads a fixed-length big-endian [scalar], refused unless [publicKey],
  /// an X9.62 point, is its public key, as a JWK's `d` and `x`/`y` carry
  /// them.
  EcdsaKeyPair.fromScalarAndPublicKey(
    EcdsaSigningAlgorithm algorithm,
    Uint8List scalar,
    Uint8List publicKey,
  ) : this._(algorithm, 3, scalar, publicKey);

  /// The algorithm the key pair signs with.
  final EcdsaSigningAlgorithm algorithm;

  /// The public key, which verifies the key pair's signatures.
  PublicKey get publicKey =>
      PublicKey._(_newHandle((out) => _keyPairPublicKey(0, _pointer, 0, out)));

  /// Signs [message].
  Uint8List sign(Uint8List message) => _output(
    _modulusLength,
    (out) => _ecdsaSign(
      _pointer,
      message.address,
      message.length,
      out.address,
      out.length,
    ),
  );

  Uint8List _export(int what) => _output(
    _exportLength,
    (out) => _ecdsaKeyPairExport(_pointer, what, out.address, out.length),
  );

  /// Encodes the private key as PKCS#8.
  Uint8List toPkcs8() => _export(1);

  /// Encodes the private key as a SEC1 `ECPrivateKey`.
  Uint8List toSec1() => _export(2);

  /// The private key's fixed-length big-endian scalar.
  Uint8List toScalar() => _export(3);

  /// Encodes the public key as a `SubjectPublicKeyInfo`.
  Uint8List toSpki() => _export(4);
}

/// An Ed25519 key pair.
final class Ed25519KeyPair extends _Handle {
  Ed25519KeyPair._(int source, Uint8List bytes, [Uint8List? publicKey])
    : super(
        _new(source, bytes, publicKey ?? Uint8List(0)),
        _ed25519KeyPairFinalizer,
      );

  static Pointer<Void> _new(int source, Uint8List bytes, Uint8List publicKey) =>
      _newHandle(
        (out) => _ed25519KeyPairNew(
          source,
          bytes.address,
          bytes.length,
          publicKey.address,
          publicKey.length,
          out,
        ),
      );

  /// Generates a random key pair.
  Ed25519KeyPair.generate() : this._(0, Uint8List(0));

  /// Parses a PKCS#8 v1 or v2 private key.
  Ed25519KeyPair.fromPkcs8(Uint8List der) : this._(1, der);

  /// Loads a key pair from its 32-byte seed.
  Ed25519KeyPair.fromSeed(Uint8List seed) : this._(2, seed);

  /// Loads a key pair from its 32-byte seed, refused unless [publicKey] is
  /// its public key.
  Ed25519KeyPair.fromSeedAndPublicKey(Uint8List seed, Uint8List publicKey)
    : this._(3, seed, publicKey);

  /// The public key, which verifies the key pair's signatures.
  PublicKey get publicKey =>
      PublicKey._(_newHandle((out) => _keyPairPublicKey(1, _pointer, 0, out)));

  /// Signs [message].
  Uint8List sign(Uint8List message) => _output(
    64,
    (out) => _ed25519Sign(
      _pointer,
      message.address,
      message.length,
      out.address,
      out.length,
    ),
  );

  Uint8List _export(int what) => _output(
    _exportLength,
    (out) => _ed25519KeyPairExport(_pointer, what, out.address, out.length),
  );

  /// Encodes the private key as PKCS#8 v2, with its public key.
  Uint8List toPkcs8() => _export(1);

  /// Encodes the private key as PKCS#8 v1, without its public key.
  Uint8List toPkcs8v1() => _export(2);

  /// The private key's 32-byte seed.
  Uint8List toSeed() => _export(3);

  /// Encodes the public key as a `SubjectPublicKeyInfo`.
  Uint8List toSpki() => _export(4);
}

/// An RSA key pair.
///
/// Generating a key and signing take milliseconds to seconds, so run them
/// off the UI isolate, as with `Isolate.run`.
final class RsaKeyPair extends _Handle {
  RsaKeyPair._(Pointer<Void> pointer) : super(pointer, _rsaKeyPairFinalizer);

  static Pointer<Void> _parse(int source, Uint8List der) => _native(
    der,
    (bytes) =>
        _newHandle((out) => _rsaKeyPairNew(source, 0, bytes, der.length, out)),
  );

  /// Generates a random key pair of [size].
  RsaKeyPair.generate(RsaKeySize size)
    : this._(
        _newHandle((out) => _rsaKeyPairNew(0, size.index, nullptr, 0, out)),
      );

  /// Parses a PKCS#8 private key.
  RsaKeyPair.fromPkcs8(Uint8List der) : this._(_parse(1, der));

  /// Parses a PKCS#1 `RSAPrivateKey`.
  RsaKeyPair.fromPkcs1(Uint8List der) : this._(_parse(2, der));

  /// The public key, which verifies the key pair's signatures made with
  /// [algorithm].
  PublicKey publicKey(RsaSigningAlgorithm algorithm) => PublicKey._(
    _newHandle((out) => _keyPairPublicKey(2, _pointer, algorithm._id, out)),
  );

  /// Signs [message] with RSASSA-PSS.
  ///
  /// [hash] is 0 for SHA-256, 1 for SHA-384, and 2 for SHA-512. [saltLength]
  /// is the salt's length in bytes.
  Uint8List signPss(int hash, int saltLength, Uint8List message) =>
      _native(message, (input) {
        return _native(Uint8List(_modulusLength), (out) {
          final len = _check(
            _rsaSignPss(
              _pointer,
              hash,
              saltLength,
              input,
              message.length,
              out,
              _modulusLength,
            ),
          );
          return Uint8List.fromList(out.asTypedList(len));
        });
      });

  /// Signs [message] with [algorithm].
  Uint8List sign(RsaSigningAlgorithm algorithm, Uint8List message) =>
      _native(message, (input) {
        return _native(Uint8List(_modulusLength), (out) {
          final len = _check(
            _rsaSign(
              _pointer,
              algorithm._id,
              input,
              message.length,
              out,
              _modulusLength,
            ),
          );
          return Uint8List.fromList(out.asTypedList(len));
        });
      });

  Uint8List _export(int what) => _output(
    _exportLength,
    (out) => _rsaKeyPairExport(_pointer, what, out.address, out.length),
  );

  /// Encodes the private key as PKCS#8.
  Uint8List toPkcs8() => _export(1);

  /// Encodes the public key as a `SubjectPublicKeyInfo`.
  Uint8List toSpki() => _export(4);
}
