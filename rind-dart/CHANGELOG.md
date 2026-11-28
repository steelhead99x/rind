## 0.2.0

- Breaking: ECDSA, Ed25519, and RSA each have a library,
  `package:rind/ecdsa.dart`, `package:rind/ed25519.dart`, and
  `package:rind/rsa.dart`, imported `as ecdsa`, `as ed25519`, and `as rsa`,
  with a `KeyPair` and a `PublicKey` of its own, as rind 0.4's `ecdsa`,
  `ed25519`, and `rsa` modules do, in place of one `PublicKey` for every
  algorithm. Those names are the classes, so `runtimeType` and the
  documentation use them. `package:rind/rind.dart` no longer exports them. A
  public key's constructor takes the algorithm's own encoding, `fromSpki` a
  `SubjectPublicKeyInfo`, and `toSpki` lives only on the public key. An RSA
  public key takes PKCS#1, is bound to no algorithm, and refuses a modulus
  below the algorithm's floor at `verify`. A signature key pair, an
  agreement private key, and an ML-KEM decapsulation key each return the
  same `publicKey` every time it is read, as does an RSA-OAEP decrypting
  key.
- `AgreementPublicKey.bytes` and `EncapsulationKey.bytes` return a new copy
  on each read, so changing a list one returned leaves the key as it was.
- Breaking: RSA-OAEP moves to `package:rind/rsa.dart` too, and
  `rsa.EncryptingKey(algorithm, der)` takes PKCS#1 only, and
  `rsa.EncryptingKey.fromSpki` a `SubjectPublicKeyInfo`.
- Breaking: RSA's SHA-1 algorithms and other modulus floors move from
  `package:rind/legacy.dart` to `package:rind/rsa_legacy.dart`, imported
  `as rsa` beside `package:rind/rsa.dart`.
- RSA-PSS with a salt length of the caller's choosing, as 0.1.1's
  `RsaPssSigningAlgorithm` is, takes this shape: `rsa.PssSigningAlgorithm`,
  which `rsa.KeyPair.sign` takes as an `rsa.SigningScheme` beside
  `rsa.SigningAlgorithm`, and `rsa.PssVerificationAlgorithm`, an
  `rsa.VerificationAlgorithm`.

| 0.1.0 | 0.2.0 |
|---|---|
| `EcdsaKeyPair` | `ecdsa.KeyPair` |
| `EcdsaSigningAlgorithm` | `ecdsa.SigningAlgorithm` |
| `Ed25519KeyPair` | `ed25519.KeyPair` |
| `RsaKeyPair` | `rsa.KeyPair` |
| `RsaSigningAlgorithm` | `rsa.SigningAlgorithm` |
| `RsaKeySize` | `rsa.KeySize` |
| `OaepAlgorithm` | `rsa.OaepAlgorithm` |
| `RsaDecryptingKey` | `rsa.DecryptingKey` |
| `RsaEncryptingKey` | `rsa.EncryptingKey` |
| `PublicKey` | `ecdsa.PublicKey`, `ed25519.PublicKey`, or `rsa.PublicKey` |
| `VerificationAlgorithm` | `ecdsa.VerificationAlgorithm` or `rsa.VerificationAlgorithm`; Ed25519 takes none |
| `VerificationAlgorithm.ecdsaP256Sha256Asn1`, and each `ecdsa…` constant | `ecdsa.VerificationAlgorithm.p256Sha256Asn1`, without `ecdsa` |
| `VerificationAlgorithm.ecdsaP256Sha256Asn1.toString()`, `ECDSA_P256_SHA256_ASN1`, and each ECDSA constant | `ecdsa.VerificationAlgorithm.p256Sha256Asn1.toString()`, `ecdsa.VerificationAlgorithm.p256Sha256Asn1` |
| `VerificationAlgorithm.rsaPkcs1Sha256.toString()`, `RSA_PKCS1_SHA256`, and each RSA constant | `rsa.VerificationAlgorithm.pkcs1Sha256.toString()`, `rsa.VerificationAlgorithm.pkcs1Sha256` |
| `EcdsaSigningAlgorithm.p256Sha256Asn1.toString()`, and each signing constant | `ecdsa.SigningAlgorithm.p256Sha256Asn1.toString()`, `ecdsa.SigningAlgorithm.p256Sha256Asn1`, and `rsa.SigningAlgorithm.pssSha256` for RSA |
| `OaepAlgorithm.sha256.toString()`, `RSA-OAEP-SHA256`, and each OAEP constant | `rsa.OaepAlgorithm.sha256.toString()`, `rsa.OaepAlgorithm.sha256` |
| `oaepSha1.toString()`, `RSA-OAEP-SHA1` | `rsa.oaepSha1.toString()`, `rsa.oaepSha1` |
| `RsaKeySize.rsa2048.toString()`, `RsaKeySize.rsa2048`, and each size | `rsa.KeySize.rsa2048.toString()`, `rsa.KeySize.rsa2048` |
| `rsaPkcs1Sha1.toString()`, `RSA_PKCS1_SHA1`, and the other legacy RSA constants | `rsa.pkcs1Sha1.toString()`, `rsa.pkcs1Sha1` |
| `VerificationAlgorithm.ed25519` | none |
| `VerificationAlgorithm.rsaPkcs1Sha256`, and each `rsa…` constant | `rsa.VerificationAlgorithm.pkcs1Sha256`, without `rsa` |
| `RsaVerificationAlgorithm`, a `VerificationAlgorithm` | `rsa.VerificationAlgorithm`, a class of its own |
| `rsaPkcs1Sha1`, `rsaPkcs1Min1024Sha1`, `rsaPkcs1Min1024Sha256`, `rsaPkcs1Min1024Sha512`, `rsaPkcs1Min3072Sha384`, from `package:rind/legacy.dart` | `rsa.pkcs1Sha1`, `rsa.pkcs1Min1024Sha1`, `rsa.pkcs1Min1024Sha256`, `rsa.pkcs1Min1024Sha512`, `rsa.pkcs1Min3072Sha384`, from `package:rind/rsa_legacy.dart` |
| `oaepSha1`, from `package:rind/legacy.dart` | `rsa.oaepSha1`, from `package:rind/rsa_legacy.dart` |
| `PublicKey(ecdsaAlgorithm, point)` | `ecdsa.PublicKey(algorithm, point)` |
| `PublicKey.fromSpki(ecdsaAlgorithm, der)` | `ecdsa.PublicKey.fromSpki(algorithm, der)` |
| `PublicKey(VerificationAlgorithm.ed25519, bytes)` | `ed25519.PublicKey(bytes)` |
| `PublicKey.fromSpki(VerificationAlgorithm.ed25519, der)` | `ed25519.PublicKey.fromSpki(der)` |
| `PublicKey(rsaAlgorithm, der)`, PKCS#1 or SPKI | `rsa.PublicKey(der)`, PKCS#1, or `rsa.PublicKey.fromSpki(der)` |
| `PublicKey.fromSpki(rsaAlgorithm, der)` | `rsa.PublicKey.fromSpki(der)` |
| `PublicKey.fromComponents(rsaAlgorithm, n: n, e: e)` | `rsa.PublicKey.fromComponents(n: n, e: e)` |
| `rsaPublicKey.verify(message, signature)` | `rsaPublicKey.verify(algorithm, message, signature)` |
| none | `rsa.PublicKey.modulusLength` |
| `EcdsaKeyPair.publicKey`, a new `PublicKey` each time | `ecdsa.KeyPair.publicKey`, the same `ecdsa.PublicKey` each time |
| `Ed25519KeyPair.publicKey`, a new `PublicKey` each time | `ed25519.KeyPair.publicKey`, the same `ed25519.PublicKey` each time |
| `RsaKeyPair.publicKey(algorithm)` | `rsa.KeyPair.publicKey`, the same `rsa.PublicKey` each time |
| `RsaDecryptingKey.publicKey`, a new `RsaEncryptingKey` each time | `rsa.DecryptingKey.publicKey`, the same `rsa.EncryptingKey` each time |
| `AgreementPrivateKey.publicKey`, a new key each time | the same `AgreementPublicKey` each time |
| `DecapsulationKey.publicKey`, a new key each time | the same `EncapsulationKey` each time |
| `AgreementPublicKey.bytes` and `EncapsulationKey.bytes`, the list the key holds | a new copy each read |
| `EcdsaKeyPair.toSpki()`, `Ed25519KeyPair.toSpki()`, `RsaKeyPair.toSpki()`, `RsaDecryptingKey.toSpki()` | `publicKey.toSpki()` |
| `RsaEncryptingKey(algorithm, der)`, PKCS#1 or SPKI | `rsa.EncryptingKey(algorithm, der)`, PKCS#1, or `rsa.EncryptingKey.fromSpki(algorithm, der)` |
| `RsaSigningScheme`, from 0.1.1 | `rsa.SigningScheme` |
| `RsaPssSigningAlgorithm.sha256(saltLength)`, from 0.1.1, and its SHA-384 and SHA-512 kin | `rsa.PssSigningAlgorithm.sha256(saltLength)` |
| `RsaVerificationAlgorithm.pssSha256(saltLength)`, from 0.1.1, and its SHA-384 and SHA-512 kin | `rsa.PssVerificationAlgorithm.sha256(saltLength)` |

## 0.1.1

- The unauthenticated ciphers: AES-CBC (`AesCbcEncryptingKey`,
  `AesCbcDecryptingKey`, `CbcIv`), AES-CTR (`AesCtr`), and ChaCha20
  (`ChaCha20`), sized by `CipherAlgorithm`.
- AES-GCM under IVs of any length but zero (`GcmKey`, `GcmIv`), and RSA-PSS
  with a salt length of the caller's choosing (`RsaPssSigningAlgorithm`, which
  `RsaKeyPair.sign` and `RsaKeyPair.publicKey` now take as an
  `RsaSigningScheme`, and `RsaVerificationAlgorithm.pssSha256` and its
  SHA-384 and SHA-512 kin).
- rind wipes a key's native memory when Dart frees the key.
- No call throws `UnsupportedError` for a missing CPU feature: rind runs on
  every CPU of each target it supports.
- An RSA `PublicKey` whose modulus is below its algorithm's floor parses, and
  `verify` throws `RindError.keyRejected`.

## 0.1.0

- rind's AEADs, digests, HMAC, HKDF, PBKDF2, key agreement, signatures,
  ML-KEM-768, and RSA-OAEP, through a prebuilt library the build hook
  downloads and checks against its pinned SHA-256, or built from source with
  the `build_from_source` user-define.
