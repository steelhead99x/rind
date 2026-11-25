# [M] rind for Dart takes rind 0.4's shape

## Goal

rind-dart's own API takes the shape rind 0.4 did in [kixel-ai/rind#781](https://github.com/kixel-ai/rind/pull/781): an ECDSA, an Ed25519, and an RSA library each have `KeyPair` and `PublicKey`, in place of `signature.dart`'s `EcdsaKeyPair`, `Ed25519KeyPair`, `RsaKeyPair`, and one `PublicKey` for every algorithm. rind_cryptography keeps the `cryptography` package's API exactly.

## Plan

Found by kixel-ai/rind#781, which changed only rind-dart's calls into rind and kept its Dart API (`rind-dart/lib/src/signature.dart`, `rsa.dart`).

- Signatures, as rind's modules are: a public key's constructor takes the algorithm's own encoding, `fromSpki` a `SubjectPublicKeyInfo`, and `toSpki` lives only on the public key. An RSA public key takes PKCS#1, is bound to no algorithm, and verifies with any RSA verification algorithm whose modulus floor it meets, refusing a smaller key at `verify`; it has `modulusLength`. A key pair's `publicKey` returns the same object each time.
- RSA's signing algorithms become one type, as rind's `rsa::SigningAlgorithm` is: the `RsaSigningAlgorithm` enum, and `RsaPssSigningAlgorithm` with the `RsaSigningScheme` that joins them, which [kixel-ai/rind#961](https://github.com/kixel-ai/rind/pull/961) added without breaking 0.1, fold into one class whose PSS constructors take a salt length.
- The rest of #781 that rind-dart exposes: `RsaEncryptingKey(algorithm, der)`, which takes PKCS#1 or a `SubjectPublicKeyInfo` today (`rind-dart/lib/src/rsa.dart:142`), takes PKCS#1, with `RsaEncryptingKey.fromSpki`.
- Dart names its libraries rather than modules: export them from `package:rind/rind.dart` with prefixes or as `package:rind/ecdsa.dart` and its siblings, whichever reads as one shape across all four in its README's examples.
- It is a breaking change for rind-dart alone, which is versioned apart from rind: release it as its next minor version (0.2.0 from 0.1.0), with a CHANGELOG table from each old name to its new one.
- Tests, examples, the benchmark, and the README move with it, and rind_cryptography's internals move to the new calls; its own tests and package:cryptography's upstream suite still pass unchanged.

## Related

- [Publish rind_cryptography to pub.dev](/quest/m2/adoption/rind-cryptography-release.md) - publishes the package this keeps compiling
