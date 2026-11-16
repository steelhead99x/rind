# [S] Give rind-dart an ECDSA library in rind 0.4's shape

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/800, an ECDSA library has `KeyPair` and `PublicKey` in place of `signature.dart`'s `EcdsaKeyPair` and a shared `PublicKey`. A public key's constructor takes the algorithm's own encoding, `fromSpki` a `SubjectPublicKeyInfo`, and `toSpki` lives only on the public key. A key pair's `publicKey` returns the same object each time. The pull request stays a draft, and no release is published.

## Plan

The work is already claimed on that upstream draft. Continue on its branch; do not open a second claim. Split ECDSA out of `rind-dart/lib/src/signature.dart` into `rind-dart/lib/src/ecdsa.dart`. Leave Ed25519, RSA, and package exports for later steps.

Settled: libraries are imported as `package:rind/ecdsa.dart` and its siblings, not only as prefixed exports from `package:rind/rind.dart`.

Success check: from `rind-dart` in the `dart` or `nix develop` shell, `dart test --name ecdsa` exits 0.

## Related

- [rind for Dart takes rind 0.4's shape](/quest/m2/api/rind-dart-shape.md) - the quest this draft implements
