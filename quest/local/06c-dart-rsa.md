# [S] Give rind-dart an RSA library in rind 0.4's shape

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/800, an RSA library has `KeyPair` and `PublicKey`. An RSA public key takes PKCS#1, is bound to no algorithm, verifies with any RSA verification algorithm whose modulus floor it meets, refusing a smaller key at `verify`, and has `modulusLength`. `RsaEncryptingKey(algorithm, der)` takes PKCS#1, with `RsaEncryptingKey.fromSpki`. The pull request stays a draft, and no release is published.

## Plan

Continue on the #800 branch. Touch `rind-dart/lib/src/rsa.dart` (the constructor today is around line 142) and any RSA types still in `rind-dart/lib/src/signature.dart`.

Success check: from `rind-dart` in the `dart` or `nix develop` shell, `dart test --name rsa` exits 0.

## Required

- [Give rind-dart an Ed25519 library in rind 0.4's shape](/quest/local/06b-dart-ed25519.md) - signatures already share one shape before RSA joins them
