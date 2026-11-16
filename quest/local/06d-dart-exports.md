# [XS] Export rind-dart's per-algorithm libraries

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/800, ECDSA, Ed25519, and RSA are imported as `package:rind/ecdsa.dart`, `package:rind/ed25519.dart`, and `package:rind/rsa.dart`, and `package:rind/rind.dart` re-exports that same shape.

## Plan

Continue on the #800 branch. Touch `rind-dart/lib/rind.dart` and add `rind-dart/lib/ecdsa.dart`, `ed25519.dart`, and `rsa.dart` as the public library entry points. Do not change README examples here; that is the docs step.

Success check: from `rind-dart`, `dart analyze --fatal-infos lib/ecdsa.dart lib/ed25519.dart lib/rsa.dart lib/rind.dart` exits 0.

## Required

- [Give rind-dart an RSA library in rind 0.4's shape](/quest/local/06c-dart-rsa.md) - all three libraries exist before they are exported
