# [S] Point rind_cryptography internals at the new rind-dart API

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/800, rind_cryptography's internals use the new rind-dart calls, and `dart test` in `rind-dart/cryptography` passes. rind_cryptography keeps the `cryptography` package's API exactly. The pull request stays a draft, and no release is published.

## Plan

Continue on the #800 branch. Touch `rind-dart/cryptography/lib/src/signature.dart` and `rind-dart/cryptography/lib/src/rsa.dart`, plus `rind-dart/cryptography/test/` only if a call site forces it.

Success check: from `rind-dart/cryptography` in the `dart` or `nix develop` shell, `dart test` exits 0.

## Required

- [Move rind-dart tests, examples, and the benchmark to the new libraries](/quest/local/06e-dart-tests-examples.md) - rind-dart's public API is stable enough for the adapter to move
