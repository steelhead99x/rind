# [S] Move rind-dart tests, examples, and the benchmark to the new libraries

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/800, `rind-dart/test/rind_test.dart`, `rind-dart/example/example.dart`, and `rind-dart/benchmark/compare.dart` use the new libraries, and `dart test` in `rind-dart` passes.

## Plan

Continue on the #800 branch. Touch those three files, and `rind-dart/test/hook_test.dart` only if it imports the old signature types.

Success check: from `rind-dart` in the `dart` or `nix develop` shell, `dart test` exits 0.

## Required

- [Export rind-dart's per-algorithm libraries](/quest/local/06d-dart-exports.md) - tests and examples import the public libraries
