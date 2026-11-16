# [XS] Update rind-dart docs and the CHANGELOG rename table

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/800, `rind-dart/README.md` and `rind-dart/CHANGELOG.md` describe the new libraries, including `package:rind/ecdsa.dart` and its siblings in the README examples, and the CHANGELOG has a table from each old name to its new one. No 0.2.0 release is published.

## Plan

Continue on the #800 branch. Touch `rind-dart/README.md` and `rind-dart/CHANGELOG.md` only. Do not publish to pub.dev.

Success check: `git grep -n package:rind/ecdsa.dart HEAD -- rind-dart/README.md` prints a match, and `git tag --list 'rind-dart-v0.2.0'` prints nothing.

## Required

- [Point rind_cryptography internals at the new rind-dart API](/quest/local/06f-dart-cryptography.md) - the API the docs describe is finished
