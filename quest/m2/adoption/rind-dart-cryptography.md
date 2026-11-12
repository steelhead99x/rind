# [M] rind as a backend for Dart's cryptography package

## Goal

A package implements the [`cryptography`](https://pub.dev/packages/cryptography)
package's `Cryptography` interface on rind, so an app opts in with one line
and its existing code runs on rind.

## Plan

- Decided with the maintainer on 2026-11-04 (see [rind for Dart](/quest/m2/adoption/rind-dart.md)).
- Algorithms rind lacks (BLAKE2, Argon2) throw `cryptography`'s unsupported
  error rather than delegating to its Dart implementation, unless the
  interface itself composes backends at setup; check when starting.
- Run `cryptography`'s own test suite against it.

## Required

- [rind for Dart and Flutter](/quest/m2/adoption/rind-dart.md) - the package this builds on
