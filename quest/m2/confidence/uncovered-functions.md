# [S] Every published function runs under a test

## Goal

The nightly coverage gate allows no function in the published code that never runs but those `admin/coverage.allow` gives a lasting reason for. Each one it listed gets a test that reaches it, or is deleted as dead code. A function only another architecture compiles counts as covered when that architecture's run reaches it.

## Plan

Planned with the maintainer on 2026-11-12, with the coverage report's goal: no percentage target, just no unrun function left without a reason.

[kixel-ai/rind#862](https://github.com/kixel-ai/rind/pull/862) reached every function the report listed in `rind` and the Rust adapters, other than those kixel-ai/rind#792's adapter tests reach and those TESTING.md's Coverage section lists with a reason. The nightly `coverage` workflow's gate now fails on a published function no tier runs, unless `admin/coverage.allow` lists it. What remains is the bindings that pyrind's and rind for Dart's 0.4 reshapes rewrite, which that file allows until then. Testing their current code would only conflict with those rewrites.

- pyrind: `rsa::DecryptingKey::from_pkcs1` and `to_pkcs8`, `rsa::EncryptingKey::from_components` and `to_spki`, and `signature::Ed25519KeyPair::from_seed_and_public_key` and `to_spki`, or whatever their reshaped successors are.
- rind for Dart: `PublicKey::to_spki` and the two closures in `rind_dart_public_key_new`, or their successors.
- Then remove their entries from `admin/coverage.allow`, which a dispatched `coverage` run's gate checks.

## Required

- [pyrind takes rind 0.4's shape](/quest/m2/api/pyrind-shape.md) - rewrites the pyrind functions left unrun
- [rind for Dart takes rind 0.4's shape](/quest/m2/api/rind-dart-shape.md) - rewrites the rind-dart functions left unrun
