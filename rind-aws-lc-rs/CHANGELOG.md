# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Fixed

- `PublicKey::modulus_len` is `ring-io` only, as in aws-lc-rs 1.19.0. `KeyPair::public_modulus_len` reads the modulus bytes, so a build without `ring-io` still compiles.

## [1.0.2](https://github.com/moq-dev/rind/compare/rind-aws-lc-rs-v1.0.1...rind-aws-lc-rs-v1.0.2) - 2026-11-08

### Other

- updated the following local packages: rind

## [1.0.1](https://github.com/moq-dev/rind/compare/rind-aws-lc-rs-v1.0.0...rind-aws-lc-rs-v1.0.1) - 2026-11-08

### Other

- updated the following local packages: rind

## [1.0.0](https://github.com/moq-dev/rind/releases/tag/rind-aws-lc-rs-v1.0.0) - 2026-11-07

### Added

- *(aws-lc-rs)* rind-aws-lc-rs offers aws-lc-rs 1.x's API backed by rind ([#465](https://github.com/moq-dev/rind/pull/465))
