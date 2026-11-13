# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.14.3](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.14.2...rind-object-store-v0.14.3) - 2026-11-08

### Other

- updated the following local packages: rind

## [0.14.2](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.14.1...rind-object-store-v0.14.2) - 2026-11-08

### Other

- updated the following local packages: rind

## [0.14.1](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.14.0...rind-object-store-v0.14.1) - 2026-11-07

### Other

- updated the following local packages: rind

## [0.14.0](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.2.0...rind-object-store-v0.14.0) - 2026-11-07

### Added

- [**breaking**] each adapter's version matches the upstream it adapts ([#440](https://github.com/kixel-ai/rind/pull/440))

### Other

- *(release)* ship rind as 0.2.1, not 0.3.0 ([#457](https://github.com/kixel-ai/rind/pull/457))

## [0.2.0](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.13...rind-object-store-v0.2.0) - 2026-11-06

### Fixed

- *(adapters)* [**breaking**] return each adapter's own MissingFeature, not rind's ([#420](https://github.com/kixel-ai/rind/pull/420))

## [0.1.13](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.12...rind-object-store-v0.1.13) - 2026-11-05

### Other

- add rind logos and credit upstream projects ([#313](https://github.com/kixel-ai/rind/pull/313))

## [0.1.12](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.11...rind-object-store-v0.1.12) - 2026-11-03

### Other

- updated the following local packages: rind

## [0.1.11](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.10...rind-object-store-v0.1.11) - 2026-11-03

### Other

- updated the following local packages: rind

## [0.1.10](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.9...rind-object-store-v0.1.10) - 2026-11-02

### Other

- updated the following local packages: rind

## [0.1.9](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.8...rind-object-store-v0.1.9) - 2026-11-02

### Other

- updated the following local packages: rind

## [0.1.8](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.7...rind-object-store-v0.1.8) - 2026-11-02

### Other

- updated the following local packages: rind

## [0.1.7](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.6...rind-object-store-v0.1.7) - 2026-11-02

### Other

- updated the following local packages: rind

## [0.1.6](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.5...rind-object-store-v0.1.6) - 2026-11-02

### Other

- updated the following local packages: rind

## [0.1.5](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.4...rind-object-store-v0.1.5) - 2026-11-01

### Other

- updated the following local packages: rind

## [0.1.4](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.3...rind-object-store-v0.1.4) - 2026-11-01

### Other

- updated the following local packages: rind

## [0.1.3](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.2...rind-object-store-v0.1.3) - 2026-11-01

### Other

- updated the following local packages: rind

## [0.1.2](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.1...rind-object-store-v0.1.2) - 2026-11-01

### Other

- updated the following local packages: rind

## [0.1.1](https://github.com/kixel-ai/rind/compare/rind-object-store-v0.1.0...rind-object-store-v0.1.1) - 2026-11-01

### Other

- updated the following local packages: rind

## [0.1.0](https://github.com/kixel-ai/rind/releases/tag/rind-object-store-v0.1.0) - 2026-10-31

### Added

- [**breaking**] adapters mirror their upstreams and refuse unsupported CPUs at setup ([#143](https://github.com/kixel-ai/rind/pull/143))
- *(signature)* [**breaking**] one PublicKey, sign and verify constants, owned encodings, RSA key checks ([#140](https://github.com/kixel-ai/rind/pull/140))
- [**breaking**] aead::Key, typed tags, legacy submodules, infallible HKDF expand ([#139](https://github.com/kixel-ai/rind/pull/139))
- [**breaking**] signature key pairs bound to algorithm constants ([#89](https://github.com/kixel-ai/rind/pull/89))
- *(hmac)* [**breaking**] reusable HMAC keys bound to an algorithm constant ([#83](https://github.com/kixel-ai/rind/pull/83))
- [**breaking**] digest constants replace the Hash trait ([#77](https://github.com/kixel-ai/rind/pull/77))
- *(object-store)* add rind-object-store ([#11](https://github.com/kixel-ai/rind/pull/11))

### Other

- attribute every algorithm's source and license ([#88](https://github.com/kixel-ai/rind/pull/88))
- follow the move to kixel-ai/rind ([#50](https://github.com/kixel-ai/rind/pull/50))
- one workspace rust-version ([#33](https://github.com/kixel-ai/rind/pull/33))
- ctgrind the adapter crates' secret paths ([#19](https://github.com/kixel-ai/rind/pull/19))
