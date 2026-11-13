# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.14.3](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.14.2...rind-rcgen-v0.14.3) - 2026-11-08

### Other

- updated the following local packages: rind

## [0.14.2](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.14.1...rind-rcgen-v0.14.2) - 2026-11-08

### Other

- updated the following local packages: rind

## [0.14.1](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.14.0...rind-rcgen-v0.14.1) - 2026-11-07

### Other

- updated the following local packages: rind

## [0.14.0](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.14...rind-rcgen-v0.14.0) - 2026-11-07

### Added

- *(rind-rcgen)* key_identifier() fills in key identifiers as rcgen does ([#452](https://github.com/kixel-ai/rind/pull/452))
- *(rind-rcgen)* check() and serial_number() so users need no direct rind dependency ([#451](https://github.com/kixel-ai/rind/pull/451))
- [**breaking**] each adapter's version matches the upstream it adapts ([#440](https://github.com/kixel-ai/rind/pull/440))

### Other

- *(release)* ship rind as 0.2.1, not 0.3.0 ([#457](https://github.com/kixel-ai/rind/pull/457))

## [0.1.14](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.13...rind-rcgen-v0.1.14) - 2026-11-06

### Other

- updated the following local packages: rind

## [0.1.13](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.12...rind-rcgen-v0.1.13) - 2026-11-05

### Other

- add rind logos and credit upstream projects ([#313](https://github.com/kixel-ai/rind/pull/313))

## [0.1.12](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.11...rind-rcgen-v0.1.12) - 2026-11-03

### Other

- updated the following local packages: rind

## [0.1.11](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.10...rind-rcgen-v0.1.11) - 2026-11-03

### Other

- updated the following local packages: rind

## [0.1.10](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.9...rind-rcgen-v0.1.10) - 2026-11-02

### Other

- updated the following local packages: rind

## [0.1.9](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.8...rind-rcgen-v0.1.9) - 2026-11-02

### Other

- updated the following local packages: rind

## [0.1.8](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.7...rind-rcgen-v0.1.8) - 2026-11-02

### Other

- updated the following local packages: rind

## [0.1.7](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.6...rind-rcgen-v0.1.7) - 2026-11-02

### Other

- updated the following local packages: rind

## [0.1.6](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.5...rind-rcgen-v0.1.6) - 2026-11-02

### Other

- updated the following local packages: rind

## [0.1.5](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.4...rind-rcgen-v0.1.5) - 2026-11-01

### Other

- updated the following local packages: rind

## [0.1.4](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.3...rind-rcgen-v0.1.4) - 2026-11-01

### Other

- updated the following local packages: rind

## [0.1.3](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.2...rind-rcgen-v0.1.3) - 2026-11-01

### Other

- updated the following local packages: rind

## [0.1.2](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.1...rind-rcgen-v0.1.2) - 2026-11-01

### Other

- updated the following local packages: rind

## [0.1.1](https://github.com/kixel-ai/rind/compare/rind-rcgen-v0.1.0...rind-rcgen-v0.1.1) - 2026-11-01

### Other

- updated the following local packages: rind

## [0.1.0](https://github.com/kixel-ai/rind/releases/tag/rind-rcgen-v0.1.0) - 2026-10-31

### Added

- [**breaking**] adapters mirror their upstreams and refuse unsupported CPUs at setup ([#143](https://github.com/kixel-ai/rind/pull/143))
- *(signature)* [**breaking**] one PublicKey, sign and verify constants, owned encodings, RSA key checks ([#140](https://github.com/kixel-ai/rind/pull/140))
- [**breaking**] rind::rand, deviation docs, and the aws-lc-rs API surface audit ([#94](https://github.com/kixel-ai/rind/pull/94))
- [**breaking**] signature key pairs bound to algorithm constants ([#89](https://github.com/kixel-ai/rind/pull/89))
- [**breaking**] agreement and kem modules with algorithm constants ([#79](https://github.com/kixel-ai/rind/pull/79))
- *(rcgen)* add rind-rcgen, an ECDSA P-256 SigningKey for rcgen ([#10](https://github.com/kixel-ai/rind/pull/10))

### Other

- attribute every algorithm's source and license ([#88](https://github.com/kixel-ai/rind/pull/88))
- follow the move to kixel-ai/rind ([#50](https://github.com/kixel-ai/rind/pull/50))
- *(cranelift)* build doctests with Cranelift and run the rcgen example ([#37](https://github.com/kixel-ai/rind/pull/37))
- one workspace rust-version ([#33](https://github.com/kixel-ai/rind/pull/33))
- ctgrind the adapter crates' secret paths ([#19](https://github.com/kixel-ai/rind/pull/19))
