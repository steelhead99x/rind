# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.25.2](https://github.com/kixel-ai/rind/compare/rind-str0m-v0.25.1...rind-str0m-v0.25.2) - 2026-11-08

### Other

- updated the following local packages: rind, rind-dimpl, rind-rcgen

## [0.25.1](https://github.com/kixel-ai/rind/compare/rind-str0m-v0.25.0...rind-str0m-v0.25.1) - 2026-11-08

### Other

- updated the following local packages: rind, rind-dimpl, rind-rcgen

## [0.25.0](https://github.com/kixel-ai/rind/releases/tag/rind-str0m-v0.25.0) - 2026-11-07

### Added

- *(str0m)* rind-str0m, a str0m CryptoProvider on rind ([#467](https://github.com/kixel-ai/rind/pull/467))
- [**breaking**] rind::rand, deviation docs, and the aws-lc-rs API surface audit ([#94](https://github.com/kixel-ai/rind/pull/94))
- *(hmac)* [**breaking**] reusable HMAC keys bound to an algorithm constant ([#83](https://github.com/kixel-ai/rind/pull/83))
- *(aead)* [**breaking**] AEAD and cipher keys bound to an algorithm constant ([#75](https://github.com/kixel-ai/rind/pull/75))
- [**breaking**] digest constants replace the Hash trait ([#77](https://github.com/kixel-ai/rind/pull/77))
- *(aead)* [**breaking**] AesGcm::new refuses a bad key length ([#43](https://github.com/kixel-ai/rind/pull/43))
- [**breaking**] AEADs refuse over-long messages ([#34](https://github.com/kixel-ai/rind/pull/34))
- *(str0m)* add rind-str0m, a str0m CryptoProvider ([#17](https://github.com/kixel-ai/rind/pull/17))

### Other

- [**breaking**] delete rind-str0m ([#138](https://github.com/kixel-ai/rind/pull/138))
- ctgrind on armv7, fixing what it finds in the arm backend ([#36](https://github.com/kixel-ai/rind/pull/36))
- follow the move to kixel-ai/rind ([#50](https://github.com/kixel-ai/rind/pull/50))
- one workspace rust-version ([#33](https://github.com/kixel-ai/rind/pull/33))
