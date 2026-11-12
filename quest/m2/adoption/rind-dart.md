# [S] rind for Dart and Flutter

## Goal

The `rind` package on pub.dev brings rind to Dart and Flutter through FFI,
with rind's own API, built by Dart's native-asset hooks for Android (aarch64,
armv7, x86_64), iOS, macOS, Linux, and Windows, where pure-Dart crypto
(pointycastle, `cryptography`'s Dart backend) is up to 100x slower.

## Plan

Decided with the maintainer on 2026-11-04, in a planning interview:

- Two packages, as rind and rind-ring are: this one with rind's own API, and
  [a `cryptography` backend](/quest/m2/adoption/rind-dart-cryptography.md) on
  top ✅ / one package.
- It lives in this workspace as a `rind-dart` crate with its Dart package,
  released by this repository's CI ✅ / a separate repository.

The package is in `rind-dart/`: its build hook downloads the prebuilt library
its release pins, or compiles the crate with cargo when asked, and
`.github/workflows/dart-release.yml` releases it when a `rind-dart-v<version>`
tag is pushed, staged by `sh/dart-package.sh` against rind from crates.io,
with the libraries `dart-libraries.yml` builds attached to the tag's GitHub
release. What remains is the first release and a phone's benchmark numbers in
its README.

## Waiting

- Maintainer: connect an Android armv7 or aarch64 phone, where rind's lead
  is largest, to the agent host with USB or wireless debugging (Developer
  options). An agent then runs `benchmark/compare.dart`'s `main` in a
  release-mode Flutter app on it, against the published 0.1.0, and adds its
  numbers to `rind-dart/README.md`; the emulator's numbers would not
  represent a phone. Check with `adb devices`, which should list the phone
  as `device`. (Maintainer, 2026-11-11: they have an Android phone to use.)
