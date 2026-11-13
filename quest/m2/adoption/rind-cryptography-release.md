# [S] Publish rind_cryptography to pub.dev

## Goal

[rind_cryptography](/rind-dart/cryptography/README.md), the `cryptography`
package's `Cryptography` on rind, is on pub.dev at 0.1.0, and CI publishes its
later versions as [dart-release.yml](/.github/workflows/dart-release.yml) does
rind's.

## Plan

- Publish from `rind-dart/cryptography` without its `pubspec_overrides.yaml`,
  so it depends on rind 0.1.0 from pub.dev. Its `hooks` user-define reaches no
  dependent app, as rind's pubspec explains.
- Add a job that publishes it on a `rind-cryptography-v{{version}}` tag
  through pub.dev's automated publishing, with the run's OIDC token in the
  `pub.dev` environment and no stored credential, after checking the tag
  matches the pubspec's version. It needs no prebuilt libraries: rind's
  release carries them.

## Waiting

- Maintainer: publish 0.1.0 by hand (`cd rind-dart/cryptography && rm
  pubspec_overrides.yaml && dart pub publish`), since pub.dev creates a new
  package only from an uploader's account, as it did for rind; then, on its
  admin page, enable automated publishing from kixel-ai/rind for
  `rind-cryptography-v{{version}}` tags in the `pub.dev` environment, and let
  that environment deploy those tags. Done when
  https://pub.dev/packages/rind_cryptography lists 0.1.0. No workflow can
  take the first step: pub.dev's automated publishing works only for a
  package that already exists.
