# [S] Publish rind_cryptography to pub.dev

## Goal

[rind_cryptography](/rind-dart/cryptography/README.md), the `cryptography`
package's `Cryptography` on rind, is on pub.dev at 0.1.0, and CI publishes its
later versions as [dart-release.yml](/.github/workflows/dart-release.yml) does
rind's.

## Plan

- Its AES-CBC, AES-CTR, and ChaCha20 use rind API newer than rind 0.1.0, so
  it requires rind ^0.1.1, and publishes only once pub.dev lists rind 0.1.1.
- Decided 2026-11-18 (maintainer, /quest-complete): ✅ rind-dart's next
  release is 0.1.1 (rejected: 0.2.0), since AES-CBC, AES-CTR, and ChaCha20
  only add API.
- Decided 2026-11-24 (maintainer, /quest-run): ✅ pre-approve pushing the
  `rind-dart-v0.1.1` tag once the 0.1.1 version bump is on `main`, which
  publishes rind 0.1.1 to pub.dev through `dart-release.yml` (rejected: ask
  again when the bump lands; defer). The first publish of rind_cryptography
  0.1.0 and enabling its automated publishing stay the maintainer's.
- rind-dart 0.1.1 builds against rind 0.4's API, and its release builds the
  crate against rind from crates.io, so the tag waits for crates.io to list
  rind 0.4.0 too: until then every library build fails, as the nightly
  `dart-libraries` run does.
- Checked 2026-11-24 on https://pub.dev/packages/rind/admin: rind's
  automated publishing names `kixel-ai/rind`, tag pattern
  `rind-dart-v{{version}}`, in the `pub.dev` environment, so the 0.1.1 tag
  run can publish.
- `dart-release.yml` publishes rind_cryptography on a
  `rind-cryptography-v{{version}}` tag, staged as pub.dev receives it,
  without its `pubspec_overrides.yaml` or `hooks` user-define, tested against
  rind from pub.dev, with the run's OIDC token in the `pub.dev` environment.

## Waiting

- kixel-ai/rind: the release PR,
  [kixel-ai/rind#511](https://github.com/kixel-ai/rind/pull/511), publishes
  rind 0.4.0 to crates.io when it merges; check https://crates.io/crates/rind lists 0.4.0. Then an agent
  pushes the pre-approved `rind-dart-v0.1.1` tag at `main` and checks that
  https://pub.dev/packages/rind lists 0.1.1.
- Maintainer: once pub.dev lists rind 0.1.1, publish rind_cryptography 0.1.0
  by hand (`cd rind-dart/cryptography && rm pubspec_overrides.yaml && dart
  pub publish`), since pub.dev creates a new package only from an uploader's
  account, as it did for rind; then, on its admin page, enable automated
  publishing from kixel-ai/rind for `rind-cryptography-v{{version}}` tags in
  the `pub.dev` environment, and let that environment deploy
  `rind-cryptography-v*` tags, a change to which refs reach its GitHub App
  key that is the maintainer's to make. Done when
  https://pub.dev/packages/rind_cryptography lists 0.1.0. No workflow can
  take the first step: pub.dev's automated publishing works only for a
  package that already exists.
