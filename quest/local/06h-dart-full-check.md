# [S] Run rind-dart's full check, including the upstream cryptography suite

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/800, `sh/dart.sh check` exits 0, including `dart run tool/upstream_test.dart` under `rind-dart/cryptography`. The pull request stays a draft, and no release is published.

## Plan

Continue on the #800 branch. Change only what a failing command in `sh/dart.sh check` requires. Do not publish.

Success check: from the repo root, `. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && nix develop -c sh/dart.sh check` exits 0, and `gh pr view 800 --repo kixel-ai/rind --json isDraft --jq .isDraft` prints `true`.

## Required

- [Update rind-dart docs and the CHANGELOG rename table](/quest/local/06g-dart-docs-changelog.md) - docs and code are in place before the full check
