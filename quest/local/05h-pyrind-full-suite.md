# [S] Run pyrind's full test script, including the upstream suites

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/799, `sh/python.sh test` exits 0, including pyrind-cryptography and the pyca/cryptography, pyjwt, and joserfc suites it runs. The pull request stays a draft, and no release is published.

## Plan

Continue on the #799 branch. Change only what a failing command in `sh/python.sh test` requires. Do not publish.

Success check: from the repo root, `. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && nix develop -c sh/python.sh test` exits 0, and `gh pr view 799 --repo kixel-ai/rind --json isDraft --jq .isDraft` prints `true`.

## Required

- [Update pyrind docs and the CHANGELOG rename table](/quest/local/05g-pyrind-docs-changelog.md) - docs and code are in place before the full suite
