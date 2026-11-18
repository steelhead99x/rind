#!/usr/bin/env bash
# Print rind-openssl's tag if its current version is tagged and that tag's
# GitHub release lacks the libraries, or nothing.
#
# Usage: GH_TOKEN=... sh/openssl-unreleased.sh
# release-plz tags rind-openssl and creates its release when a release PR
# lands, since it never goes to crates.io. release.yml then attaches the
# libraries, SHA256SUMS last, so a release with SHA256SUMS is complete and
# one without it may be partly attached; release.yml replaces those files.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

version=$(cargo metadata --format-version 1 --no-deps --locked |
    jq -r '.packages[] | select(.name == "rind-openssl") | .version')
tag="rind-openssl-v$version"
# Exit status 2 means no such tag: this version is unreleased.
tagged=0
git ls-remote --exit-code --tags origin "refs/tags/$tag" >/dev/null || tagged=$?
case "$tagged" in
    0) ;;
    2) exit 0 ;;
    *) exit "$tagged" ;;
esac

# A tag without a release is an error: release-plz creates both.
assets=$(gh release view "$tag" --json assets --jq '.assets[].name')
grep -qxF SHA256SUMS <<<"$assets" || echo "$tag"
