#!/usr/bin/env bash
# Lint and test rind-dart's Dart packages, rind and rind_cryptography, whose
# tests build the crate through rind's build hook, or apply their formatter
# and fixes. rind_cryptography's checks run the cryptography package's own
# tests on it too. Runs in the `dart` shell.
#
# Usage: sh/dart.sh check|fix
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../rind-dart"
case "${1:-}" in
    check)
        for package in . cryptography; do
            (
                cd "$package"
                dart pub get
                dart format --output=none --set-exit-if-changed .
                dart analyze --fatal-infos
                dart test
            )
        done
        (cd cryptography && dart run tool/upstream_test.dart)
        ;;
    fix)
        for package in . cryptography; do
            (
                cd "$package"
                dart pub get
                dart fix --apply
                dart format .
            )
        done
        ;;
    *)
        echo "usage: sh/dart.sh check|fix" >&2
        exit 2
        ;;
esac
