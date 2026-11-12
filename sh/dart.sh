#!/usr/bin/env bash
# Lint and test rind-dart's Dart package, whose tests build the crate through
# its build hook, or apply its formatter and fixes. Runs in the `dart` shell.
#
# Usage: sh/dart.sh check|fix
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../rind-dart"
dart pub get
case "${1:-}" in
    check)
        dart format --output=none --set-exit-if-changed .
        dart analyze --fatal-infos
        dart test
        ;;
    fix)
        dart fix --apply
        dart format .
        ;;
    *)
        echo "usage: sh/dart.sh check|fix" >&2
        exit 2
        ;;
esac
