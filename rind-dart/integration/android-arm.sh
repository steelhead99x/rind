#!/usr/bin/env bash
# Runs the integration test as an armv7 release build on the running Android
# emulator, under its ARM translation, in which Flutter's debug JIT crashes.
# Release builds leave out integration_test's plugin, so the result comes from
# the test reporter's log rather than from flutter drive.
# See UPSTREAM.md, "Flutter's debug JIT crashes under the Android emulator's
# ARM translation".
#
# Usage: rind-dart/integration/android-arm.sh
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"
flutter build apk --release --target-platform android-arm -t integration_test/rind_test.dart
adb install -r build/app/outputs/flutter-apk/app-release.apk
adb logcat -c
adb shell am start -n com.example.rind_integration/.MainActivity

# The reporter's summary or the app's crash ends the run; a hang fails after
# ten minutes, with the log still dumped below.
result=$(timeout 600 grep -m1 -E "All tests passed!|Some tests failed|Fatal signal" \
    <(adb logcat -v raw flutter:I libc:F "*:S") || echo "no test result before timeout")
adb logcat -d -v raw flutter:I libc:F DEBUG:F "*:S"
[[ $result == *'All tests passed!'* ]]
