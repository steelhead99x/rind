# [XS] The dart-ios job returns to Flutter's stable channel

## Goal

`build.yml`'s `dart-ios` job installs Flutter's `stable` channel again, as its other Flutter jobs do, with nothing left of the beta workaround.

## Plan

`dart-ios` runs `channel: beta` because stable 3.50.0's `flutter test` hangs on the iOS simulator when `log stream` attaches after the app logs its VM service URL ([flutter/flutter#181771](https://github.com/flutter/flutter/issues/181771)), which beta's 3.51.0-0.1.pre fixes ([flutter/flutter#193142](https://github.com/flutter/flutter/pull/193142)). Once stable carries that fix, set the channel back to `stable`, remove the comment above it, and delete the "Flutter's iOS simulator test run hangs when its log stream attaches late" entry from `UPSTREAM.md`.

## Waiting

- flutter/flutter: a stable release that contains `_ready` in `packages/flutter_tools/lib/src/ios/simulators.dart` (check: `curl -s https://raw.githubusercontent.com/flutter/flutter/stable/packages/flutter_tools/lib/src/ios/simulators.dart | grep -c _ready` prints a non-zero count).
