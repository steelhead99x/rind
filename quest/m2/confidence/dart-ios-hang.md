# [S] The dart-ios check finishes instead of hanging

## Goal

`build.yml`'s `dart-ios` job runs the Flutter integration tests on the iOS simulator and reports a result every time. On 2026-11-12 it hung on several unrelated branches (moq-dev/rind#634's three runs, one of the ML-KEM quest's, and one of release-plz's), each time silent from `Xcode build done` until the job's 30-minute timeout, while other runs on the same `macos-26-arm64` image printed the test results about 45 seconds after the build.

## Plan

- Reproduce on a hosted `macos-latest` runner, or on the Mac mini once [its runner quest](/quest/m0/mac-mini-runner.md) lands, with `flutter test -v` and the simulator's log (`xcrun simctl spawn <udid> log stream`) to find where it stops: installing the app, launching it, or attaching to its VM service.
- Fix that cause. Raising the timeout or retrying the job only hides it.
- Recommendation: keep `flutter test -v` in the job if the cause is intermittent, so the next hang names its step.
