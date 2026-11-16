# [XS] Decide whether SHA-512 is placed in IRAM by default

## Goal

https://github.com/steelhead99x/rind/pull/94 has a recorded decision on whether SHA-512 should go into the ESP32-S3's fast memory (IRAM) by default, even though a speedup has not been measured.

## Plan

This is a person action, not a coding session. Record the default on the pull request. Do not change the branch in this step.

Success check: `gh pr view 94 --repo steelhead99x/rind --json body --jq .body; gh api repos/steelhead99x/rind/issues/94/comments --jq '.[].body'` prints a decision on the IRAM default.

## Waiting

- Maintainer: decide whether SHA-512 is placed in IRAM by default on https://github.com/steelhead99x/rind/pull/94. Check: the success check above finds that choice.

## Related

- [Review the ESP32-S3 SHA draft](/quest/local/08d-review-esp32-sha.md) - related ESP32-S3 SHA work upstream
