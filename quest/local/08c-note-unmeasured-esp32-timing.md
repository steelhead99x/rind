# [XS] Note that ESP32-S3 SHA board timing has not been measured

## Goal

https://github.com/kixel-ai/rind/pull/793 states that SHA performance on the ESP32-S3 board has not been measured, and it does not claim a speedup without numbers.

## Plan

This is a person action, not a coding session. After an explicit go, add this sentence to the pull request body (or a comment if the body is left otherwise unchanged): "SHA performance on the ESP32-S3 board has not been measured."

Success check: `gh pr view 793 --repo kixel-ai/rind --json body --jq .body` contains `SHA performance on the ESP32-S3 board has not been measured`.

## Required

- [Resolve the ESP32-S3 SHA conflict in ALGORITHMS.md](/quest/local/08b-resolve-esp32-sha-algorithms.md) - the draft is caught up before the note is posted

## Waiting

- Maintainer: approve posting the sentence above on https://github.com/kixel-ai/rind/pull/793. Check: the success check above finds that sentence.
