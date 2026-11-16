# [S] Settle the remaining findings on the wide-multiplier and SHA-512 IRAM drafts

## Goal

https://github.com/steelhead99x/rind/pull/82 and https://github.com/steelhead99x/rind/pull/94 each have a recorded decision on their open findings, and the branches follow those decisions.

## Plan

- On https://github.com/steelhead99x/rind/pull/82, the remaining low findings include whether `wide_multiplier()` should be public API, and the Raspberry Pi 5 benches. Record the API decision, then fix or refute the lows, including any bench follow-up the decision requires.
- On https://github.com/steelhead99x/rind/pull/94, one medium finding remains after three review rounds: whether SHA-512 should go into the ESP32-S3's fast memory (IRAM) by default, even though a speedup has not been measured. Record the default, then apply it.

## Waiting

- Maintainer: decide whether `wide_multiplier()` on https://github.com/steelhead99x/rind/pull/82 is public API, and whether the Raspberry Pi 5 benches are required before landing. Check: a comment or commit on the pull request states the choices.
- Maintainer: decide whether SHA-512 is placed in IRAM by default on https://github.com/steelhead99x/rind/pull/94. Check: a comment or commit on the pull request states the choice.

## Related

- [Resolve and review the ESP32-S3 SHA draft](/quest/local/08-big-esp32-s3-sha.md) - related ESP32-S3 SHA work upstream
