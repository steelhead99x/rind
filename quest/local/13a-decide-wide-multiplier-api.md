# [XS] Decide whether wide_multiplier is public API and whether Pi 5 benches are required

## Goal

https://github.com/steelhead99x/rind/pull/82 has a recorded decision on whether `wide_multiplier()` is public API, and on whether the Raspberry Pi 5 benches are required before landing.

## Plan

This is a person action, not a coding session. Record both choices on the pull request. Do not change the branch in this step.

Success check: `gh pr view 82 --repo steelhead99x/rind --json body --jq .body; gh api repos/steelhead99x/rind/issues/82/comments --jq '.[].body'` prints a decision on `wide_multiplier()` visibility and on the Raspberry Pi 5 benches.

## Waiting

- Maintainer: decide whether `wide_multiplier()` on https://github.com/steelhead99x/rind/pull/82 is public API, and whether the Raspberry Pi 5 benches are required before landing. Check: the success check above finds both choices.

## Related

- [Decide whether SHA-512 is placed in IRAM by default](/quest/local/13b-decide-sha512-iram-default.md) - the other remaining design call in this group
