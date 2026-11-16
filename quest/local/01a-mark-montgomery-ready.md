# [XS] Mark the Montgomery four-row-products draft ready

## Goal

https://github.com/kixel-ai/rind/pull/780 is marked ready for review. The draft is already clean and approved.

## Plan

This is a person action, not a coding session. The pull request merges cleanly into upstream main. Once there is an explicit go, mark it ready and leave the branch untouched.

Success check: `gh pr view 780 --repo kixel-ai/rind --json isDraft --jq .isDraft` prints `false`.

## Waiting

- Maintainer: approve marking https://github.com/kixel-ai/rind/pull/780 ready for review. Check: the success check above prints `false`.
