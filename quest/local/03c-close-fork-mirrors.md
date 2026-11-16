# [XS] Close the fork mirrors of the upstream drafts

## Goal

https://github.com/steelhead99x/rind/pull/111, https://github.com/steelhead99x/rind/pull/112, https://github.com/steelhead99x/rind/pull/113, https://github.com/steelhead99x/rind/pull/114, and https://github.com/steelhead99x/rind/pull/115 are closed. The matching upstream drafts remain open.

## Plan

This is a person action, not a coding session. Close the five fork pull requests only after the porting check, and only with an explicit go. Leave the upstream drafts open.

Success check: `for n in 111 112 113 114 115; do gh pr view $n --repo steelhead99x/rind --json number,state --jq '[.number,.state]|@tsv'; done` prints `CLOSED` for each, and `for n in 790 791 792 793 794; do gh pr view $n --repo kixel-ai/rind --json number,state --jq '[.number,.state]|@tsv'; done` prints `OPEN` for each.

## Required

- [Port any missing later fixes to the upstream drafts](/quest/local/03b-port-missing-mirror-fixes.md) - missing fixes are on the upstream drafts, or none were missing

## Waiting

- Maintainer: approve closing the five fork pull requests. Check: the success check above shows #111 through #115 closed and #790 through #794 open.
