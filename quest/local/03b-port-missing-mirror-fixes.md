# [S] Port any missing later fixes to the upstream drafts

## Goal

Every later fork fix named by the comparison, including `fe5a0ee5aa5b3f103263b80047ec41ba4f4b7ac4` if it is missing from https://github.com/kixel-ai/rind/pull/790, is present on the matching upstream draft. If the comparison found nothing missing, the heads are left untouched.

## Plan

If the comparison recorded no missing fixes, this step is a no-op. If a hunk is missing, port it on the upstream draft branch. Pushing to an upstream pull request branch waits on an explicit go.

Success check: `git fetch up pull/790/head && git show fe5a0ee5aa5b3f103263b80047ec41ba4f4b7ac4 -- rind/src/mid/mod.rs && git grep -n 'table alignment comes from the wrapper' FETCH_HEAD -- rind/src/mid/mod.rs` prints a match, and the same form of `git grep` or `git show` confirms every other named fix is on its upstream head.

## Required

- [Check that later fork fixes were ported to the upstream drafts](/quest/local/03a-check-fork-mirror-fixes.md) - names any missing fix to port

## Waiting

- Maintainer: if a port must be pushed to an upstream draft, approve that push. Check: the success check above finds each named fix. Skip this item when nothing is missing.
