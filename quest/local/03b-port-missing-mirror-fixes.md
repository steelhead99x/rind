# [S] Port any missing later fixes to the upstream drafts

## Goal

Every later fork fix named by the comparison, including `fe5a0ee5aa5b3f103263b80047ec41ba4f4b7ac4` if it is missing from https://github.com/kixel-ai/rind/pull/790, is present on the matching upstream draft. If the comparison found nothing missing, the heads are left untouched.

## Plan

The comparison is in `~/rind-responses/r1115/03a-ports.md`. Missing: #790 from fork #79 `fa675158`, `76107d8a`, `1d892295`, `94479701`, `fe5a0ee5`; #791 from #39 `6b27ab63`, `9c9e33ef`; #792 from #23 `bf25c044`; #794 from #102 `cd4eeea3`, `72033c83`, `3236167c`, `6ea28637`, `0294fe8d`; #793 from #69 nothing. For each missing hunk, port it on the upstream draft branch. Pushing to an upstream pull request branch waits on an explicit go.

Success check: `git fetch up pull/790/head && git show fe5a0ee5aa5b3f103263b80047ec41ba4f4b7ac4 -- rind/src/mid/mod.rs && git grep -n 'The alignment comes only from this wrapper' FETCH_HEAD -- rind/src/mid/mod.rs` prints a match, and the same form of `git grep` or `git show` confirms every other named fix is on its upstream head.

## Waiting

- Maintainer: if a port must be pushed to an upstream draft, approve that push. Check: the success check above finds each named fix. Skip this item when nothing is missing.
