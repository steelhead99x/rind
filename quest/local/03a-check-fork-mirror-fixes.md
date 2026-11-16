# [XS] Check that later fork fixes were ported to the upstream drafts

## Goal

Each fork mirror has been compared with its upstream draft, and any later fix that is missing from the upstream head is named, including the documentation fix `fe5a0ee5aa5b3f103263b80047ec41ba4f4b7ac4` from https://github.com/steelhead99x/rind/pull/79.

## Plan

The pairs are https://github.com/steelhead99x/rind/pull/111 with https://github.com/kixel-ai/rind/pull/790, #112 with #791, #113 with #792, #114 with #793, and #115 with #794. For each pair, fetch both heads and compare later commits on the fork original (the earlier, non-mirror pull request, such as #79 for #111) against the upstream draft.

For the documentation fix, compare `rind/src/mid/mod.rs` on `fe5a0ee5aa5b3f103263b80047ec41ba4f4b7ac4` with the same file on #790. Do not close any pull request in this step, and do not push.

Success check: `git fetch origin pull/79/head && git fetch up pull/790/head && git show fe5a0ee5aa5b3f103263b80047ec41ba4f4b7ac4:rind/src/mid/mod.rs > /tmp/79-mod.rs && git show FETCH_HEAD:rind/src/mid/mod.rs > /tmp/790-mod.rs && diff -u /tmp/79-mod.rs /tmp/790-mod.rs`. Repeat an equivalent `git show` comparison for the other four pairs. The step is done when each pair is recorded as "hunk present" or "missing: <commit>".
