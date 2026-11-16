# [S] Resolve the drop-libcrux conflict in ALGORITHMS.md

## Goal

https://github.com/kixel-ai/rind/pull/794 merges cleanly into upstream main, `ALGORITHMS.md` is resolved, and libcrux stays dropped from the rind crate.

## Plan

The only conflict with upstream main is `ALGORITHMS.md`. Merge upstream main into the #794 branch, keep the drop of libcrux, and push only after the go. Confirm `rind/Cargo.toml` still has no libcrux dependency.

Success check: `git merge-tree --write-tree --name-only up/main HEAD` prints only a tree object (no conflict paths), `git grep -n libcrux HEAD -- rind/Cargo.toml` prints nothing, and after the push `gh pr view 794 --repo kixel-ai/rind --json mergeable --jq .mergeable` prints `MERGEABLE`.

## Required

- [Approve merging upstream main into the drop-libcrux draft](/quest/local/07a-approve-libcrux-merge.md) - pushing the merge is approved
