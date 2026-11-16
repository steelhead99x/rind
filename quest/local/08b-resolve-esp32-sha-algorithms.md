# [S] Resolve the ESP32-S3 SHA conflict in ALGORITHMS.md

## Goal

https://github.com/kixel-ai/rind/pull/793 merges cleanly into upstream main, and `ALGORITHMS.md` is resolved without dropping the ESP32-S3 SHA work.

## Plan

The only conflict with upstream main is `ALGORITHMS.md`. Merge upstream main into the #793 branch and push only after the go.

Success check: `git merge-tree --write-tree --name-only up/main HEAD` prints only a tree object (no conflict paths), and after the push `gh pr view 793 --repo kixel-ai/rind --json mergeable --jq .mergeable` prints `MERGEABLE`.

## Required

- [Approve merging upstream main into the ESP32-S3 SHA draft](/quest/local/08a-approve-esp32-sha-merge.md) - pushing the merge is approved
