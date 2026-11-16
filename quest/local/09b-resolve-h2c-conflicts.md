# [S] Resolve the hash-to-curve conflicts

## Goal

https://github.com/kixel-ai/rind/pull/791 merges cleanly into upstream main after resolving `TESTING.md`, `rind-timing/src/cases.rs`, and `rind/src/high/oprf/tests.rs` against the current API.

## Plan

Those three paths are the files that conflict with upstream main. Merge upstream main into the #791 branch, resolve them, and push only after the go.

Success check: `git merge-tree --write-tree --name-only up/main HEAD` prints only a tree object, after the push `gh pr view 791 --repo kixel-ai/rind --json mergeable --jq .mergeable` prints `MERGEABLE`, and in a worktree of the branch `. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && nix develop -c cargo test -p rind -- p256_refuses_identity_hash_at_oprf_boundaries` and `nix develop -c cargo test -p rind-timing` both exit 0.

## Required

- [Approve merging upstream main into the hash-to-curve draft](/quest/local/09a-approve-h2c-merge.md) - pushing the merge is approved
