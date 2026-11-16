# [S] Resolve the Ed25519 CCTV conflicts

## Goal

https://github.com/kixel-ai/rind/pull/797 merges cleanly into upstream main after resolving `TESTING.md`, `rind/tests/cctv.rs`, and `rind/tests/heap_scratch.rs` against the current API.

## Plan

Those three paths are the files that conflict with upstream main. Merge upstream main into the #797 branch, resolve them, and push only after the go.

Success check: `git merge-tree --write-tree --name-only up/main HEAD` prints only a tree object, after the push `gh pr view 797 --repo kixel-ai/rind --json mergeable --jq .mergeable` prints `MERGEABLE`, and in a worktree of the branch `. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && nix develop -c cargo test -p rind --test cctv` and `nix develop -c cargo test -p rind --test heap_scratch` both exit 0.

## Required

- [Approve merging upstream main into the Ed25519 CCTV draft](/quest/local/09i-approve-ed25519-cctv-merge.md) - pushing the merge is approved
