# [XS] Resolve the adapter-mutants conflict in mutants.toml

## Goal

https://github.com/kixel-ai/rind/pull/792 merges cleanly into upstream main after resolving `.cargo/mutants.toml`, and the pin check still matches the mutants it names.

## Plan

The only conflict with upstream main is `.cargo/mutants.toml`. Merge upstream main into the #792 branch, keep the adapter-campaign pin updates, and push only after the go.

Success check: `git merge-tree --write-tree --name-only up/main HEAD` prints only a tree object, after the push `gh pr view 792 --repo kixel-ai/rind --json mergeable --jq .mergeable` prints `MERGEABLE`, and in a worktree of the branch `. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && nix develop -c admin/mutants --pins` exits 0.

## Required

- [Approve merging upstream main into the adapter-mutants draft](/quest/local/09e-approve-adapter-mutants-merge.md) - pushing the merge is approved
