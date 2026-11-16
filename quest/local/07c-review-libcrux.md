# [S] Review the drop-libcrux draft

## Goal

https://github.com/kixel-ai/rind/pull/794 has one local review against the post-merge head and current upstream main, with numbered findings or an explicit "no findings" result.

## Plan

In a worktree of the #794 branch, review the diff against upstream main. Do not mark the draft ready, and do not post under the owner's name without an explicit go.

Success check: in that worktree, `. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && nix develop -c just check up/main` exits 0.

## Required

- [Resolve the drop-libcrux conflict in ALGORITHMS.md](/quest/local/07b-resolve-libcrux-algorithms.md) - the draft merges cleanly before it is reviewed
