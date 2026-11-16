# [S] Apply the ML-DSA error-mapping decision and fix the remaining findings

## Goal

https://github.com/steelhead99x/rind/pull/109 maps refusal errors by the recorded decision, and its medium findings are fixed or refuted.

## Plan

On the #109 branch, apply the mapping recorded in the decision, then fix or refute any remaining findings. Do not reopen the mapping rule.

Success check: in a worktree of the #109 branch, `. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && nix develop -c just check origin/main` exits 0.

## Required

- [Decide ML-DSA wipe and refusal error mapping](/quest/local/11a-decide-mldsa-error-mapping.md) - records the mapping this step applies
