# [S] Apply the SHA-512 IRAM default decision

## Goal

The branch of https://github.com/steelhead99x/rind/pull/94 follows the recorded decision on whether SHA-512 is placed in IRAM by default.

## Plan

On the #94 branch, apply the recorded default. Do not reopen the question, and do not claim a board speedup without numbers.

Success check: in a worktree of the #94 branch, `. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && nix develop -c just check origin/main` exits 0.

## Required

- [Decide whether SHA-512 is placed in IRAM by default](/quest/local/13b-decide-sha512-iram-default.md) - records the default this step applies

## Related

- [Note that ESP32-S3 SHA board timing has not been measured](/quest/local/08c-note-unmeasured-esp32-timing.md) - related unmeasured ESP32-S3 SHA timing
