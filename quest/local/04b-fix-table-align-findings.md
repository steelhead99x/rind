# [S] Fix or refute the table-alignment review findings

## Goal

Every finding from the review of https://github.com/kixel-ai/rind/pull/790 is fixed or refuted on that branch. If the review recorded none, the head is unchanged and still green.

## Plan

The review (7/10, head `b2ca6a39`) is in `~/rind-responses/r1115/04a-review-790.md`: 1 medium, the Lean specs guess an Aeneas extraction and disagree with each other (run `admin/prove lean` and match them; fork #79's `fa675158`, not yet on #790, already reworks the aarch64 P-256 proof); 1 low, the benchmark table does not measure this change (measure against the parent or retitle `fix(ec)`). Fix or refute each finding on the #790 branch. Pushing to the upstream draft waits on an explicit go. Do not mark the draft ready.

On macOS, `just check` also fails on `rind::zeroing ml_dsa` (fails on the parent too, rewritten upstream by #781) and on `mutants` (no Darwin arm64 campaign); neither comes from this diff.

Success check: in a worktree of the #790 branch, `. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && nix develop -c just check up/main` exits 0.
