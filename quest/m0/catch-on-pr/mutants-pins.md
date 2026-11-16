# [M] Mutants exclusions survive code moving

## Goal

`.cargo/mutants.toml`'s exclusions keep matching the mutants they were written for when unrelated code above them moves, and `admin/mutants --pins` fails on an exclusion that matches fewer mutants than it names.

## Plan

- Many `exclude_re` entries pin a mutant by `file:line:col`, so any edit above one moves it off its mutant and main's mutants check fails; that happened twice on 2026-11-14 and 2026-11-15. Replace each line pin with a match on the function and mutation text cargo-mutants prints, as the `\d+:\d+` entries already do, and keep a line only where two mutants in one function are otherwise identical, saying so in the entry's comment.
- `admin/mutants --pins` passes an alternation such as `(a|b)` when either half matches, so a half that went stale hides. Check each alternative of a top-level group on its own, or require each entry to match as many mutants as it is written for; pick whichever keeps the config readable, and say which in the PR.
- [PR checks running the queue's cheap modules](/quest/m0/catch-on-pr/pr-queue-parity.md) makes the pin check run on PRs; this quest makes it fail less often.
