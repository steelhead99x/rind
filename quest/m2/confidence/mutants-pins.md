# [S] Every mutants exclusion matches a mutant

## Goal

Each `exclude_re` entry in `.cargo/mutants.toml` that pins a `file:line` matches a mutant `cargo mutants --list` lists today, and a check fails when one stops matching, so a pin that drifts is caught in the PR that moves its code rather than later as a nightly survivor.

## Plan

- Decided 2026-11-12 (maintainer, while picking [moq-dev/rind#655](https://github.com/moq-dev/rind/pull/655)): ✅ plan this quest (rejected: leave stale pins for the nightly to surface one at a time). #655 found about 36 pinned entries that no longer match any mutant, in `low/x86_64/cpu.rs`, `mid/mldsa.rs`, `hkdf.rs`, `ghash.rs`, `sha1.rs`, and the adapter crates, some pointing at deleted code. It is the third time pins have drifted.
- Repin each stale entry to the line `cargo mutants --list` reports for the same mutant, or drop it where the code is gone or a test now catches the mutant (run `admin/mutants` on that file to tell).
- Add the check to `just check`'s scope for changes that touch `.cargo/mutants.toml` or a pinned file: list the mutants for each architecture `admin/mutants` covers, and fail naming every pinned entry that matches none. Listing takes seconds; it needs no test run.
- Prefer patterns that survive line moves, such as matching the function name the mutant names, where cargo-mutants' output carries it.

## Related

- [Adapter crates' surviving mutants](/quest/m2/confidence/mutants-adapters.md) - kills the adapters' excluded mutants; this quest only keeps the pins accurate
