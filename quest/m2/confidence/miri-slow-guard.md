# [XS] Miri's slow list names real tests

## Goal

`sh/miri.sh` fails when a name in its `slow` list matches no test, so a
renamed or misspelled entry cannot silently put a slow test back into the
Miri run.

## Plan

Decided 2026-11-12 (user, /quest-plan), from rind's trimmed Pullfrog
learnings. `.cargo/mutants.toml`'s exclusions already have their guard,
`admin/mutants --pins`, so this quest covers only the Miri list.

Open PR [moq-dev/rind#693](https://github.com/moq-dev/rind/pull/693) rewrites
the list and moves Miri to nightly; build on whatever it lands.

Recommended: before running Miri, list the test names with `cargo nextest
list` under the Miri run's own `RUSTFLAGS`, features, `--target`, and test
targets (today `--cfg rind_portable`, `--features wipe`, and `--lib --test cpu
--test debug`, `sh/miri.sh:122-125`), and fail naming each `slow` entry that
matches none, the way #699 checks mutants exclusions. A host listing without
`rind_portable` misses tests such as
`low::posint::tests::mont_exp_matches_square_and_multiply`, which
`rind/src/low/posint.rs` compiles only off the x86_64 backend.
