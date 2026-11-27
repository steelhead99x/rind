# [L] Benches move from Criterion to rust2-bench-harness

## Goal

Every bench target in `rind-bench` is written as rust2-bench-harness `#[bench]` functions, which rust2-bench counts and the native rows, the weekly gate, and the benchmark report time through the harness. Criterion, `codspeed-criterion-compat`, and the `__bench_codspeed` feature leave the workspace, so nothing in rind names CodSpeed.

Non-goals: what each row measures, the weekly cadence, the report's hosts, and the libraries rind is compared against.

## Plan

Decided 2026-11-25 (maintainer, `/quest-plan` in kixel-ai/rust2, [kixel-ai/rust2#1031](https://github.com/kixel-ai/rust2/pull/1031)):

- ✅ No CodSpeed service, app, or code in moq-dev or kixel-ai (rejected: the service and app only; drop the work). [kixel-ai/rind#1013](https://github.com/kixel-ai/rind/pull/1013) ends the service; this ends the crate.
- ✅ Rewrite the benches to `#[bench]` (rejected: a Criterion-API count layer in the harness, deleted later by this rewrite; wait for rust2's m2 harness epic).
- ✅ The harness's wall-clock timing ships first, so each bench is written once and Criterion leaves with CodSpeed's crate (rejected: rewrite now and stop the native rows' timing until it ships; keep a Criterion copy of each bench for timing). rust2's [paired timing](https://github.com/kixel-ai/rust2/blob/main/quest/m1/codspeed/paired.md) is required to time one build's rows against each other, as the native rows compare rind with aws-lc-rs and ring.

Recommendations for the implementer:

- One PR: Criterion can leave only once every target has moved, and `admin/bench-report` would otherwise read two formats.
- `admin/bench-report`, the weekly `gate`, and `BENCHMARKS.md`'s refresh read Criterion's IDs and `target/criterion/**/benchmark.json`. Move them to the harness's output in the same PR, and keep each row's operation and library recoverable from its name.
- Keep each benchmark's name where the harness can, so Kixel Quest's instruction series and the gate's `--previous` comparison continue. Name in the PR the ones that change; a gate across the rename compares nothing for them for one run.
- The Graviola rows that #1013 leaves out of the count build, since Valgrind hides ADX, and `rsa_gen`'s `NOISY_BENCHMARKS` gate need a home in the harness's terms, without a cargo feature to switch harnesses.
- Update `TESTING.md`, `CONTRIBUTING.md`, and every comment that names CodSpeed.

Public API: none.

## Waiting

- kixel-ai/rust2: paired timing, `quest/m1/codspeed/paired.md` in its quest tree; check that the file is gone from rust2's `main` and rind's rust2 flake pin includes it.

## Required

- [The Valgrind runner](/quest/m2/bench/valgrind-runner.md) - moves the weekly count to rust2-bench, which this rewrite builds on

## Related

- `quest/m2/bench/deterministic-counts.md`, which [kixel-ai/rind#1013](https://github.com/kixel-ai/rind/pull/1013) adds - the same counts' noise
