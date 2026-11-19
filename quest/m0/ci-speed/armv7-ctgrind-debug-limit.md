# [S] armv7's debug ctgrind unit rows finish inside the job limit

## Goal

ctgrind's `armv7 (unit, debug)` and `armv7 (unit, no-neon, debug)` rows run every unit test under memcheck and finish well inside GitHub's 6-hour job limit on `ubuntu-24.04-arm`, so the weekly ctgrind run can pass.

## Plan

- Keep this quest, in m0: ✅ keep, m0 (rejected: drop it). The maintainer's pick on [kixel-ai/rind#818](https://github.com/kixel-ai/rind/pull/818#issuecomment-6942507833), 2026-11-17.
- Both rows were cancelled at 6 hours on main's code in [run 43884518954](https://github.com/kixel-ai/rind/actions/runs/43884518954) and [run 43883030917](https://github.com/kixel-ai/rind/actions/runs/43883030917), after about 460 of the suite's 522 tests. The tests still running at the cut were ML-KEM's `acvp_encap_decap`, ML-DSA's `acvp_sig_ver` and `wycheproof`, and P-384's and P-521's `multipl*_match_double_and_add`. The release rows take about 75 minutes, and valgrind runs every thread on one core.
- Measure first: per-test times from one debug run's log, such as libtest's `--report-time` or nextest's.
- Recommended: split the debug unit suite across parallel jobs, as the suites already are, such as by `cargo nextest run --partition`, with ctgrind as nextest's target runner, keeping every test. Skipping the slowest tests in debug is the fallback, but only for tests that mark no secret, with the reason recorded.
- The armv7 rows came from [kixel-ai/rind#743](https://github.com/kixel-ai/rind/pull/743), whose goal was weekly suites that finish.
