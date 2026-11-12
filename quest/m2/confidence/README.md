# Every primitive is tested as thoroughly as the best libraries test theirs

## Goal

Every primitive, on every backend and CPU tier, has published test vectors, a differential fuzz target, a differential test, and a constant-time check that also catches variable-time instructions. Mutation testing shows the tests catch changes to rind's Rust. Mechanical checks guard what those cannot see: the assembly boundary, wiping, the portable backend, and the adapters' promises.

## Plan

Decided with the maintainer on 2026-11-07, in m3. Moved to m2 with the maintainer on 2026-11-09, after an audit of the whole tree: ✅ m2 (rejected: redefine m3 to hold assurance, move only the security check). This is active work, not deferred, and m3 is for waits and work deferred by priority.

rind already has these:
- differential fuzz targets against aws-lc-rs, run nightly;
- Wycheproof and cross-checks against aws-lc-rs;
- Intel SDE CPU models for every x86_64 dispatch path;
- ctgrind, `admin/ct-sde`, and `admin/ct-qemu` for secret-dependent branches and addresses;
- `admin/ct-vartime`, in `just ci`, for variable-time instructions, which those three can't see.

[OSS-Fuzz](/quest/m4/oss-fuzz.md) is planned in m4 and isn't repeated here.

The 2026-11-09 audit found no exploitable bug and no panic reachable from public input, and planned the eleven children from the hostile-input fuzz target down: each is a hole it confirmed in the code that no test, fuzzer, or proof sees today.

Three coverage children joined on 2026-11-12, with the maintainer, from the nightly `coverage.yml` report: it measures only published code under the tests that call it, rind-aws-lc-rs runs aws-lc-rs's own tests, and every published function then runs under a test.

- Fix what a check finds in its own quest's PR when it's small; otherwise plan a follow-up.
- Slow suites run in their own workflows, not in `just ci`, as `AGENTS.md` asks.
