# [M] just ci runs only what a change can break, concurrently

## Goal

`just check` and `just ci` run each module only when the branch changed a folder or crate that module can break, scoped to those crates, as moq's do, and run the selected modules concurrently. A merge group or a local check that touches one crate pays for that crate's checks, not the whole tree's.

## Plan

Asked for by the maintainer on 2026-11-12, after the measurements in [the epic](/quest/m0/ci-speed/README.md).

- rind's `sh/dispatch.sh` already selects by diff, but several modules match broadly and then run a fixed workload: `cross` and `vartime` on any `rind/src` change, `msrv` on any crate directory (it then checks rind and rind-rustls on three targets whatever changed), `fixtures` on anything under `rind/`. In the long merge groups (20 to 29 min) `cross`, `vartime`, `msrv`, and `dart` together outlast `rs`. Narrow each module's pattern and its workload to what the change can break, with the reason in the map's comment; where only `rind` itself is affected, the full module still runs, since every crate depends on it.
- Port moq's dispatcher features rind lacks, from moq-dev/moq's `sh/dispatch.sh`: `CHECK_JOBS` lanes running modules concurrently with readable output, `CHECK_FAIL_FAST` for the queue, `CHECK_MODULES` to run or skip named modules, and `CHECK_TIMES` per-phase timings. Measure a merge group's time before and after.
- Inside `rind`, select by primitive where tests run slowly, not where they compile: one map from a changed path (such as `rind/src/mid/aes*` or `rind/src/low/x86_64/aes*`) to a nextest filterset and the benchmark groups for that primitive, used by the SDE, qemu, miri, and ctgrind runs and by bench dispatch ([hosted-trim](/quest/m0/ci-speed/hosted-trim.md)), locally and in CI. A shared path such as `low/mod.rs` or `Cargo.toml` selects everything.
- ✅ Don't split the integration test binaries (`wycheproof.rs`, `cctv.rs`, `aws_lc.rs`) or crates by primitive (maintainer, 2026-11-12, on the recommendation): native tests take about 10 s against minutes of compiling, and more binaries add link steps (rejected: one test binary per primitive).
- Recommendation: no record of passed modules to skip a re-run on an unchanged tree. Diff scoping plus cargo's incremental build already make a re-run cheap; a pass cache would be one more thing to invalidate correctly.
- Keep `check --all` and the daily unscoped run on main ([hosted-trim](/quest/m0/ci-speed/hosted-trim.md)) as the backstop for a pattern drawn too narrow.
