# [M] rind-devbench and admin/hw/ab time swole's benches

## Goal

`rind-devbench` runs rind-bench's swole benches, the files in `rind-bench/benches/`, inside its iOS and Android apps under the same row IDs, and `rind-devbench/criterion-benches/` goes; and `admin/hw/ab`'s A/B rounds time a swole revision through `swole bench <base>` rather than criterion's binaries.

## Plan

- Why: kixel-ai/rind#1141 moved every rind-bench bench to swole's `#[bench]` functions, which devbench's criterion shim cannot run, so the sync that took it (steelhead99x/rind#349) kept devbench on a copy of the last criterion files, `rind-devbench/criterion-benches/`. A row rind-bench adds now reaches the app only by being copied there, and the copy drifts from what the report times.
- devbench: a `swole` stand-in crate under `rind-devbench/`, which swole's own `swole-macros` expands `#[bench]` into, as its `::swole::__private` API (`Bench`, `Case`, `fresh`, `kept`, `fresh_timed`, `kept_timed`, `step`, `single`, `each`, `inventory`, `black_box`, `Iterations`), with its cases public to the app, so it lists each case and times it for N iterations in process. IDs follow `admin/bench-report`'s `bench_id`: the path after the file with `/` for `::` and `-` for `_`, then the argument. swole has no throughput, so devbench derives a row's bytes from its size argument where the report needs them. `src/benches.rs` then includes `../rind-bench/benches/*.rs`, `tools/gen-ops.py --check` still passes, and the iOS and Android builds and the host smoke (`cargo run --release --example devbench-cli`) list the same rows the report has.
- `admin/hw/ab`: its `rounds` time a swole revision with `swole bench <base> --benchmarks <list> --out`, pinned as now, keeping its rotation, idle checks, and controls, and its own `CRITERION_ARGS` go once no pending hardware run needs a criterion revision.
- `RIND_BENCH_LOW_MEMORY` (argon2's 64 MiB row and rustls's every-CPU rows) moves into the stand-in's selection, since a swole row cannot leave itself out at run time without changing its ID.

## Hosts

- macos - the iOS build
- linux - the Android build and `admin/hw/ab`
