# [S] The ESP32-C6's results are written down, each with how it was measured

## Goal

`benchmarks/esp32c6.md` holds rind's ESP32-C6 results: the measured-without-the-board table (code, static RAM, stack, heap, from qemu-user and section sizes) and the on-board table (time per operation, rounds, medians, clock, supply, temperature). Every cell is a number a command produced, or `TODO`. The board tables were filled from one run of [the firmware](/quest/m2/bench/esp32-c6-bench.md) on a board in the compare PR; cells for operations the firmware does not time stay `TODO`.

## Plan

Drafted 2026-11-20 (Claude). The skeleton is in the PR: the qemu-user table with the numbers `admin/esp32c6-riscv32 size` printed, the board table with `TODO` in every number cell, and a short list of what each cell's number means and does not mean.

- Fill the board table from `admin/esp32c6-bench-ingest`'s JSON, one row per operation, median over the firmware's rounds with min and max, and add the supply, ambient temperature if known, and the firmware commit.
- Delete the `TODO` rows that no run will fill (for example an operation the firmware leaves out) instead of leaving them.
- Say, beside the table, that no other library was timed: aws-lc-rs and ring do not build for riscv32imac without a C toolchain, so the rows give no comparison and no claim that rind is faster.
- When the board table is full, link `benchmarks/esp32c6.md` from `PLATFORMS.md` and `ALGORITHMS.md`'s microcontroller notes.

## Required

- [The firmware and ingest script](/quest/m2/bench/esp32-c6-bench.md) - produce the log this table is made from
