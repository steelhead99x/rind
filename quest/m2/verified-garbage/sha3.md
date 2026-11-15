# [S] SHA-3 runs pyca/verified-garbage's code where it is faster

## Goal

For each cell below, an operation on a tier, where pyca/verified-garbage (VG) measured at least as fast as rind at every size, SHA-3 and SHAKE runs VG's routine under rind's glue and behavior.

## Plan

- Measured in [run 43531095881](https://github.com/kixel-ai/rind/actions/runs/43531095881) (the `bench` workflow dispatched on [kixel-ai/rind#741](https://github.com/kixel-ai/rind/pull/741) at VG `d004ffae`) and on the report's hosts, as [the epic](/quest/m2/verified-garbage/README.md) records. Ratios are VG's time over rind's.
- Take VG's lowest routine that leaves rind's API and behavior intact and keep rind's glue, as the epic's Plan settles. Vendor it with `admin/import-vg`, which the first switch to land adds.
- Re-measure each cell below before and after on the weekly bench's tiers and an idle host, and switch only the cells that still hold at every size; every other tier keeps rind's code.
- Wycheproof and the aws-lc-rs differential tests already cover the operation; extend the ctgrind tests to the new code path.

Cells VG won:

- aarch64 (Neoverse N2) with the SHA-3 instructions: 0.46 to 0.54 at every size and output length, though VG runs its NEON Keccak there (it takes FEAT_SHA3 only when `VG_CPU_FEATURES` names it). First find why rind's FEAT_SHA3 path is twice as slow; without the instructions the two are level (0.97 to 1.08).
- x86_64 without AVX2: 0.88 to 0.98 at every size.
- `desktop` (noisy): 0.88 to 0.97. `ovh-sea`: 0.96 to 1.00. Lost: AVX-512 (up to 1.05), `ovh-iad` SHA3-256 at 1350 B (1.04).
