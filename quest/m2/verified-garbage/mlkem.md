# [M] ML-KEM-768 runs pyca/verified-garbage's code where it is faster

## Goal

For each cell below, an operation on a tier, where pyca/verified-garbage (VG) measured at least as fast as rind at every size, ML-KEM-768 runs VG's routine under rind's glue and behavior.

## Plan

- Measured in [run 43531095881](https://github.com/kixel-ai/rind/actions/runs/43531095881) (the `bench` workflow dispatched on [kixel-ai/rind#741](https://github.com/kixel-ai/rind/pull/741) at VG `d004ffae`) and on the report's hosts, as [the epic](/quest/m2/verified-garbage/README.md) records. Ratios are VG's time over rind's.
- Take VG's lowest routine that leaves rind's API and behavior intact and keep rind's glue, as the epic's Plan settles. Vendor it with `admin/import-vg`, which the first switch to land adds.
- Re-measure each cell below before and after on the weekly bench's tiers and an idle host, and switch only the cells that still hold at every size; every other tier keeps rind's code.
- Wycheproof and the aws-lc-rs differential tests already cover the operation; extend the ctgrind tests to the new code path.

Cells VG won:

- Key generation and encapsulation, on every tier and host timed but armv7: 0.66 to 0.88 (AVX-512 0.66 to 0.81, no AVX-512 0.75 to 0.85, no AVX2 0.74 to 0.87, aarch64 0.67 to 0.71, the Haswell VPSes 0.75 to 0.88, `desktop` 0.68 to 0.78).
- Decapsulation only with AVX-512 (0.96). It loses elsewhere: no AVX-512 1.17, no AVX2 1.25, aarch64 without SHA-3 2.48, the Haswell VPSes 1.20.
- VG generates keys from a seed; its row draws the seed in the loop as rind does.
- On AVX-512 VG wins every operation, so a switch there replaces Graviola's AVX-512 sampler, and [its proof quest](/quest/m4/verified/mlkem-avx512-sampler.md) is deleted with it. Elsewhere decide whether to switch key generation and encapsulation alone, since decapsulation re-encrypts with the same arithmetic.
