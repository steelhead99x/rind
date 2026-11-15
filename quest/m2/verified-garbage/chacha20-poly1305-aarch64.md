# [M] ChaCha20-Poly1305 on aarch64 runs pyca/verified-garbage's code where it is faster

## Goal

For each cell below, an operation on a tier, where pyca/verified-garbage (VG) measured at least as fast as rind at every size, ChaCha20-Poly1305 on aarch64 runs VG's routine under rind's glue and behavior.

## Plan

- Measured in [run 43531095881](https://github.com/kixel-ai/rind/actions/runs/43531095881) (the `bench` workflow dispatched on [kixel-ai/rind#741](https://github.com/kixel-ai/rind/pull/741) at VG `d004ffae`) and on the report's hosts, as [the epic](/quest/m2/verified-garbage/README.md) records. Ratios are VG's time over rind's.
- Take VG's lowest routine that leaves rind's API and behavior intact and keep rind's glue, as the epic's Plan settles. Vendor it with `admin/import-vg`, which the first switch to land adds.
- Re-measure each cell below before and after on the weekly bench's tiers and an idle host, and switch only the cells that still hold at every size; every other tier keeps rind's code.
- Wycheproof and the aws-lc-rs differential tests already cover the operation; extend the ctgrind tests to the new code path.

Cells VG won:

- aarch64 (Neoverse N2), with and without the crypto extension: seal 0.76 to 0.92 and open 0.60 to 0.92 at every size, 32 B to 16 KB.
- Lost on x86_64: AVX-512 up to 1.14 (seal at 512 B), no AVX2 1.16 to 1.68, the Haswell VPSes 1.02 to 1.10. Level without AES-NI (0.91 to 1.01) and without SSSE3 (0.98 to 1.00).
- VG has no XChaCha20-Poly1305 or HChaCha20; ChaCha20 header protection loses (1.21 to 1.37). A switch shrinks [the aarch64 proof quest](/quest/m4/verified/chacha20-poly1305-aarch64.md) to what rind still runs.
