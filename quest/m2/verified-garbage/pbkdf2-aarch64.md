# [S] PBKDF2 on aarch64 runs pyca/verified-garbage's code where it is faster

## Goal

For each cell below, an operation on a tier, where pyca/verified-garbage (VG) measured at least as fast as rind at every size, PBKDF2 on aarch64 runs VG's routine under rind's glue and behavior.

## Plan

- Measured in [run 43531095881](https://github.com/kixel-ai/rind/actions/runs/43531095881) (the `bench` workflow dispatched on [kixel-ai/rind#741](https://github.com/kixel-ai/rind/pull/741) at VG `d004ffae`) and on the report's hosts, as [the epic](/quest/m2/verified-garbage/README.md) records. Ratios are VG's time over rind's.
- Take VG's lowest routine that leaves rind's API and behavior intact and keep rind's glue, as the epic's Plan settles. Vendor it with `admin/import-vg`, which the first switch to land adds.
- Re-measure each cell below before and after on the weekly bench's tiers and an idle host, and switch only the cells that still hold at every size; every other tier keeps rind's code.
- Wycheproof and the aws-lc-rs differential tests already cover the operation; extend the ctgrind tests to the new code path.

Cells VG won:

- aarch64 (Neoverse N2): PBKDF2-HMAC-SHA1, -SHA256, -SHA384, and -SHA512 at 0.88 to 0.93; level on x86_64 with AVX-512 (0.99 to 1.01), and on `desktop` 0.83 to 0.94 under load.
- VG's single HMAC loses at short messages (1.3 to 1.4 at 32 B), so the win is its iteration loop: compare it with rind's before taking VG's code.
