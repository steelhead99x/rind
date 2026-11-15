# [S] cipher::ChaCha20 runs pyca/verified-garbage's code where it is faster

## Goal

For each cell below, an operation on a tier, where pyca/verified-garbage (VG) measures at least as fast as rind at every size, the bare `cipher::ChaCha20` stream cipher runs VG's routine under rind's glue and behavior.

## Plan

- Measured only on `desktop` (Arrow Lake) under load on 2026-11-14, by the `chacha20` rows [kixel-ai/rind#741](https://github.com/kixel-ai/rind/pull/741) added after its bench run, so first read those rows in a weekly bench run that ran them and time an idle host. Ratios are VG's time over rind's.
- Take VG's lowest routine that leaves rind's API and behavior intact and keep rind's glue, as [the epic](/quest/m2/verified-garbage/README.md)'s Plan settles. Vendor it with `admin/import-vg`, which the first switch to land adds.
- Re-measure each cell below before and after on the weekly bench's tiers and an idle host, and switch only the cells that still hold at every size; every other tier keeps rind's code.
- QUIC header protection keeps rind's one-block path, where VG lost (1.21 to 1.37), since a mask starts a new keystream each time.
- Wycheproof and the aws-lc-rs differential tests already cover the operation; extend the ctgrind tests to the new code path.

Cells VG may win:

- x86_64 with AVX2 (`desktop`, noisy): 0.88 to 0.93 at 32 B and 1200 B, 0.52 to 0.85 at 1350 B, and 0.63 to 0.75 at 16 KB, against rind's AVX2 kernels. AVX-512 CPUs run the same AVX2 kernels, so [the x86_64 cipher proof quest](/quest/m4/verified/chacha20-poly1305-x86/cipher.md) drops them only if both tiers switch.
- Unmeasured: AVX-512, aarch64 (where a switch shrinks [the aarch64 proof quest](/quest/m4/verified/chacha20-poly1305-aarch64.md) to the AEAD), and armv7.
- Lost: x86_64 without AVX2 (aws-lc's SSSE3 routine), 1.08 to 1.37 from 1200 B up, though 0.94 at 32 B.
