# [M] RSA on AVX-512 runs pyca/verified-garbage's code where it is faster

## Goal

For each cell below, an operation on a tier, where pyca/verified-garbage (VG) measured at least as fast as rind at every size, RSA on x86_64 with AVX-512 IFMA runs VG's routine under rind's glue and behavior.

## Plan

- Measured in [run 43531095881](https://github.com/kixel-ai/rind/actions/runs/43531095881) (the `bench` workflow dispatched on [kixel-ai/rind#741](https://github.com/kixel-ai/rind/pull/741) at VG `d004ffae`) and on the report's hosts, as [the epic](/quest/m2/verified-garbage/README.md) records. Ratios are VG's time over rind's.
- Take VG's lowest routine that leaves rind's API and behavior intact and keep rind's glue, as the epic's Plan settles. Vendor it with `admin/import-vg`, which the first switch to land adds.
- Re-measure each cell below before and after on the weekly bench's tiers and an idle host, and switch only the cells that still hold at every size; every other tier keeps rind's code.
- Wycheproof and the aws-lc-rs differential tests already cover the operation; extend the ctgrind tests to the new code path.

Cells VG won:

- Public operation, x86_64 with AVX-512 (Zen 4): verification with a parsed key 0.55, PKCS#1 and PSS verification 0.49 to 0.56 at 2048 to 4096 bits and 0.95 at 6144 and 8192, OAEP encryption 0.61. (The unparsed rows skip rind's DER parse for VG, so read the parsed one.)
- Private operation with IFMA, at the sizes rind's dual RSAZ runs (2048, 3072, 4096 bits): 0.96 to 0.99, OAEP decryption 0.98. A switch at all three sizes replaces the dual RSAZ, and [its proof quest](/quest/m4/verified/rsa-x86-ifma.md) is deleted with it; a partial one shrinks that quest to the sizes left.
- Lost: 2056 and 2560 bits (1.12, 1.71), 6144 and 8192 signing (1.06, 1.07), key generation below 4096 bits (1.26 to 1.30), every size on the Haswell VPSes without ADX (about 2.0 to 2.2), and aarch64's parsed verification (1.04). VG imports keys from components, not DER, so rind keeps its parsing and key checks.
