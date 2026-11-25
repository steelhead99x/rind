# [S] ML-DSA signing without AVX2 runs pyca/verified-garbage's code where it is faster

## Goal

For each cell below, an operation on a tier, where pyca/verified-garbage (VG) measured at least as fast as rind at every size, ML-DSA signing on x86_64 without AVX2 runs VG's routine under rind's glue and behavior.

## Plan

- Measured in [run 43531095881](https://github.com/kixel-ai/rind/actions/runs/43531095881) (the `bench` workflow dispatched on [kixel-ai/rind#741](https://github.com/kixel-ai/rind/pull/741) at VG `d004ffae`) and on the report's hosts, as [the epic](/quest/m2/verified-garbage/README.md) records. Ratios are VG's time over rind's.
- Take VG's lowest routine that leaves rind's API and behavior intact and keep rind's glue, as the epic's Plan settles. Vendor it with `admin/import-vg`, which the first switch to land adds.
- Re-measure each cell below before and after on the weekly bench's tiers and an idle host, and switch only the cells that still hold at every size; every other tier keeps rind's code.
- Wycheproof and the aws-lc-rs differential tests already cover the operation; extend the ctgrind tests to the new code path.

Cells VG won:

- x86_64 without AVX2: signing at 0.85 to 0.87 for ML-DSA-44, -65, and -87. Key generation (1.04) and verification (1.01 to 1.09) lose there.
- aarch64: ML-DSA-65 and -87 signing at 0.99, ML-DSA-44 1.05, so no cell. Lost with AVX2 (1.04 to 1.10) and on the Haswell VPSes (1.26).
- VG's row signs with its plain signing key, not its pre-expanded one.

Done on the PR branch: `admin/import-vg` vendors `vg_mldsa{44,65,87}_sign` (VG's plain-key routines, which need no CPU feature) at its pin, `low::mldsa_vg::sign` wraps them, and `vg_sign_matches_rind` checks they sign as rind does, byte for byte. Only that test calls the wrapper yet.

Left:
- Measure before switching: `RIND_CPU_DISABLE_avx2=1` forces the no-AVX2 path; run rind-bench's `mldsa` rows for rind and VG on the weekly bench's no-AVX2 tier and an idle host, every size. Then switch `KeyPair::sign` to VG on CPUs without AVX2 for each set that still wins, for keys generated from a seed only (VG's contract asks for a key its key generation wrote; a key loaded from its expanded form keeps rind's arithmetic, as ML-KEM's decapsulation does).
- ctgrind: VG's routine branches on which attempt it rejects (`signLeak`) inside its assembly, where rind cannot declassify as its own signing does, so memcheck would flag it.

## Waiting

- Maintainer: how ctgrind checks VG's signing, whose rejection branches memcheck would flag. Options: (a) a valgrind suppression for conditional jumps inside `vg_mldsa*_sign_with_cache`, resting on VG's constant-time proof for the rest, recommended; (b) check it only under `admin/ct-sde`/`ct-qemu` trace comparison with inputs of equal attempt counts; (c) leave signing on rind's code.
