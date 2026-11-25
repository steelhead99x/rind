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

Done on the PR branch: `admin/import-vg` vendors `vg_mldsa{44,65,87}_sign` (VG's plain-key routines, which need no CPU feature) at its pin, `low::mldsa_vg::sign` wraps them, and `vg_sign_matches_rind` checks they sign as rind does, byte for byte. Only that test calls the wrapper yet. Under `admin/ctgrind` that test checks VG's signing, with the glue declassifying whether it finished and the signature, as rind's signing does.

- Decided 2026-11-25 (fork owner): ✅ ctgrind suppresses memcheck's conditional jumps whose innermost frame is `vg_mldsa*_sign_with_cache` (`vg-mldsa-sign-rejection` in `admin/ctgrind.supp`), resting on VG's constant-time theorem for the rest (rejected: trace comparison under `admin/ct-sde`/`ct-qemu` with equal attempt counts; keeping signing on rind's code).
- Upstream decided 2026-11-19 ([the epic](/quest/m2/verified-garbage/README.md), on [kixel-ai/rind#849](https://github.com/kixel-ai/rind/pull/849)): keep rind's own signing, since after [kixel-ai/rind#863](https://github.com/kixel-ai/rind/pull/863) VG lost every size on the weekly tier (1.11, 1.17, 1.36), and propose the switch again only with new numbers. That decision deleted this quest on upstream's `main`; the fork keeps it for this PR.

Left:
- Measure before switching: `RIND_CPU_DISABLE_avx2=1` forces the no-AVX2 path; run rind-bench's `mldsa` rows for rind and VG on the weekly bench's no-AVX2 tier and an idle host, every size, against rind after [kixel-ai/rind#863](https://github.com/kixel-ai/rind/pull/863). Then switch `KeyPair::sign` to VG on CPUs without AVX2 for each set that still wins, for keys generated from a seed only (VG's contract asks for a key its key generation wrote; a key loaded from its expanded form keeps rind's arithmetic, as ML-KEM's decapsulation does).

## Waiting

- Measurement: the timing A/B above needs the weekly bench's no-AVX2 tier or an idle host. GitHub Actions does not run on the fork's account, and this host has 2 CPUs shared with other agents.
- Fork owner: with only `vg-mldsa-sign-rejection`, ctgrind still fails `vg_sign_matches_rind`, in two routines the signing loop calls, on the rest of VG's `signLeak`: `vg_mldsa_sample_in_ball` branches on and indexes by each attempt's `c_tilde`, and `vg_mldsa_hint_bit_pack` branches on the hint. rind's own signing declassifies both (`c_tilde` before `SampleInBall`, `w0` and `w1` before packing hints). Options: (a) suppress conditional jumps in both and secret-indexed loads (`Value8`) in `vg_mldsa_sample_in_ball`, each matched as its innermost frame, recommended, since it is exactly what rind declassifies and VG's theorem allows; (b) keep ctgrind red on this test until the switch, as it already was; (c) check VG's signing by trace comparison instead.
- Fork owner: whether this PR continues after upstream's 2026-11-19 decision above, which `main` took with the sync in [steelhead99x/rind#317](https://github.com/steelhead99x/rind/pull/317). Options: (a) keep it as a draft that vendors and checks VG's signing until a no-AVX2 run against rind after kixel-ai/rind#863 shows VG winning at every size, recommended; (b) close it, as upstream closed kixel-ai/rind#849.
