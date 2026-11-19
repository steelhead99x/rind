# [S] aarch64 cipher::ChaCha20 runs pyca/verified-garbage's code where it is faster

## Goal

On aarch64, where pyca/verified-garbage (VG) measures at least as fast as rind at every size, the bare `cipher::ChaCha20` stream cipher runs VG's routine under rind's glue and behavior.

## Plan

- x86_64 switched in [kixel-ai/rind#811](https://github.com/kixel-ai/rind/pull/811): VG's AVX2 and AVX-512 VL routines from 256 bytes, with a tail of two to four blocks after their eight-block loop on rind's two-block kernel, since VG takes those one block at a time and lost to the kernel by up to 1.73x on Arrow Lake. Below 256 bytes, the kernel and HACL*'s rounds stay. x86_64 without AVX2 lost (VG over rind 1.15 to 1.28 from 1200 B with SSSE3, 1.03 at 16 KB without), and armv7 lost 2.3 to 2.5x, VG having no NEON code there ([run 43881997679](https://github.com/kixel-ai/rind/actions/runs/43881997679)), so those keep rind's code.
- aarch64 measured on a Neoverse N2 in that run, VG over rind: 0.52 to 0.65 from 1200 B, but 1.22 at 32 B. VG has an SVE2 routine, which the N2 ran, and a NEON one, for cores without SVE2 such as Apple's. Apple's M4 (`kixtop`, NEON, 2026-11-17, about 1.6 of its 10 CPUs busy with other work) measured VG's API over rind's: 0.75 at 1200 and 1350 B and 0.57 at 16 KB, but 1.30 at 32 B, the N2's shape. Time both against rind's NEON from 32 B through 2 KB at every block count and partial block, on an idle N2-class host and an Apple M-series one, and switch from the length past which VG wins at every size, as x86_64 does, splitting off any tail it loses on.
- Take `vg_chacha20_init`, `vg_chacha20_apply_neon`, and `vg_chacha20_apply_sve2` through `admin/import-vg`'s `ROOTS["aarch64"]`, beside [kixel-ai/rind#813](https://github.com/kixel-ai/rind/pull/813)'s ChaCha20-Poly1305 roots, and detect SVE2 at run time.
- QUIC header protection keeps rind's one-block path, where VG lost (1.21 to 1.37), since a mask starts a new keystream each time.
- Wycheproof and the aws-lc-rs differential tests already cover the operation; extend `low::aarch64` tests to every path, and `admin/ct-qemu` to the SVE2 routine, which valgrind cannot run.

## Hosts

- linux - an idle aarch64 host with SVE2, such as a Neoverse N2
- macos - Apple's cores, which lack SVE2

## Related

- [The proof](/quest/m2/verified-garbage/chacha20-proof.md) - imports the theorems of the routines this adopts
