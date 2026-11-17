# [L] cipher::ChaCha20 is proven on x86_64

## Goal

`cipher::ChaCha20` earns the ✓ on x86_64 CPUs with SSE4.1.

## Plan

- Prove rind's AVX2 kernels with Aeneas over modelled intrinsics, and compose them with the HACL* rounds' proof. The SSSE3 routine this used to name no longer ships: without AVX2 the keystream is those rounds at every length.
- pyca/verified-garbage (VG)'s bare ChaCha20 looked faster than rind's AVX2 kernels on `desktop` (0.52 to 0.93 under load) and slower than the SSSE3 routine (1.08 to 1.37 from 1200 B up); [its switch quest](/quest/m2/verified-garbage/chacha20.md) settles it on the tiers.

## Required

- [cipher::ChaCha20 runs pyca/verified-garbage's code where it is faster](/quest/m2/verified-garbage/chacha20.md) - this quest drops a kernel only once no tier runs it, such as the AVX2 kernels if both the AVX2 and AVX-512 tiers switch; delete it if every tier switches, and drop this link if none does
