# [M] cipher::ChaCha20 earns the ✓ from pyca/verified-garbage's proof

## Goal

Every VG routine [the switch](/quest/m2/verified-garbage/chacha20.md) adopts is imported as a theorem, so `cipher::ChaCha20` earns the ✓ on the tiers that run it.

## Plan

- Import each routine's VG theorem as one axiom about rind's opaque wrapper, under [the m3 epic's composition rule](/quest/m3/verified/README.md), as [the epic](/quest/m2/verified-garbage/README.md)'s Plan settles, and add the `benchmarks/verified.toml` entries for the switched tiers.
- Prove rind's glue around it as the m3 and m4 epics prove rind's other glue.
- [The cosimulation quest](/quest/m2/verified-garbage/cosim.md) does not cover this routine's instructions; extend it here.

## Required

- [cipher::ChaCha20 runs pyca/verified-garbage's code where it is faster](/quest/m2/verified-garbage/chacha20.md) - the routines this proves
- [VG's ISA models are cosimulated](/quest/m2/verified-garbage/cosim.md) - the cosimulation harness this extends
