# [M] X25519 and Ed25519 on AVX-512 earns the ✓ from pyca/verified-garbage's proof

## Goal

Every VG routine [the switch](/quest/m2/verified-garbage/curve25519.md) adopts is imported as a theorem, so X25519 and Ed25519 earns the ✓ on the tiers that run it.

## Plan

- Import each routine's VG theorem as one axiom about rind's opaque wrapper, under [the m3 epic's composition rule](/quest/m3/verified/README.md), as [the epic](/quest/m2/verified-garbage/README.md)'s Plan settles, and add the `benchmarks/verified.toml` entries for the switched tiers.
- Prove rind's glue around it as the m3 and m4 epics prove rind's other glue.

## Required

- [X25519 and Ed25519 on AVX-512 runs pyca/verified-garbage's code where it is faster](/quest/m2/verified-garbage/curve25519.md) - the routines this proves
- [VG's ISA models are cosimulated](/quest/m2/verified-garbage/cosim.md) - the instructions those routines run, checked against the CPU
