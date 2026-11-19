# [M] P-384 earns the ✓ from pyca/verified-garbage's proof

## Goal

Every VG routine [the switch](/quest/m2/verified-garbage/p384.md) adopts is imported as a theorem, so P-384 key agreement and ECDSA earns the ✓ on the tiers that run it.

## Plan

- Import each routine's VG theorem as one axiom about rind's opaque wrapper, under [the m4 epic's composition rule](/quest/m4/verified/README.md#composition-rule), as [the epic](/quest/m2/verified-garbage/README.md)'s Plan settles, and add the `benchmarks/verified.toml` entries for the switched tiers.
- Prove rind's glue around it as the m4 epic proves rind's other glue.
- Model gaps, which the maintainer ruled on 2026-11-17 ([kixel-ai/rind#815](https://github.com/kixel-ai/rind/pull/815#issuecomment-6943056592)) as [the epic](/quest/m2/verified-garbage/README.md)'s Plan records: ✅ the stack-slot gap is reported upstream and this ✓ waits for VG's fix and a re-pin (rejected: a rind-side check that each stack load reads only bytes its own frame stored; accepting the model as is). ✅ The `NoResidue` undefined-flags gap is reported upstream and does not hold this ✓, since rind imports no `NoResidue` theorem (rejected: not reporting it).

## Required

- [P-384 runs pyca/verified-garbage's code where it is faster](/quest/m2/verified-garbage/p384.md) - the routines this proves
