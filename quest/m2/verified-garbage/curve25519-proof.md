# [M] X25519 and Ed25519 on AVX-512 earns the ✓ from pyca/verified-garbage's proof

## Goal

Every VG routine X25519 and Ed25519 run is imported as a theorem, so they earn the ✓ on the x86_64 CPUs with AVX-512 IFMA that run them ([kixel-ai/rind#845](https://github.com/kixel-ai/rind/pull/845)): `vg_x25519_exchange_ifma`, `vg_x25519_base_ifma`, `vg_ed25519_key_pair_avx2_ifma`, `vg_ed25519_sign_expanded_avx2_ifma`, and `vg_ed25519_verify_avx2_ifma`, against `VG.Spec.X25519`'s and `VG.Spec.Ed25519`'s contracts.

## Plan

- Import each routine's VG theorem as one axiom about rind's opaque wrapper, under [the m4 epic's composition rule](/quest/m4/verified/README.md#composition-rule), as [the epic](/quest/m2/verified-garbage/README.md)'s Plan settles, and add the `benchmarks/verified.toml` entries for the switched tiers.
- Prove rind's glue around it as the m4 epic proves rind's other glue: the word-to-byte conversions around X25519, and Ed25519's key types, whose `Path` picks VG's routines once per key and passes `vg_ed25519_sign_expanded_avx2_ifma` the digest and public key `vg_ed25519_key_pair_avx2_ifma` wrote, as its precondition requires.
- Model gaps, which the maintainer ruled on 2026-11-17 ([kixel-ai/rind#815](https://github.com/kixel-ai/rind/pull/815#issuecomment-6943056592)) as [the epic](/quest/m2/verified-garbage/README.md)'s Plan records: ✅ the stack-slot gap is reported upstream and this ✓ waits for VG's fix and a re-pin (rejected: a rind-side check that each stack load reads only bytes its own frame stored; accepting the model as is). ✅ The `NoResidue` undefined-flags gap is reported upstream and does not hold this ✓, since rind imports no `NoResidue` theorem (rejected: not reporting it).

## Waiting

- pyca/verified-garbage: fix the stack-slot model, [pyca/verified-garbage#5321](https://github.com/pyca/verified-garbage/issues/5321) (a freed frame's bytes keep their values in the model, so a proof can read back a value hardware may have lost); then re-pin `admin/import-vg`'s `REV`, which `admin/import-vg-models` also reads, to a commit with the fix. Check: the issue is closed by a merged fix.
