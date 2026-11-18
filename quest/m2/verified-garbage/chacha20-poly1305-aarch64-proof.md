# [M] ChaCha20-Poly1305 on aarch64 earns the ✓ from pyca/verified-garbage's proof

## Goal

VG's SVE2 `vg_chacha20_poly1305_seal_sve2` and `vg_chacha20_poly1305_open_sve2`, which rind runs on aarch64 CPUs with SVE2 (`rind/src/low/aarch64/chacha20poly1305.rs`), are imported as theorems, so ChaCha20-Poly1305 and XChaCha20-Poly1305's one pass on aarch64 earn the ✓ on SVE2 CPUs.

## Plan

- Import each routine's VG theorem as one axiom about rind's opaque wrapper, under [the m3 epic's composition rule](/quest/m3/verified/README.md), as [the epic](/quest/m2/verified-garbage/README.md)'s Plan settles, and add the `benchmarks/verified.toml` entries for the switched tiers.
- rind's glue around it, HChaCha20 included, is the same on every CPU, and [the m4 quest](/quest/m4/verified/chacha20-poly1305-aarch64.md) proves it; the ✓ on SVE2 CPUs needs that proof too.
- The ✓'s CPU features: `rind-cpuid` and `admin/bench-report`'s `CPU_FEATURES` name no `sve2` yet; add it, so the entries can require it.
- Model gaps, which the maintainer ruled on 2026-11-17 ([kixel-ai/rind#815](https://github.com/kixel-ai/rind/pull/815#issuecomment-6943056592)) as [the epic](/quest/m2/verified-garbage/README.md)'s Plan records: ✅ the stack-slot gap is reported upstream and this ✓ waits for VG's fix and a re-pin (rejected: a rind-side check that each stack load reads only bytes its own frame stored; accepting the model as is). ✅ The `NoResidue` undefined-flags gap is reported upstream and does not hold this ✓, since rind imports no `NoResidue` theorem (rejected: not reporting it).

## Waiting

- pyca/verified-garbage: fix the stack-slot model, [pyca/verified-garbage#5321](https://github.com/pyca/verified-garbage/issues/5321) (a freed frame's bytes keep their values in the model, so a proof can read back a value hardware may have lost); then re-pin `admin/import-vg`'s `REV`, which `admin/import-vg-models` also reads, to a commit with the fix. Check: the issue is closed by a merged fix.
