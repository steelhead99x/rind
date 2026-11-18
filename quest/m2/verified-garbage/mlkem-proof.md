# [M] ML-KEM-768 earns the ✓ from pyca/verified-garbage's proof

## Goal

Every VG routine ML-KEM-768 runs is imported as a theorem, so ML-KEM-768 earns the ✓ on the tiers that run it: its encapsulation key check and encapsulation on every x86_64 CPU and on aarch64 with the SHA-3 instructions, and its key generation and decapsulation on x86_64 with AVX-512 (`low/<arch>/mlkem768_vg.rs`, vendored by `admin/import-vg`).

## Plan

- Import each routine's VG theorem as one axiom about rind's opaque wrapper, under [the m3 epic's composition rule](/quest/m3/verified/README.md), as [the epic](/quest/m2/verified-garbage/README.md)'s Plan settles, and add the `benchmarks/verified.toml` entries for the switched tiers.
- Prove rind's glue around it as the m3 and m4 epics prove rind's other glue: `mid/mlkem.rs` picks VG's routine per key, encodes a VG key as FIPS 203's `dk` for decapsulation, and falls back to rind's arithmetic when a routine reports that a `SampleNTT` reached VG's bound.
- That fallback is rind's arithmetic, which on CPUs with AVX-512 VBMI2 samples the matrix with Graviola's unproven AVX-512 eight-way sampler (`low/x86_64/mlkem_sample_poly_ntt_8x.rs`). That is the only path on which ML-KEM-768 still runs it, since the sampler also asks for AVX-512 VL, so VG's AVX-512 key generation runs wherever it does. The ✓ needs it covered: recommended, route the fallback to the proven four-way sampler, since speed does not matter at a probability below 2^-261, rather than prove the sampler.
- Elsewhere ML-KEM-768 keeps rind's arithmetic, whose ✓ [the construction quest](/quest/m4/verified/mlkem-construction.md) and [the portable arithmetic quest](/quest/m4/verified/mlkem-portable.md) cover.
- Model gaps, which the maintainer ruled on 2026-11-17 ([kixel-ai/rind#815](https://github.com/kixel-ai/rind/pull/815#issuecomment-6943056592)) as [the epic](/quest/m2/verified-garbage/README.md)'s Plan records: ✅ the stack-slot gap is reported upstream and this ✓ waits for VG's fix and a re-pin (rejected: a rind-side check that each stack load reads only bytes its own frame stored; accepting the model as is). ✅ The `NoResidue` undefined-flags gap is reported upstream and does not hold this ✓, since rind imports no `NoResidue` theorem (rejected: not reporting it).

## Waiting

- pyca/verified-garbage: fix the stack-slot model, [pyca/verified-garbage#5321](https://github.com/pyca/verified-garbage/issues/5321) (a freed frame's bytes keep their values in the model, so a proof can read back a value hardware may have lost); then re-pin `admin/import-vg`'s `REV`, which `admin/import-vg-models` also reads, to a commit with the fix. Check: the issue is closed by a merged fix.
