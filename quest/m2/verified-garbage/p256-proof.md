# [M] P-256 earns the ✓ from pyca/verified-garbage's proof

## Goal

Every VG routine P-256 runs is imported as a theorem, so P-256 key agreement and ECDSA earns the ✓ on the tiers that run it: ECDH and ECDSA verification on x86_64 with BMI2, ADX, AVX, and AVX2 (with AVX-512 IFMA, its IFMA variants) and on aarch64, and the public key's derivation, which key generation and signing's nonce point run, on aarch64 and on such x86_64 CPUs from Intel or with IFMA (`low/<arch>/p256_vg.rs`, vendored by `admin/import-vg`). Until then P-256 has no ✓ on those tiers, and the Lean theorems state `NoVgP256`.

## Plan

- Import each routine's VG theorem as one axiom about rind's opaque wrapper, under [the m3 epic's composition rule](/quest/m3/verified/README.md), as [the epic](/quest/m2/verified-garbage/README.md)'s Plan settles, and add the `benchmarks/verified.toml` entries for the switched tiers.
- Prove rind's glue around it as the m3 and m4 epics prove rind's other glue: `mid/p256.rs` picks VG's routine by `P256::check` or `check_public_key`, encodes the key and point for it, and reads the public key's x-coordinate as signing's `r`. Then drop `NoVgP256` from the P-256 theorems and restore the `benchmarks/verified.toml` entries this quest's switch removed (aarch64's) or narrowed to `!adx` (x86_64's).
- Model gaps, which the maintainer ruled on 2026-11-17 ([kixel-ai/rind#815](https://github.com/kixel-ai/rind/pull/815#issuecomment-6943056592)) as [the epic](/quest/m2/verified-garbage/README.md)'s Plan records: ✅ the stack-slot gap is reported upstream and this ✓ waits for VG's fix and a re-pin (rejected: a rind-side check that each stack load reads only bytes its own frame stored; accepting the model as is). ✅ The `NoResidue` undefined-flags gap is reported upstream and does not hold this ✓, since rind imports no `NoResidue` theorem (rejected: not reporting it).

## Waiting

- pyca/verified-garbage: fix the stack-slot model, [pyca/verified-garbage#5321](https://github.com/pyca/verified-garbage/issues/5321) (a freed frame's bytes keep their values in the model, so a proof can read back a value hardware may have lost); then re-pin `admin/import-vg`'s `REV`, which `admin/import-vg-models` also reads, to a commit with the fix. Check: the issue is closed by a merged fix.
