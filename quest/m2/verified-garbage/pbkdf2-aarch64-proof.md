# [M] PBKDF2 on aarch64 earns the ✓ from pyca/verified-garbage's proof

## Goal

Every VG routine PBKDF2 on aarch64 runs is imported as a theorem, so PBKDF2 on aarch64 earns the ✓ on the tiers that run it: `vg_pbkdf2_hmac_sha1_sha2` and `vg_pbkdf2_hmac_sha256_sha2` with the crypto extension, and `vg_pbkdf2_hmac_sha384_sha512` and `vg_pbkdf2_hmac_sha512_sha512` with the SHA-512 instructions, which `low::aarch64::pbkdf2_vg` calls. Without those instructions PBKDF2 runs rind's loop, whose Lean proof already holds.

## Plan

- Import each routine's VG theorem as one axiom about rind's opaque wrapper, under [the m4 epic's composition rule](/quest/m4/verified/README.md#composition-rule), as [the epic](/quest/m2/verified-garbage/README.md)'s Plan settles, and add the `benchmarks/verified.toml` entries for the switched tiers.
- Prove rind's glue around it as the m4 epic proves rind's other glue: `mid::pbkdf2_vg::Key`, which keeps HMAC's key (the secret, or its hash past a block) and checks lengths, and `pbkdf2::Secret`'s `Vg` branch. `admin/prove`'s PBKDF2 pass leaves `mid::pbkdf2_vg` opaque (`proofs/Rind/X86_64/Kdf/FunsExternal.lean`), so `derive_spec` and `verify_spec` in `proofs/Rind/X86_64/Pbkdf2.lean` cover only `Secret`'s `Rind` branch; extend them to the `Vg` branch on aarch64.
- Model gaps, which the maintainer ruled on 2026-11-17 ([kixel-ai/rind#815](https://github.com/kixel-ai/rind/pull/815#issuecomment-6943056592)) as [the epic](/quest/m2/verified-garbage/README.md)'s Plan records: ✅ the stack-slot gap is reported upstream and this ✓ waits for VG's fix and a re-pin (rejected: a rind-side check that each stack load reads only bytes its own frame stored; accepting the model as is). ✅ The `NoResidue` undefined-flags gap is reported upstream and does not hold this ✓, since rind imports no `NoResidue` theorem (rejected: not reporting it).

## Waiting

- pyca/verified-garbage: fix the stack-slot model, [pyca/verified-garbage#5321](https://github.com/pyca/verified-garbage/issues/5321) (a freed frame's bytes keep their values in the model, so a proof can read back a value hardware may have lost); then re-pin `admin/import-vg`'s `REV`, which `admin/import-vg-models` also reads, to a commit with the fix. Check: the issue is closed by a merged fix.
