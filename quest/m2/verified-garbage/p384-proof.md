# [M] P-384 earns the ✓ from pyca/verified-garbage's proof

## Goal

Every VG routine P-384 runs is imported as a theorem, so P-384 key agreement and ECDSA earn back the ✓ on the tiers that run it: VG's `d·G` (`vg_ec_p384_public_key`, and its BMI2 and ADX variant on x86_64), which agreement's and ECDSA's key generation and each signature's `k·G` take on x86_64 and aarch64, and its ECDSA verification, on x86_64 with BMI2 and ADX for every key (`vg_ecdsa_p384_verify_adx`) and on aarch64 until a key's multiples are ready (`vg_ecdsa_p384_verify`) (`low/<arch>/p384_vg.rs`, vendored by `admin/import-vg`).

## Plan

- Import each routine's VG theorem as one axiom about rind's opaque wrapper, under [the m4 epic's composition rule](/quest/m4/verified/README.md#composition-rule), as [the epic](/quest/m2/verified-garbage/README.md)'s Plan settles.
- Prove rind's glue around it as the m4 epic proves rind's other glue: `mid/p384.rs` picks VG's routine by `MulBase::check` or `Verify::check`, encodes the scalar for `d·G`, checks the point it returns is on the curve, reduces its x-coordinate mod n for `r`, and passes verification `r`, `s`, and `e` as bytes, `e` as the 48-byte digest whose leftmost 384 bits VG reads. Signing's `s`, rind's hedged nonce, and the twin multiplication that x86_64 without ADX and aarch64 runs once a key's multiples are ready are already proven (`P384Ecdsa.lean`).
- Then drop `NoVgP384` and `NoVgP384Verify` from the P-384 theorems and restore the `benchmarks/verified.toml` entries [kixel-ai/rind#847](https://github.com/kixel-ai/rind/pull/847)'s switch removed: `p384-ecdh` and `p384-ecdsa-sign` on x86_64 and aarch64, and `p384-ecdsa-verify` on aarch64 and on x86_64 with ADX.
- Model gaps, which the maintainer ruled on 2026-11-17 ([kixel-ai/rind#815](https://github.com/kixel-ai/rind/pull/815#issuecomment-6943056592)) as [the epic](/quest/m2/verified-garbage/README.md)'s Plan records: ✅ the stack-slot gap is reported upstream and this ✓ waits for VG's fix and a re-pin (rejected: a rind-side check that each stack load reads only bytes its own frame stored; accepting the model as is). ✅ The `NoResidue` undefined-flags gap is reported upstream and does not hold this ✓, since rind imports no `NoResidue` theorem (rejected: not reporting it).
