# [M] RSA on AVX-512 earns the ✓ from pyca/verified-garbage's proof

## Goal

Every VG routine rind runs for RSA on x86_64 with AVX-512 IFMA since [kixel-ai/rind#814](https://github.com/kixel-ai/rind/pull/814) is imported as a theorem, so RSA there earns the ✓ on the tiers that run it: the public operation of 2048-, 3072-, and 4096-bit moduli with e = 65537 (`vg_rsa_public_precomputed_checked_ifma`, VG's `checked_correct` against `pdChkContract`), and the CRT of 2048- and 4096-bit keys, and of 3072-bit keys with AVX512_FP16 (`vg_rsa_private_crt_precomputed_ifma` and `_ifma512`, VG's `codeP_inlined` against `crtContractP`), both reaching `vg_rsa_mont_mul_adx`.

## Plan

- Import each routine's VG theorem as one axiom about rind's opaque wrapper, under [the m3 epic's composition rule](/quest/m3/verified/README.md), as [the epic](/quest/m2/verified-garbage/README.md)'s Plan settles, and add the `benchmarks/verified.toml` entries for the switched tiers.
- Prove rind's glue around it as the m3 and m4 epics prove rind's other glue.
- RSA-2048 PKCS#1 v1.5 verification lost its ✓ on CPUs with AVX-512 IFMA when it switched: `benchmarks/verified.toml` denies `avx512ifma`, and `proofs/Rind/X86_64/RsaPublic.lean`'s `public_op_spec` assumes `NoIfma`, that `low::RsaIfma::check` returns `None`. Restoring it replaces `NoIfma` with the imported theorem about the opaque `RsaPublicKey::public_op_ifma`, which `admin/prove` leaves untranslated.
- These are VG's internal functions, whose contracts are in its proofs rather than its trusted `Spec`, so the import restates them from `Proof/Variants/RsaPublicPrecomputed/X86_64/Ifma.lean` and `Proof/Variants/RsaPrivateCrt/X86_64/Ifma.lean`; `rind/src/low/x86_64/rsa_ifma.rs`'s `# Safety` comments restate their preconditions.
- Model gaps, which the maintainer ruled on 2026-11-17 ([kixel-ai/rind#815](https://github.com/kixel-ai/rind/pull/815#issuecomment-6943056592)) as [the epic](/quest/m2/verified-garbage/README.md)'s Plan records: ✅ the stack-slot gap is reported upstream and this ✓ waits for VG's fix and a re-pin (rejected: a rind-side check that each stack load reads only bytes its own frame stored; accepting the model as is). ✅ The `NoResidue` undefined-flags gap is reported upstream and does not hold this ✓, since rind imports no `NoResidue` theorem (rejected: not reporting it).

## Waiting

- pyca/verified-garbage: fix the stack-slot model, [pyca/verified-garbage#5321](https://github.com/pyca/verified-garbage/issues/5321) (a freed frame's bytes keep their values in the model, so a proof can read back a value hardware may have lost); then re-pin `admin/import-vg`'s `REV`, which `admin/import-vg-models` also reads, to a commit with the fix. Check: the issue is closed by a merged fix.
