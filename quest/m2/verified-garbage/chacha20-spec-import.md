# [M] rind's copy of pyca/verified-garbage's ChaCha20 spec is proven equal to VG's

## Goal

`proofs/Rind/VgChaCha20.lean` no longer trusts that its copy of pyca/verified-garbage's (VG's) `Spec/ChaCha20.lean` matches VG's text. The x86_64 ChaCha20 axioms are stated over VG's own definitions, imported from the vendored `VerifiedGarbage.Spec.ChaCha20`, and a theorem bridges them to the byte view rind's proof uses. So a re-pin that changes VG's spec fails the Lean build instead of waiting on someone to review the diff.

## Plan

- Found in [kixel-ai/rind#853](https://github.com/kixel-ai/rind/pull/853). Its copy reads the streaming state's 768 bytes `st` where VG reads memory, with `m (p + i)` as `st[i]!` and `Mem.read` and `Mem.readW` as little-endian reads of `st`. Its header says no check compares it with VG's text.
- `admin/import-vg-models` already vendors `Spec/ChaCha20.lean` and `Spec/ChaCha20/Contract.lean` under `proofs/verified-garbage/`, so nothing new needs copying.
- Follow the RSA import: `Rind/X86_64/VgRsa.lean` imports `VerifiedGarbage.Spec.Rsa` and states its axioms over VG's definitions. Restate `vg_chacha20_init_spec`, `vg_chacha20_apply_avx2_spec` and `vg_chacha20_apply_avx512vl_spec` the same way, and prove that VG's memory view of the state agrees with the byte view `chacha20_apply_keystream` uses, so that theorem's statement and `#print axioms` set stay as they are.
- Then delete the adapted definitions, along with the copy's `LICENSE` entry and SPDX header, which only an adapted file needs.
- [kixel-ai/rind#869](https://github.com/kixel-ai/rind/pull/869) also edits `Rind/X86_64/VgChaCha20.lean`. Whichever lands second merges the other.

## Related

- [cipher::ChaCha20 earns the ✓ from pyca/verified-garbage's proof](/quest/m2/verified-garbage/chacha20-proof.md) - imports aarch64's routines the same way once its switch lands
