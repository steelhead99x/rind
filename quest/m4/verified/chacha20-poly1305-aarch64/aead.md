# [XL] aws-lc's ChaCha20-Poly1305 seal and open are proven on aarch64

## Goal

`AwsLc` in `proofs/Rind/Aarch64/ChaCha20Poly1305.lean` is discharged, so ChaCha20-Poly1305 and XChaCha20-Poly1305 earn the ✓ at every length on aarch64 CPUs without SVE2, as they do with it.

## Plan

- Runs: aws-lc's NEON `chacha20_poly1305_{seal,open}` and `poly_hash_ad_internal` (`low/aarch64/aws_lc/`), which interleave NEON ChaCha20 with scalar Poly1305, on CPUs without SVE2 at the lengths `seal_runs_vg` and `open_runs_vg` leave to it: sealing up to 576 bytes and from 769 to 896, and opening up to 128, from 257 to 448, and from 896 to 960. rind passes no extra ciphertext, so the routines' `extra_in` paths never run.
- Proof: Lean proofs of the routines on VG's aarch64 model, with their leakage contracts, against `Rind/Spec.lean`'s RFC 8439, as [kixel-ai/rind#912](https://github.com/kixel-ai/rind/pull/912) proved aarch64 SHA-256, rind's extension in `proofs/verified-garbage/RindIsa/` adding what aws-lc's code uses beyond VG's model (its LD1 and ST1 of up to four registers and `x29`/`x30` frame are there). Restate them in `Rind/Aarch64/` as axioms about `seal_aws_lc` and `open_aws_lc` that give `AwsLc`, record them in `Axioms.lean`, and add the `verified.toml` entry for `chacha20poly1305/*` and `xchacha20poly1305/*` on aarch64 without SVE2 (`cpu = ["!sve2"]`), replacing the epic's 1350 B and 16 KB one if it has landed. Until `kixtop` is measured at a revision with [kixel-ai/rind#1023](https://github.com/kixel-ai/rind/pull/1023), which moved those two rows to VG's NEON routine, the entry leaves them out, as the epic's README and `benchmarks/verified.toml` say.
- Found on [kixel-ai/rind#1077](https://github.com/kixel-ai/rind/pull/1077): VG's model proves structured code (`Code` in `VerifiedGarbage/TCB/Code.lean`: blocks, `if`, do-while loops, calls, and frames), which its printer lowers to the bytes `admin/prove` checks, but aws-lc's routines branch freely. The seal's main loop exits from its middle, three paths enter `.Lchacha_poly_seal_tail`, and the 128-byte path, laid out after `finalize`, jumps back into it. Those bytes have no `Code` form.
- Route (maintainer, 2026-11-26, through /quest-merge on kixel-ai/rind#1077): ✅ (a) rind's own structured copy of the routines in VG's `Code`, each shared tail duplicated into the paths that reach it and the `extra_in` paths dropped, taken only if it measures within noise of aws-lc's on an Apple M-series core and a Neoverse N2, and listed in ALGORITHMS.md as a deliberate change; it leaves VG's trusted base as it is (rejected: (b) a semantics for unstructured code in `RindIsa`, a control-flow graph over aws-lc's bytes with its own leakage and frame rules, a larger trusted base). If the copy does not measure within noise, the routines stay unproven here and the quest is replanned. [x86_64's aws-lc child](/quest/m4/verified/chacha20-poly1305-x86/aead.md) faces the same choice, as its routines branch the same way.
- Seal and open are 1,114 and 1,281 instructions, under a third of the 8,138 of x86_64's.

## Related

- [aws-lc's ChaCha20-Poly1305 seal and open are proven on x86_64](/quest/m4/verified/chacha20-poly1305-x86/aead.md) - the same routines' x86_64 halves, on the same route
