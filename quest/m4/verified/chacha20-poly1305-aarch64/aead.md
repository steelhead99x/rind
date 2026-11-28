# [XL] aws-lc's ChaCha20-Poly1305 seal and open are proven on aarch64

## Goal

`AwsLc` in `proofs/Rind/Aarch64/ChaCha20Poly1305.lean` is discharged, so ChaCha20-Poly1305 and XChaCha20-Poly1305 earn the ✓ at every length on aarch64 CPUs without SVE2, as they do with it.

## Plan

- Runs: rind's structured copy of aws-lc's NEON `chacha20_poly1305_{seal,open}` (`low/aarch64/chacha20poly1305/`), which interleaves NEON ChaCha20 with scalar Poly1305, on CPUs without SVE2 at the lengths `seal_runs_vg` and `open_runs_vg` leave to it: sealing up to 576 bytes and from 769 to 896, and opening up to 128, from 257 to 448, and from 896 to 960.
- Done in [kixel-ai/rind#1118](https://github.com/kixel-ai/rind/pull/1118), on route (a), which the maintainer chose on [kixel-ai/rind#1077](https://github.com/kixel-ai/rind/pull/1077):
  - The copy keeps aws-lc's instructions, inlines `poly_hash_ad_internal`, drops `extra_in`, and lays each routine out as VG's `Code`. It measured within noise of aws-lc's on an Apple M5 Pro and a Neoverse N2, and ALGORITHMS.md lists it as a deliberate change.
  - `RindIsa` gained the instructions it uses, B.cond, and `ite`/`loop` layout.
  - `RindIsa/AArch64/ChaCha20Poly1305.lean` holds `sealProg` and `openProg`, which `admin/prove lean` checks byte for byte and `admin/prove vg` cosimulates.
  - `Rind/Aarch64/ChaCha20Poly1305Asm.lean` proves both programs constant-time for public `x0`–`x5`, `sp`, and the constants' address, through the kernel-checked taint checker in `Rind/Aarch64/Taint.lean`.
- Done in [kixel-ai/rind#1147](https://github.com/kixel-ai/rind/pull/1147):
  - `Rind/Aarch64/Asm.lean` runs straight-line blocks of rind's AArch64 model symbolically, with frames and a loop lemma, as `Rind/X86_64/Asm.lean` does for x86_64.
  - `Rind/Aarch64/ChaCha20Poly1305Poly.lean` proves the Poly1305 block step at the level of numbers (`limbs_mulOut`, `limbs_addT`, `acc_step`: 3 limbs times a clamped 2-limb `r`, partially reduced mod 2^130 − 5) and runs `polyAdd` and `polyMul` on the model. `limbs` and `reduce_limbs` moved to `Rind/Poly1305Limbs.lean`, which the x86_64 proofs import.
  - `Rind/Aarch64/ChaCha20Poly1305Ad.lean` proves the inlined AAD hash, `adBlocks` then `adTail`, all four copies (`ad_ok`), with traces of the AAD's address and length alone.
  - `Rind/Aarch64/ChaCha20Poly1305Named.lean` restates both programs in named blocks, `sealNamed` and `openNamed`, equal to `sealProg` and `openProg` by `rfl`: all 31 copies of the multiply-and-reduce (`polyMul`, inside `polyBlock` or `polyAdd ++ polyMul`), the AAD hash, and the double round over one, two, or three blocks (`doubleRound1` to `doubleRound3`).
- Left: functional correctness of `sealNamed` and `openNamed` in the model against `Rind/Spec.lean`'s RFC 8439, as `Rind/Aarch64/Sha256HwAsm.lean` proves SHA-256's routine: from a `Pre` (lengths, a 16-byte-aligned stack with 64 writable bytes below it, readable input, AAD, and constants, writable output and data block, input equal to or disjoint from output), the output holds `chacha20.encrypt key 1 nonce msg` and the data block's first 16 bytes the tag, d8–d15, `sp`, and `x30` are kept, and some state meets `Pre`.
  - ChaCha20 on NEON: `doubleRound1` to `doubleRound3` as RFC 8439's double round on each block's state in the registers aws-lc keeps it in (block `i`'s rows in `v<i>`, `v<5+i>`, `v<10+i>`, and `v<15+i>`), then the round loops and the key-stream additions. The main loops' rounds over more blocks interleave `polyBlock` with two halves of a double round that stay inline in `sealNamed` and `openNamed`: name those halves first, each proven equal by `rfl` as the rest are, then prove them.
  - The keystream XOR and stores (`ld1`, `eor`, `st1`), and the ciphertext hash loops, which run `polyBlock` or `umovs ++ polyAdd ++ polyMul` (`hash_ok`) over the ciphertext as `ad_ok` does over the AAD, then the lengths block and the tag.
  - Compose the paths: seal's 128-byte, initial, main-loop, and tail paths, open's likewise, each a `seqs` of the blocks above.
  - A throwaway interpreter for `Code` ran both programs in the model against the spec at 22 lengths from 1 to 1000 bytes, every branch path, all matching: the model and the programs agree with RFC 8439 at those lengths.
- Then restate the theorems in `Rind/Aarch64/` as axioms about `seal_aws_lc` and `open_aws_lc` that give `AwsLc`, as `Rind/Aarch64/Sha256Hw.lean` restates SHA-256's, and record them in `Axioms.lean`. Add the `verified.toml` entry for `chacha20poly1305/*` and `xchacha20poly1305/*` on aarch64 without SVE2 (`cpu = ["!sve2"]`), replacing the epic's 1350 B and 16 KB one if it has landed. Until `kixtop` is measured at a revision with [kixel-ai/rind#1023](https://github.com/kixel-ai/rind/pull/1023), which moved those two rows to VG's NEON routine, the entry leaves them out, as the epic's README and `benchmarks/verified.toml` say.
- Seal and open are 1,172 and 1,813 instruction words with the inlined helper and alignment.

## Related

- [aws-lc's ChaCha20-Poly1305 seal and open are proven on x86_64](/quest/m4/verified/chacha20-poly1305-x86/aead.md) - the same routines' x86_64 halves, on the same route; `Rind/Aarch64/Taint.lean`'s checker ports to `RindIsa/X86_64` for its leakage half
