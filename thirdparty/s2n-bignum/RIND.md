# rind's fork of s2n-bignum

This directory is rind's fork of
[s2n-bignum](https://github.com/awslabs/s2n-bignum), on which rind's HOL Light
proofs build, from which `admin/parse-asm` transliterates rind's s2n-bignum
routines, and whose proofs `admin/prove bytes` checks rind's code against.

Base: `3f01260ff1bd2577abf0117ce45aa008bc243a80`

Every file here is upstream's at that commit, unchanged, except this one and
those listed under "Changed files", so each change can be offered upstream.
`admin/regenerate` fails unless that holds: each file this lists differs from
upstream's, or one of them lacks it, and every other file of either is the
same in both.

## Moving the base

The fork holds upstream's whole tree, so moving the base is a merge: apply
upstream's changes from the base to the new commit, which
`admin/upstream s2n-bignum <commit>` checks out into
`.tmp/upstream/s2n-bignum@<commit>`, resolve them against each change below,
delete a change upstream has merged, set the base above, and run
`admin/regenerate` and `admin/prove`.

## Changed files

Each bullet names one file.

- `x86/proofs/instruction.ml`: the two sets of instructions below.
- `x86/proofs/decode.ml`: their decoders.
- `x86/proofs/x86.ml`: their semantics.
- `x86/proofs/simulator.ml`: the CPU features `ANDN`, `RORX`, `SHLX`, and
  `SHRX` need, BMI1 and BMI2, so cosimulation skips them on a CPU without
  those, as it does upstream's other instructions.
- `x86/proofs/utils/sha256_spec.ml`: SHA-256's FIPS 180-4 spec, from
  [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415) at
  `79120e64ed55e37c9652565ff272b7ef17f76738`, unchanged.
  [awslabs/s2n-bignum#450](https://github.com/awslabs/s2n-bignum/pull/450)
  carries the same file but for one comment line, so this copy serves both.
- `x86/proofs/utils/sha512_spec.ml`: SHA-512's FIPS 180-4 spec, from
  [awslabs/s2n-bignum#420](https://github.com/awslabs/s2n-bignum/pull/420) at
  `7ef7ba7c2d830d9c713512035ae6eb4aa8fe0a2b`, unchanged.
- `common/chacha20poly1305.ml`: rind's. RFC 8439's ChaCha20, Poly1305, and
  AEAD_CHACHA20_POLY1305 on byte lists, which rind's proofs of aws-lc's
  ChaCha20-Poly1305 and ChaCha20 routines state their results against, with
  `CHACHA20_POLY1305_CONV`, which evaluates them on literals, and known-answer
  tests from the RFC's sections 2.4.2, 2.5.2, and 2.8.2, which run as it
  loads. Like `common/bignum.ml`, it loads after an architecture's
  `proofs/base.ml`. `proofs/Rind/S2nChaCha20Poly1305.lean` proves it is
  `proofs/Rind/Spec.lean`'s.
- `x86/proofs/rind_cosim.ml`: rind's. It cosimulates both sets of
  instructions below against the CPU, as s2n-bignum checks its own, the SHA
  extensions only where the CPU has them: `nix develop .#hol-light --command
  admin/prove cosim`, which the `prove` workflow runs. For those it evaluates
  #450's SHA-256 operations on constants, which the simulator's
  simplification leaves folded. Offered upstream, its encodings would join
  `x86/proofs/simulator.ml`'s, as s2n-bignum's own additions do.
- `aarch32/proofs/instruction.ml`: rind's. The AArch32 model's state and the
  semantics of the instructions below, from the Arm Architecture Reference
  Manual's AArch32 pseudocode (DDI 0487, part F).
- `aarch32/proofs/decode.ml`: rind's. Their A32 encodings.
- `aarch32/proofs/aarch32.ml`: rind's. The step relation, symbolic-execution
  tactics, and AAPCS argument and clobber lists.
- `aarch32/proofs/consttime.ml`: rind's. s2n-bignum's safety tactics
  specialized to the model.
- `aarch32/proofs/base.ml`: rind's. What a proof on the model loads.
- `aarch32/proofs/simulator.ml`: rind's. The model's cosimulation against
  qemu-arm.
- `aarch32/proofs/cosim_runner.c`: rind's. The cosimulation's executor, a
  static armv7 program.
- `aarch32/proofs/cosim_start.S`: rind's. That program's entry point.

### Instructions from awslabs/s2n-bignum#450

#450's changes to the three model files at
`7ef212f3f517635c57174475f413c74013ae79a5`, merged onto the base, since its
files branch from `7948ca13` and would otherwise revert later upstream
commits to them. They add `SHA256RNDS2`, `SHA256MSG1`, `SHA256MSG2`, and the
legacy SSE `PALIGNR`, `PUNPCKLQDQ`, and `PUNPCKHQDQ`, which x86_64's SHA-NI
SHA-256 blocks run. Every line #450 adds or removes is unchanged but these,
which follow upstream commits since #450 branched: `x86.ml`'s instruction
list, which also names rind's instructions and the `_ALT` shift theorems of
upstream's `3888c57`; its decoders, which match the prefixes exactly, as
upstream's `caeca8c` does its own, so the three SHA instructions decode only
without a prefix and the three legacy SSE ones only with 66, where #450's
also take the MMX form; and their execution, which as upstream's `64e533b`
requires a 16-byte memory source to be aligned.

### rind's instructions

What aws-lc's x86_64 ChaCha20-Poly1305 and ChaCha20 routines need,
`chacha20_poly1305_{seal,open}`, `poly_hash_ad_internal`, and
`ChaCha20_ctr32_ssse3_4x` (maintainer, 2026-11-11, on
[kixel-ai/rind#627](https://github.com/kixel-ai/rind/pull/627)), its
AES-CTR and AES-CBC routines, `aes_hw_ctr32_encrypt_blocks` and
`aes_hw_cbc_encrypt`, and what OpenSSL's `sha512_block_data_order_avx2`
adds to them: BMI1's `ANDN`, BMI2's `RORX`, and `PUSH m64`. With them every instruction of those
routines, as rind's release build emits them,
decodes. Posting them to awslabs/s2n-bignum needs the maintainer's approval
([kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

| Instruction | Encoding | Note |
| --- | --- | --- |
| `VPALIGNR xmm/ymm, xmm/ymm, xmm/ymm/m, imm8` | VEX.128/256.66.0F3A.WIG 0F /r ib | `PALIGNR` in each 128-bit lane |
| `PSLLD xmm, imm8` | 66 0F 72 /6 ib | |
| `PSRLD xmm, imm8` | 66 0F 72 /2 ib | |
| `PSLLDQ xmm, imm8` | 66 0F 73 /7 ib | semantics as in [awslabs/s2n-bignum#439](https://github.com/awslabs/s2n-bignum/pull/439) |
| `PSRLDQ xmm, imm8` | 66 0F 73 /3 ib | semantics as in #439 |
| `PINSRB xmm, r32/m8, imm8` | 66 0F 3A 20 /r ib | REX.W refused |
| `PEXTRB r32/m8, xmm, imm8` | 66 0F 3A 14 /r ib | REX.W refused |
| `PEXTRQ r/m64, xmm, imm8` | 66 REX.W 0F 3A 16 /r ib | |
| `POR xmm, xmm/m128` | 66 0F EB /r | |
| `PANDN xmm, xmm/m128` | 66 0F DF /r | |
| `PCMPEQD xmm, xmm/m128` | 66 0F 76 /r | |
| `PUNPCKLDQ xmm, xmm/m128` | 66 0F 62 /r | |
| `PUNPCKHDQ xmm, xmm/m128` | 66 0F 6A /r | |
| `SHLX r32/r64, r/m32/m64, r32/r64` | VEX.LZ.66.0F38.W0/W1 F7 /r | BMI2; the count masked to the width, flags unchanged |
| `SHRX r32/r64, r/m32/m64, r32/r64` | VEX.LZ.F2.0F38.W0/W1 F7 /r | BMI2; the count masked to the width, flags unchanged |
| `VBROADCASTI128 ymm, m128` | VEX.256.66.0F38.W0 5A /r | |
| `ANDN r32/64, r32/64, r/m32/64` | VEX.LZ.0F38.W0/W1 F2 /r | sets SF and ZF, clears OF and CF, AF and PF undefined |
| `RORX r32/64, r/m32/64, imm8` | VEX.LZ.F2.0F3A.W0/W1 F0 /r ib | leaves the flags |
| `PUSH r/m64` | FF /6 | the memory form; the model already decodes the register one |
| `RET` with the F3 prefix | F3 C3 | aws-lc's `rep ret`, which every CPU runs as `RET` |
| `XORPS xmm, xmm/m128` | 0F 57 /r | decoded as `PXOR`, the same bitwise XOR of the low 128 bits |
| `PREFETCHT0 m8` | 0F 18 /1 | decoded as `NOP_N`: a prefetch changes no architectural state |
| `STOSB`, `REP STOSB` | AA, F3 AA | allows every next state, a sound over-approximation: it decodes so the code after it can be stepped, and a proof that reaches it proves nothing |

The legacy SSE forms write only the low 128 bits of their register, as the
model's other legacy SSE instructions do, decode only with the 66 prefix
and no other (`XORPS` only with none), where #439 also takes the MMX form
without it, and, as
upstream's own since `64e533b`, take a 16-byte memory source only aligned.
`OPERAND_SIZE_CASES` gains the 32-or-8-bit operand case `PINSRB` and
`PEXTRB` dispatch on. `rind_cosim.ml` checks every row but `RET` and `STOSB`.

### rind's AArch32 model

`aarch32/proofs/` models the A32 instructions armv7's proofs need, after
s2n-bignum's RV32IM model in `riscv/proofs/` and on the 32-bit infrastructure
[awslabs/s2n-bignum#452](https://github.com/awslabs/s2n-bignum/pull/452)
added. The state is R0-R12, SP, LR, PC, the N, Z, C, and V flags, memory, and
the event trace s2n-bignum's safety proofs read.

| Instructions | Forms |
| --- | --- |
| `AND`, `EOR`, `SUB`, `RSB`, `ADD`, `ADC`, `SBC`, `RSC`, `ORR`, `BIC`, and their `S` forms | register with an immediate shift, or a modified immediate |
| `TST`, `TEQ`, `CMP`, `CMN` | the same operands |
| `MOV`, `MVN`, and their `S` forms | the same operands |
| `MOVW`, `MOVT` | 16-bit immediate |
| `LDR`, `LDRB`, `STR`, `STRB` | 12-bit immediate offset, pre-indexed, or post-indexed |
| `B` | 24-bit offset |

Each takes any condition but the unconditional space. The decoder refuses
everything else: Thumb, register-shifted registers, PC as an operand or
destination, `LDRT` and the other unprivileged forms, write-back to the
transferred register, and every other encoding. Loads and stores may be
unaligned, as Linux and Android leave them.

`simulator.ml` cosimulates the model as s2n-bignum's
`riscv/proofs/simulator.ml` does its own: directed cases at the shifts' and
carries' edges, a backward branch, and unaligned word loads and stores, then
random instructions from every row above, each with a random condition and
state, branches forward and back and word offsets unaligned, which
`cosim_runner.c` and `cosim_start.S` run under qemu-arm, and the model must
prove reach the same state. `admin/prove cosim` runs 1000 random cases,
printing the seed, which
`S2N_BIGNUM_SEMATEST_SEED` repeats. Offering the model upstream is also a
post to awslabs/s2n-bignum, which needs the maintainer's approval.
