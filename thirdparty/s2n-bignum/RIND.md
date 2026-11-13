# rind's fork of s2n-bignum

This directory is rind's fork of
[s2n-bignum](https://github.com/awslabs/s2n-bignum), on which rind's HOL Light
proofs build, from which `admin/parse-asm` transliterates rind's s2n-bignum
routines, and whose proofs `admin/prove bytes` checks rind's code against.

Base: `b4f17ee743ebc9b53a26c3cd1908f50f0658314f`

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

### Instructions from awslabs/s2n-bignum#450

#450's changes to the three model files at
`7ef212f3f517635c57174475f413c74013ae79a5`, merged onto the base with every
line it adds or removes unchanged but two lines of `x86.ml`'s instruction
list, which also name rind's instructions, since its files branch from `7948ca13` and
would otherwise revert three later upstream commits to them (#429, #438, and
#452). They add `SHA256RNDS2`, `SHA256MSG1`, `SHA256MSG2`, and the legacy SSE
`PALIGNR`, `PUNPCKLQDQ`, and `PUNPCKHQDQ`, which x86_64's SHA-NI SHA-256
blocks run. #450's decoders of its three legacy SSE instructions also take
the MMX form without the 66 prefix, which no proven routine runs, where
rind's decoders below refuse it.

### rind's instructions

What aws-lc's x86_64 ChaCha20-Poly1305 and ChaCha20 routines need,
`chacha20_poly1305_{seal,open}`, `poly_hash_ad_internal`, and
`ChaCha20_ctr32_ssse3_4x` (maintainer, 2026-11-11, on
[kixel-ai/rind#627](https://github.com/kixel-ai/rind/pull/627)). With them
every instruction of those routines, as rind's release build emits them,
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
| `PUNPCKLDQ xmm, xmm/m128` | 66 0F 62 /r | |
| `PUNPCKHDQ xmm, xmm/m128` | 66 0F 6A /r | |
| `VBROADCASTI128 ymm, m128` | VEX.256.66.0F38.W0 5A /r | |
| `RET` with the F3 prefix | F3 C3 | aws-lc's `rep ret`, which every CPU runs as `RET` |

The legacy SSE forms write only the low 128 bits of their register, as the
model's other legacy SSE instructions do, and decode only with the 66 prefix
and no other, where #439 also takes the MMX form without it.
`OPERAND_SIZE_CASES` gains the 32-or-8-bit operand case `PINSRB` and
`PEXTRB` dispatch on. `rind_cosim.ml` checks every row but the last.
