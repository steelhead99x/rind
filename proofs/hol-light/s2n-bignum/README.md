# What rind carries for s2n-bignum

rind's HOL Light proofs build on
[s2n-bignum](https://github.com/awslabs/s2n-bignum) at the commit of rind's
`thirdparty/s2n-bignum` submodule. This directory holds everything rind adds
to it, each listed below so it can be offered upstream. HOL Light loads it
ahead of the submodule.

## Specs from unmerged pull requests

Each is the pull request's file unchanged, at its path in s2n-bignum, so a
submodule bump past its merge deletes it.

- `x86/proofs/utils/sha256_spec.ml`: SHA-256's FIPS 180-4 spec, from
  [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415) at
  `79120e64ed55e37c9652565ff272b7ef17f76738`.

## rind's additions to the x86 model

`x86.patch` adds what aws-lc's x86_64 ChaCha20-Poly1305 and ChaCha20 routines
need, `chacha20_poly1305_{seal,open}`, `poly_hash_ad_internal`, and
`ChaCha20_ctr32_ssse3_4x`, to `x86/proofs/instruction.ml`, `decode.ml`, and
`x86.ml` (maintainer, 2026-11-11, on
[moq-dev/rind#627](https://github.com/moq-dev/rind/pull/627)). Under it every
instruction of those routines, as rind's release build emits them, decodes.
`admin/prove` applies it to the files it changes, where this directory
vendors one, or else to the submodule's, and fails unless every hunk applies
exactly, so a submodule bump that touches them means redoing it.

| Instruction | Encoding | Note |
| --- | --- | --- |
| `PALIGNR xmm, xmm/m128, imm8` | 66 0F 3A 0F /r ib | semantics as in [awslabs/s2n-bignum#450](https://github.com/awslabs/s2n-bignum/pull/450) |
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
| `PUNPCKLQDQ xmm, xmm/m128` | 66 0F 6C /r | semantics as in #450 |
| `PUNPCKHQDQ xmm, xmm/m128` | 66 0F 6D /r | semantics as in #450 |
| `VBROADCASTI128 ymm, m128` | VEX.256.66.0F38.W0 5A /r | |
| `RET` with the F3 prefix | F3 C3 | aws-lc's `rep ret`, which every CPU runs as `RET` |

The legacy SSE forms write only the low 128 bits of their register, as the
model's other legacy SSE instructions do, and decode only with the 66 prefix
and no other, where #439 and #450 also take the MMX form without it.
`OPERAND_SIZE_CASES` gains the 32-or-8-bit operand case `PINSRB` and
`PEXTRB` dispatch on.

`x86-cosim.ml` checks every row but the last against the CPU, as s2n-bignum
checks its own instructions: `nix develop .#hol-light --command admin/prove
cosim`, which the `prove` workflow runs. Offering the patch upstream would
also add its encodings to s2n-bignum's `x86/proofs/simulator.ml`, as
s2n-bignum's own additions do. Posting to awslabs/s2n-bignum needs the
maintainer's approval
([moq-dev/rind#448](https://github.com/moq-dev/rind/pull/448)).
