module

public import VerifiedGarbage.TCB.X86_64.Avx

/-!
# x86-64 AVX-512 instructions

**Trusted.** The EVEX-encoded (AVX-512F, AVX-512BW, VAES and VPCLMULQDQ) instructions of the x86-64 model in
`TCB/X86_64/Isa.lean` that write only vector registers, all with 512-bit
(`zmm`) operands and no masking, and the operations of those with an
embedded-broadcast memory operand (`ZBcstOp`, which `Isa.lean` runs since
they read memory).
-/

@[expose] public section

namespace VG.X86_64

/-- EVEX-encoded three-operand instructions `vop zmm, zmm, zmm` that act on
each 128-bit lane as the legacy SSE instruction does on its destination
(`src1`) and source (`src2`). -/
inductive ZBinOp
  | vpaddd | vpxord | vpunpckldq | vpunpckhdq | vpunpcklqdq | vpunpckhqdq
  | vpaddq | vpmuludq | vpandq | vporq | vpandnq
  | vaesenc | vaesenclast | vaesdec | vaesdeclast | vpshufb
  | vpsubq
  deriving DecidableEq, Repr

/-- EVEX-encoded shifts of each quadword by an immediate count,
`vop zmm1, zmm2, imm8`. -/
inductive ZShiftOp | vpsllq | vpsrlq
  deriving DecidableEq, Repr

/-- The EVEX.512 operations with their second source in `zmm16`–`zmm31`, as
needed to keep AES round keys and constants there.
Intel SDM Vol. 2, "PXOR" (`EVEX.512.66.0F.W0 EF /r`), "AESENC" and
"AESENCLAST" (`EVEX.512.66.0F38.WIG DC/DD /r`), "PADDB/PADDW/PADDD/PADDQ"
(VPADDD, `EVEX.512.66.0F.W0 FE /r`: `DEST[i+31:i] := SRC1[i+31:i] +
SRC2[i+31:i]` for each doubleword, no write mask nor embedded broadcast, a
register second source): the register source is selected by the five-bit
EVEX register specifier (Vol. 2 §2.7.1).
The unmasked operations apply PXOR, AESENC, AESENCLAST or PADDD independently
to each 128-bit lane, exactly as `ZBinOp` does for registers 0–15. -/
inductive ZKeyOp | vpxord | vaesenc | vaesenclast | vpaddd
  deriving DecidableEq, Repr

def ZKeyOp.sse : ZKeyOp → XBinOp
  | .vpxord => .pxor | .vaesenc => .aesenc | .vaesenclast => .aesenclast | .vpaddd => .paddd

/-- AVX-512 instructions with 512-bit operands that write only vector
registers. None is masked: the opmask is `k0` (`EVEX.aaa = 000`), so every
element of the destination is written. -/
inductive ZOp
  /-- `vop zmm1, zmm2, zmm3` -/
  | zbin (op : ZBinOp) (dst src1 src2 : XReg)
  /-- An unmasked EVEX.512 operation with its second source in `zmm16`–`zmm31`. -/
  | zbinH (op : ZKeyOp) (dst src1 : XReg) (src2 : HReg)
  /-- `vpclmulqdq zmm1, zmm2, zmm3, imm8` (EVEX.512, unmasked). -/
  | vpclmulqdq (dst src1 src2 : XReg) (sel : BitVec 8)
  /-- `vprold zmm1, zmm2, imm8` (`EVEX.512.66.0F.W0 72 /1 ib`) -/
  | vprold (dst src : XReg) (count : BitVec 8)
  /-- `vpshufd zmm1, zmm2, imm8` (`EVEX.512.66.0F.W0 70 /r ib`) -/
  | vpshufd (dst src : XReg) (order : BitVec 8)
  /-- `vshufi32x4 zmm1, zmm2, zmm3, imm8` (`EVEX.512.66.0F3A.W0 43 /r ib`) -/
  | vshufi32x4 (dst src1 src2 : XReg) (sel : BitVec 8)
  /-- `vpsllq zmm1, zmm2, imm8` (`EVEX.512.66.0F.W1 73 /6 ib`) or `vpsrlq zmm1,
  zmm2, imm8` (`EVEX.512.66.0F.W1 73 /2 ib`) -/
  | vshift (op : ZShiftOp) (dst src : XReg) (count : BitVec 8)
  /-- `vpslldq zmm1, zmm2, imm8` (EVEX.512, lane-wise). -/
  | vpslldq (dst src : XReg) (count : BitVec 8)
  /-- `vpsrldq zmm1, zmm2, imm8` (EVEX.512, lane-wise). -/
  | vpsrldq (dst src : XReg) (count : BitVec 8)
  /-- `vpbroadcastq zmm1, xmm2` (`EVEX.512.66.0F38.W1 59 /r`) -/
  | vpbroadcastq (dst src : XReg)
  /-- `vmovdqa64 zmm1, zmm2` (`EVEX.512.66.0F.W1 6F /r`) -/
  | vmovdqa64 (dst src : XReg)
  /-- `vpternlogd zmm1, zmm2, zmm3, imm8` (`EVEX.512.66.0F3A.W0 25 /r ib`):
  each bit of `zmm1` is the bit of `imm8` that the bits of `zmm1`, `zmm2`
  and `zmm3` there index (see `ternlog`). -/
  | vpternlogd (dst src1 src2 : XReg) (imm : BitVec 8)
  /-- `vprorq zmm1, zmm2, imm8` (`EVEX.512.66.0F.W1 72 /0 ib`): each
  quadword of `zmm2` rotated right by `imm8` modulo 64 (see `rorQwords`). -/
  | vprorq (dst src : XReg) (count : BitVec 8)
  /-- `vpermq zmm1, zmm2, imm8` (`EVEX.512.66.0F3A.W1 00 /r ib`): the
  quadwords of each 256-bit half of `zmm2` permuted by `imm8` (see
  `ZOp.exec`). -/
  | vpermq (dst src : XReg) (order : BitVec 8)
  /-- `vpmadd52luq zmm1, zmm2, zmm3` (`EVEX.512.66.0F38.W1 B4 /r`), or with `hi`
  `vpmadd52huq zmm1, zmm2, zmm3` (`EVEX.512.66.0F38.W1 B5 /r`); AVX512_IFMA:
  each quadword of `zmm1` plus the low (or high) 52 bits of the 104-bit product
  of the low 52 bits of the quadwords of `zmm2` and `zmm3` (see `madd52`). -/
  | vpmadd52 (hi : Bool) (dst src1 src2 : XReg)
  /-- `vpermw zmm1, zmm2, zmm3` (`EVEX.512.66.0F38.W1 8D /r`), AVX512BW:
  word `j` of `zmm1` is the word of `zmm3` that bits 4:0 of word `j` of
  `zmm2` index (see `permWord`). -/
  | vpermw (dst idx src : XReg)
  /-- `vpsrlvw zmm1, zmm2, zmm3` (`EVEX.512.66.0F38.W1 10 /r`), AVX512BW:
  each word of `zmm2` shifted right by the same word of `zmm3`, zero for a
  count above 15 (see `srlvWord`). -/
  | vpsrlvw (dst src cnt : XReg)
  /-- `vextracti32x4 xmm1, zmm2, imm8` (`EVEX.512.66.0F3A.W0 39 /r ib`),
  AVX512F, with a register destination: lane `imm8[1:0]` of `zmm2`, and
  the rest of the destination zeroed. -/
  | vextracti32x4 (dst src : XReg) (sel : BitVec 8)
  deriving DecidableEq, Repr

/-- Word `j` (bits `16j+15:16j`, for `j` from 0 to 31) of `zmm r`: word
`j % 8` of its lane `j / 8`. -/
def State.zword (s : State) (r : XReg) (j : Nat) : BitVec 16 := word (s.zlane r (j / 8)) (j % 8)

/-- SDM Vol. 2, "VPERMB/VPERMW/VPERMD/VPERMQ", "VPERMW (EVEX encoded
versions)" with `VL = 512` (`KL = 32`, `id := 4`), no write mask and a
register `SRC2`: `FOR j := 0 TO KL-1: i := j * 16; id := SRC1[i+id:i];
DEST[i+15:i] := SRC2[id*16+15:id*16]`: word `j` of the result, of `SRC1`
(`zmm2`, the indices) `a` and `SRC2` (`zmm3`) `b`. -/
def State.permWord (s : State) (a b : XReg) (j : Nat) : BitVec 16 := s.zword b ((s.zword a j).toNat % 32)

/-- SDM Vol. 2, "VPSRLVW/VPSRLVD/VPSRLVQ", "VPSRLVW (EVEX encoded version)"
with `(KL, VL) = (32, 512)`, no write mask and a register `SRC2`: `FOR j :=
0 TO KL-1: i := j * 16; DEST[i+15:i] := ZeroExtend(SRC1[i+15:i] >>
SRC2[i+15:i])`, where (the operation's description) "if the unsigned value
of the variable shift count exceeds 15, the result is 0": word `j` of the
result, of `SRC1` `a` and `SRC2` `b`. -/
def State.srlvWord (s : State) (a b : XReg) (j : Nat) : BitVec 16 :=
  let c := (s.zword b j).toNat
  if c < 16 then s.zword a j >>> c else 0

/-- The legacy SSE instruction whose operation `op` applies to each lane:
VPADDD, VPXORD, VPUNPCK{L,H}{DQ,QDQ}, VPADDQ, VPMULUDQ, VPANDQ, VPORQ and
VPANDNQ are, lane by lane, PADDD, PXOR, PUNPCK{L,H}{DQ,QDQ}, PADDQ, PMULUDQ,
PAND, POR and PANDN, and VPSUBQ is PSUBQ (SDM Vol. 2, each instruction's "EVEX.512 encoded
version" pseudocode, with `SRC1` in place of the destination and no write
mask nor embedded broadcast, the second source being a register: VPADDD and
VPXORD act on each doubleword; VPADDQ (`DEST[i+63:i] := SRC1[i+63:i] +
SRC2[i+63:i]`), VPSUBQ ("PSUBB/PSUBW/PSUBD/PSUBQ", `EVEX.512.66.0F.W1 FB /r`:
`DEST[i+63:i] := SRC1[i+63:i] - SRC2[i+63:i]`), VPANDQ, VPORQ and VPANDNQ
(`DEST[i+63:i] := ((NOT SRC1[i+63:i]) BITWISE AND SRC2[i+63:i])`) on each
quadword, which on each 128-bit lane is what PADDQ, PSUBQ, PAND, POR and PANDN
compute; VPMULUDQ
(`DEST[i+63:i] := ZeroExtend64( SRC1[i+31:i]) * ZeroExtend64( SRC2[i+31:i]
)`) multiplies the low doublewords of each quadword, as PMULUDQ does on
each lane's two; and VPUNPCK* interleave the elements of each 128-bit lane
as the VEX.256 forms do on two). -/
def ZBinOp.sse : ZBinOp → XBinOp
  | .vpaddd => .paddd | .vpxord => .pxor
  | .vpunpckldq => .punpckldq | .vpunpckhdq => .punpckhdq
  | .vpunpcklqdq => .punpcklqdq | .vpunpckhqdq => .punpckhqdq
  | .vpaddq => .paddq | .vpmuludq => .pmuludq | .vpandq => .pand | .vporq => .por
  | .vpandnq => .pandn
  | .vaesenc => .aesenc | .vaesenclast => .aesenclast | .vaesdec => .aesdec
  | .vaesdeclast => .aesdeclast | .vpshufb => .pshufb
  | .vpsubq => .psubq

/-! Intel SDM Vol. 2, "AESENC", "AESENCLAST", "AESDEC", "AESDECLAST" and
"PCLMULQDQ": EVEX.512 VAESENC/VAESENCLAST, VAESDEC/VAESDECLAST
(`EVEX.512.66.0F38.WIG DE /r`, `DF /r`) and VPCLMULQDQ apply the same
operation as VEX to all four 128-bit lanes (see `Avx.lean`), without
masking.
"PSHUFB" (EVEX.512) selects bytes within each 128-bit lane, zeroing an
output byte if the corresponding selector's bit 7 is set (`XBinOp.pshufb`).
"PSLLDQ"/"PSRLDQ" (EVEX.512) shift each 128-bit lane by imm8 bytes,
zero-filling, with counts above 15 yielding zero (`XShiftOp.eval`).
These byte operations require AVX512BW, unlike the quadword shifts. -/

/-- The legacy SSE shift whose operation `op` applies to each lane: SDM Vol.
2, "PSLLW/PSLLD/PSLLQ" and "PSRLW/PSRLD/PSRLQ", "VPSLLQ (EVEX versions,
imm8)": `DEST[i+63:i] := LOGICAL_LEFT_SHIFT_QWORDS(SRC1[i+63:i], imm8)` for
each quadword (no write mask, a register source), and VPSRLQ likewise with
`LOGICAL_RIGHT_SHIFT_QWORDS`: on each 128-bit lane what PSLLQ and PSRLQ
compute (a count above 63 gives zero). -/
def ZShiftOp.sse : ZShiftOp → XShiftOp
  | .vpsllq => .psllq | .vpsrlq => .psrlq

/-- EVEX-encoded three-operand instructions `vop zmm, zmm, m64bcst` whose
second source is a quadword in memory broadcast to every element
(`QWORD PTR [m]{1to8}`, `EVEX.b = 1`); see `ZBcstOp.sse`. -/
inductive ZBcstOp
  | vpmuludq | vpandq | vporq
  deriving DecidableEq, Repr

/-- The legacy SSE instruction whose operation `op` applies to each lane,
with the loaded quadword in both quadwords of its source. SDM Vol. 2, each
instruction's "EVEX encoded versions" pseudocode with `(KL, VL) = (8, 512)`,
no write mask and a memory `SRC2` with `EVEX.b = 1`, for each quadword
`j` from 0 to 7 (`i := j * 64`):

* VPMULUDQ ("PMULUDQ"): `IF (EVEX.b = 1) AND (SRC2 *is memory*) THEN
  DEST[i+63:i] := ZeroExtend64( SRC1[i+31:i]) * ZeroExtend64( SRC2[31:0] )`.
* VPANDQ ("PAND"): `IF (EVEX.b = 1) AND (SRC2 *is memory*) THEN
  DEST[i+63:i] := SRC1[i+63:i] BITWISE AND SRC2[63:0]`.
* VPORQ ("POR/VPOR/VPORD/VPORQ"): the SDM gives the pseudocode of VPORD
  only, `IF (EVEX.b = 1) AND (SRC2 *is memory*) THEN DEST[i+31:i] :=
  SRC1[i+31:i] BITWISE OR SRC2[31:0]` for each doubleword (`i := j * 32`),
  and describes VPORQ as the same on quadwords, its source "a 512/256/128-bit
  vector broadcasted from a 32/64-bit memory location" (the 64-bit one for
  VPORQ): `DEST[i+63:i] := SRC1[i+63:i] BITWISE OR SRC2[63:0]` with
  `i := j * 64`, as VPANDQ.

Each quadword of `DEST` is that of `SRC1` combined with `SRC2[63:0]`, so
on each 128-bit lane this is PMULUDQ, PAND and POR (`XBinOp.eval`) of the
lane of `SRC1` and `SRC2[63:0]` twice: PMULUDQ multiplies the low
doubleword of each quadword, and the low doubleword of `SRC2[63:0]` is
`SRC2[31:0]`. -/
def ZBcstOp.sse : ZBcstOp → XBinOp
  | .vpmuludq => .pmuludq | .vpandq => .pand | .vporq => .por

/-- EVEX-encoded three-operand instructions `vop zmm, zmm, m32bcst` whose
second source is a doubleword in memory broadcast to every doubleword
(`DWORD PTR [m]{1to16}`, `EVEX.b = 1`); see `ZBcstDOp.sse`. -/
inductive ZBcstDOp
  | vpaddd
  deriving DecidableEq, Repr

/-- The legacy SSE instruction whose operation `op` applies to each lane,
with the loaded doubleword in all four doublewords of its source. SDM
Vol. 2, "PADDB/PADDW/PADDD/PADDQ", "VPADDD (EVEX Encoded Versions)" with
`(KL, VL) = (16, 512)`, no write mask and a memory `SRC2` with
`EVEX.b = 1`: `IF (EVEX.b = 1) AND (SRC2 *is memory*) THEN DEST[i+31:i] :=
SRC1[i+31:i] + SRC2[31:0]` for each doubleword `j` from 0 to 15
(`i := j * 32`). Each doubleword of `DEST` is that of `SRC1` plus
`SRC2[31:0]`, so on each 128-bit lane this is PADDD (`XBinOp.eval`) of the
lane of `SRC1` and `SRC2[31:0]` four times. -/
def ZBcstDOp.sse : ZBcstDOp → XBinOp
  | .vpaddd => .paddd

/-- SDM Vol. 2, "VSHUFF32x4/VSHUFF64x2/VSHUFI32x4/VSHUFI64x2", 512-bit form:
`Select4(SRC, control) { CASE (control[1:0]) OF 0: TMP := SRC[127:0]; 1:
TMP := SRC[255:128]; 2: TMP := SRC[383:256]; 3: TMP := SRC[511:384]; }`,
`DEST[127:0] := Select4(SRC1, imm8[1:0]); DEST[255:128] := Select4(SRC1,
imm8[3:2]); DEST[383:256] := Select4(SRC2, imm8[5:4]); DEST[511:384] :=
Select4(SRC2, imm8[7:6])`. Here `a i` and `b i` are lane `i` of `SRC1` and
`SRC2`, and the result is lane `j` of `DEST`. -/
def shuf4Lanes (a b : Nat → BitVec 128) (sel : BitVec 8) (j : Nat) : BitVec 128 :=
  let k := (sel.extractLsb' (2 * j) 2).toNat
  if j < 2 then a k else b k

/-- Semantics of an AVX-512 instruction that writes only vector registers.
SDM Vol. 2 (no flags are affected; with 512-bit operands the whole of
`DEST[511:0]` is written):

* The lane-wise instructions: see `ZBinOp.sse`, `rolDwords` (VPROLD) and
  `shufDwords` (VPSHUFD: "EVEX.512 encoded version", each lane with the
  same `imm8`).
* VAESENC/VAESENCLAST, VPCLMULQDQ, VPSHUFB, VPSLLDQ and VPSRLDQ:
  see the vector AES/GCM description above.
* VSHUFI32X4: see `shuf4Lanes`.
* VPSLLQ and VPSRLQ: see `ZShiftOp.sse`.
* VPBROADCASTQ (EVEX.512 encoded version, register source, no write mask):
  every quadword of `DEST` is `SRC[63:0]`.
* VMOVDQA64 (EVEX.512 encoded version, register to register, no write
  mask): `DEST[511:0] := SRC[511:0]`.
* VPTERNLOGD (EVEX.512 encoded version, register `SRC2`, no write mask):
  see `ternlog`, each lane (the SDM's loop over the sixteen doublewords of
  the 512-bit form, `KL, VL = 16, 512`, computes each bit from the same bits
  of `DEST`, `SRC1` and `SRC2`, so lane by lane).
* VPRORQ (EVEX.512 encoded version, immediate count, register source, no
  write mask): see `rorQwords`, each lane.
* VPERMQ ("VPERMQ (EVEX - imm8 control forms)", `VL = 512`, register
  source, no write mask): `TMP_DEST[63:0] := (TMP_SRC[255:0] >> (IMM8[1:0] *
  64))[63:0]; …; TMP_DEST[255:192] := (TMP_SRC[255:0] >> (IMM8[7:6] *
  64))[63:0]; IF VL >= 512 TMP_DEST[319:256] := (TMP_SRC[511:256] >>
  (IMM8[1:0] * 64))[63:0]; …; TMP_DEST[511:448] := (TMP_SRC[511:256] >>
  (IMM8[7:6] * 64))[63:0]`, with `TMP_SRC := SRC`: each 256-bit half of
  `DEST` is the same half of `SRC` permuted as VEX.256 VPERMQ permutes a
  register (`permQwords`).
* VPERMW and VPSRLVW: see `permWord` and `srlvWord`, each word of the
  destination (word `8i + k` is word `k` of lane `i`).
* VEXTRACTI32X4 ("VEXTRACTI32x4 (EVEX encoded versions) when destination
  is a register", `VL = 512`, no write mask): `CASE (imm8[1:0]) OF 00:
  TMP_DEST[127:0] := SRC1[127:0]; 01: TMP_DEST[127:0] := SRC1[255:128]; 10:
  TMP_DEST[127:0] := SRC1[383:256]; 11: TMP_DEST[127:0] := SRC1[511:384];
  ESAC. DEST[127:0] := TMP_DEST[127:0]; DEST[MAXVL-1:128] := 0`.
* VPMADD52LUQ and VPMADD52HUQ ("EVEX encoded version", `(KL, VL) = (8,
  512)`, no write mask, a register `SRC3`): `temp128 :=
  ZeroExtend64(SRC2[i+51:i]) * ZeroExtend64(SRC3[i+51:i]); DEST[i+63:i] :=
  DEST[i+63:i] + ZeroExtend64(temp128[51:0])` (`temp128[103:52]` for
  VPMADD52HUQ) for each of the eight quadwords: `madd52` on each lane, as the
  256-bit forms (`Avx.lean`) on two. -/
def ZOp.exec : ZOp → State → State
  | .zbinH op d a b, s =>
    let f (i : Nat) := op.sse.eval (s.zlane a i) (s.zlaneH b i)
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .zbin op d a b, s =>
    let f (i : Nat) := op.sse.eval (s.zlane a i) (s.zlane b i)
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vpclmulqdq d a b n, s =>
    let f (i : Nat) := pclmul (s.zlane a i) (s.zlane b i) n
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vprold d r n, s =>
    let f (i : Nat) := rolDwords (s.zlane r i) n
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vpshufd d r o, s =>
    let f (i : Nat) := shufDwords (s.zlane r i) o
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vshufi32x4 d a b n, s =>
    let f := shuf4Lanes (s.zlane a) (s.zlane b) n
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vshift op d r n, s =>
    let f (i : Nat) := op.sse.eval (s.zlane r i) n
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vpslldq d r n, s =>
    let f (i : Nat) := XShiftOp.pslldq.eval (s.zlane r i) n
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vpsrldq d r n, s =>
    let f (i : Nat) := XShiftOp.psrldq.eval (s.zlane r i) n
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vpbroadcastq d r, s =>
    let x := qword (s.xmm r) 0 ++ qword (s.xmm r) 0
    s.setZ d x x x x
  | .vmovdqa64 d r, s => s.setZ d (s.zlane r 0) (s.zlane r 1) (s.zlane r 2) (s.zlane r 3)
  | .vpternlogd d a b n, s =>
    let f (i : Nat) := ternlog (s.zlane d i) (s.zlane a i) (s.zlane b i) n
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vprorq d r n, s =>
    let f (i : Nat) := rorQwords (s.zlane r i) n
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vpermq d r o, s =>
    let lo := permQwords (s.zlane r 1 ++ s.zlane r 0) o
    let hi := permQwords (s.zlane r 3 ++ s.zlane r 2) o
    s.setZ d (lo.extractLsb' 0 128) (lo.extractLsb' 128 128) (hi.extractLsb' 0 128)
      (hi.extractLsb' 128 128)
  | .vpmadd52 hi d a b, s =>
    let f (i : Nat) := madd52 hi (s.zlane d i) (s.zlane a i) (s.zlane b i)
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vpermw d a b, s =>
    let f (i : Nat) := ofWords fun k => s.permWord a b (8 * i + k)
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vpsrlvw d a b, s =>
    let f (i : Nat) := ofWords fun k => s.srlvWord a b (8 * i + k)
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vextracti32x4 d r n, s => s.setZ d (s.zlane r (n.toNat % 4)) 0 0 0

end VG.X86_64
