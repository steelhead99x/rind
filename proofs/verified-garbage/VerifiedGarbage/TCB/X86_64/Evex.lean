module

public import VerifiedGarbage.TCB.X86_64.Avx512

/-!
# x86-64 EVEX-encoded instructions on `ymm0`–`ymm31` and `zmm0`–`zmm31`

**Trusted.** The EVEX-encoded instructions of the x86-64 model in
`TCB/X86_64/Isa.lean` whose operands are 256-bit (`ymm`) vector registers,
of all thirty-two (`VReg`): the sixteen of the SSE and AVX instructions
(`XReg`), and `ymm16`–`ymm31` (`HReg`), which only EVEX-encoded instructions
can name (SDM Vol. 2 §2.7.1, "Instruction Format and EVEX": `EVEX.R'` and
`EVEX.V'` extend the register specifiers to five bits). Each is an
`EVEX.256` form (AVX512VL), unmasked (the opmask is `k0`, `EVEX.aaa = 000`)
and without embedded broadcast or rounding (`EVEX.b = 0`), and so writes all
256 bits of its destination and zeroes bits `MAXVL-1:256` (SDM Vol. 2
§2.7.1 and each instruction's pseudocode, `DEST[MAXVL-1:VL] := 0`); the
`EVEX.128` form of `VMOVQ xmm1, r64` zeroes bits `MAXVL-1:64` likewise.

Bits 511:256 of `zmm16`–`zmm31` are held in `zmmHiH`: these instructions zero
them. For `xmm0`–`xmm15` the state's
`xmm`, `ymmHi` and `zmmHi` hold the register, as for the VEX-encoded
instructions (`State.setV`), whose results these EVEX forms compute.

The last section has `EVEX.512` forms (`E5Op`), likewise unmasked, of all
thirty-two `zmm` registers: they write all 512 bits of their destination
(`State.setVz`).
-/

@[expose] public section

namespace VG.X86_64

/-- A vector register of an EVEX-encoded instruction: one of `xmm0`–`xmm15`
or one of `xmm16`–`xmm31` (or the `ymm` register that contains it). -/
inductive VReg
  | lo (r : XReg)
  | hi (r : HReg)
  deriving DecidableEq, Repr

namespace State

/-- The 256 bits of `ymm` register `r`. -/
def vy (s : State) : VReg → BitVec 256
  | .lo r => s.ymm r
  | .hi r => s.ymmH r

/-- Write an `EVEX.256` instruction's result to `r`, zeroing bits
`MAXVL-1:256` (Intel SDM Vol. 2, EVEX.256 instruction pseudocode). -/
def setVy (s : State) (r : VReg) (v : BitVec 256) : State :=
  match r with
  | .lo r => s.setV .l256 r (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  | .hi r => { s with
      ymmH := fun r' => if r' = r then v else s.ymmH r'
      zmmHiH := fun r' => if r' = r then 0 else s.zmmHiH r' }

end State

/-- `EVEX.256` instructions `vop ymm1, ymm2, ymm3` that act on each 128-bit
lane as the legacy SSE instruction does on its destination (`src1`) and
source (`src2`); see `EBinOp.sse`. -/
inductive EBinOp | vpaddq | vpsubq | vpxorq | vpandq | vporq
  deriving DecidableEq, Repr

/-- The legacy SSE instruction whose operation `op` applies to each lane:
SDM Vol. 2, each instruction's "EVEX encoded versions" pseudocode with
`(KL, VL) = (4, 256)`, no write mask and a register `SRC2`: VPADDQ
("PADDB/PADDW/PADDD/PADDQ", `EVEX.256.66.0F.W1 D4 /r`): `DEST[i+63:i] :=
SRC1[i+63:i] + SRC2[i+63:i]`; VPSUBQ ("PSUBB/PSUBW/PSUBD/PSUBQ",
`EVEX.256.66.0F.W1 FB /r`): `DEST[i+63:i] := SRC1[i+63:i] - SRC2[i+63:i]`;
VPXORQ ("PXOR", `EVEX.256.66.0F.W1 EF /r`):
`DEST[i+63:i] := SRC1[i+63:i] BITWISE XOR SRC2[i+63:i]`; VPANDQ ("PAND",
`EVEX.256.66.0F.W1 DB /r`): `... BITWISE AND ...`; VPORQ ("POR",
`EVEX.256.66.0F.W1 EB /r`): `... BITWISE OR ...`; for each quadword `j` from
0 to 3 (`i := j * 64`), which on each 128-bit lane is what PADDQ, PSUBQ,
PXOR, PAND and POR compute. -/
def EBinOp.sse : EBinOp → XBinOp
  | .vpaddq => .paddq | .vpsubq => .psubq | .vpxorq => .pxor | .vpandq => .pand | .vporq => .por

/-- Lane `i` (bits `128i+127:128i`, `i` 0 or 1) of a 256-bit value. -/
def lane256 (x : BitVec 256) (i : Nat) : BitVec 128 := x.extractLsb' (128 * i) 128

/-- `f` on each 128-bit lane of `a` and `b`. -/
def lanes256 (f : BitVec 128 → BitVec 128 → BitVec 128) (a b : BitVec 256) : BitVec 256 :=
  f (lane256 a 1) (lane256 b 1) ++ f (lane256 a 0) (lane256 b 0)

/-- SDM Vol. 2, "VALIGND/VALIGNQ—Align Doubleword/Quadword Vectors", VALIGNQ
with `(KL, VL) = (4, 256)` (`EVEX.256.66.0F3A.W1 03 /r ib`), no write mask
and a register `SRC2`: `TMP_DEST[511:0] := (SRC1[255:0] << 256) |
SRC2[255:0]; TMP_DEST[511:0] := TMP_DEST[511:0] >> (imm8[1:0] * 64)`, and
`DEST[i+63:i] := TMP_DEST[i+63:i]` for each quadword `j` from 0 to 3. -/
def alignQwords (a b : BitVec 256) (imm : BitVec 8) : BitVec 256 :=
  ((a ++ b) >>> (64 * (imm.toNat % 4))).extractLsb' 0 256

/-- EVEX-encoded instructions with 256-bit operands (or, for `vmovq`, a
128-bit destination) that write only a vector register. -/
inductive EOp
  /-- `vop ymm1, ymm2, ymm3` -/
  | bin (op : EBinOp) (dst src1 src2 : VReg)
  /-- `vpsllq ymm1, ymm2, imm8` (`EVEX.256.66.0F.W1 73 /6 ib`) or `vpsrlq
  ymm1, ymm2, imm8` (`EVEX.256.66.0F.W1 73 /2 ib`) -/
  | shift (op : ZShiftOp) (dst src : VReg) (count : BitVec 8)
  /-- `vpermq ymm1, ymm2, imm8` (`EVEX.256.66.0F3A.W1 00 /r ib`) -/
  | vpermq (dst src : VReg) (order : BitVec 8)
  /-- `valignq ymm1, ymm2, ymm3, imm8` (`EVEX.256.66.0F3A.W1 03 /r ib`) -/
  | valignq (dst src1 src2 : VReg) (count : BitVec 8)
  /-- `vpbroadcastq ymm1, xmm2` (`EVEX.256.66.0F38.W1 59 /r`) -/
  | vpbroadcastq (dst src : VReg)
  /-- `vmovq xmm1, r64` (`EVEX.128.66.0F.W1 6E /r`) -/
  | vmovq (dst : VReg) (src : Reg)
  /-- `vmovq xmm1, xmm2` (`EVEX.128.F3.0F.W1 7E /r`) -/
  | vmovqx (dst src : VReg)
  /-- `vpmadd52luq ymm1, ymm2, ymm3` (`EVEX.256.66.0F38.W1 B4 /r`), or with
  `hi` `vpmadd52huq ymm1, ymm2, ymm3` (`EVEX.256.66.0F38.W1 B5 /r`) -/
  | vpmadd52 (hi : Bool) (dst src1 src2 : VReg)
  /-- `vpternlogq ymm1, ymm2, ymm3, imm8` (`EVEX.256.66.0F3A.W1 25 /r ib`) -/
  | vpternlogq (dst src1 src2 : VReg) (imm : BitVec 8)
  /-- `vprorq ymm1, ymm2, imm8` (`EVEX.256.66.0F.W1 72 /0 ib`) -/
  | vprorq (dst src : VReg) (count : BitVec 8)
  /-- `vpsraq ymm1, ymm2, imm8` (`EVEX.256.66.0F.W1 72 /4 ib`) -/
  | vpsraq (dst src : VReg) (count : BitVec 8)
  /-- `vmovdqa64 ymm1, ymm2` (`EVEX.256.66.0F.W1 6F /r`) -/
  | vmovdqa64 (dst src : VReg)
  deriving DecidableEq, Repr

/-- Semantics of the `EVEX.256` instructions (see the module doc for the
zeroing of the bits above the vector length, `State.setVy`):

* `bin`: `EBinOp.sse` on each lane.
* `shift`: SDM Vol. 2, "PSLLW/PSLLD/PSLLQ" and "PSRLW/PSRLD/PSRLQ", "VPSLLQ
  (EVEX versions, imm8)": `DEST[i+63:i] := LOGICAL_LEFT_SHIFT_QWORDS(SRC1[i+63:i],
  imm8)` for each quadword (no write mask, a register source), and VPSRLQ
  likewise with `LOGICAL_RIGHT_SHIFT_QWORDS`: on each lane what PSLLQ and
  PSRLQ compute (a count above 63 gives zero).
* `vpermq`: SDM Vol. 2, "VPERMQ—Qwords Element Permutation", "VPERMQ (EVEX -
  imm8 control forms)" with `(KL, VL) = (4, 256)`: `TMP_DEST[63:0] :=
  (SRC[255:0] >> (IMM8[1:0] * 64))[63:0]`, …, `TMP_DEST[255:192] :=
  (SRC[255:0] >> (IMM8[7:6] * 64))[63:0]`, which is what the VEX.256 form
  computes (`permQwords`).
* `valignq`: `alignQwords`.
* `vpbroadcastq`: SDM Vol. 2, "VPBROADCAST", "VPBROADCASTQ (EVEX encoded
  versions)" with `(KL, VL) = (4, 256)`: `DEST[i+63:i] := SRC[63:0]` for each
  quadword.
* `vmovq`: SDM Vol. 2, "MOVD/MOVQ", "VMOVQ (EVEX encoded version, load)":
  `DEST[63:0] := SRC[63:0]; DEST[MAXVL-1:64] := 0`.
* `vmovqx`: SDM Vol. 2, "MOVQ—Move Quadword", "VMOVQ (EVEX.128.F3.0F.W1 7E)
  with XMM register source and destination": `DEST[63:0] := SRC[63:0];
  DEST[MAXVL-1:64] := 0`.
* `vpmadd52`: SDM Vol. 2, "VPMADD52LUQ" and "VPMADD52HUQ" with `(KL, VL) =
  (4, 256)`, no write mask and a register `SRC3`: `madd52` on each lane.
* `vpternlogq`: SDM Vol. 2, "VPTERNLOGD/VPTERNLOGQ—Bitwise Ternary Logic",
  "VPTERNLOGQ (EVEX encoded versions)" with `(KL, VL) = (4, 256)`, no write
  mask and a register `SRC2`: `FOR k := 0 TO 63 … DEST[j][k] :=
  imm[(DEST[i+k] << 2) + (SRC1[ i+k ] << 1) + SRC2[ i+k ]]` for each
  quadword `j` (`i := j * 64`): bit by bit, as VPTERNLOGD, so `ternlog` on
  each lane.
* `vprorq`: SDM Vol. 2, "VPRORD/VPRORVD/VPRORQ/VPRORVQ—Bit Rotate Right",
  "VPRORQ (EVEX encoded versions, imm8)" with `(KL, VL) = (4, 256)`, no write
  mask and a register source: `DEST[i+63:i] := RIGHT_ROTATE_QWORDS(SRC1[i+63:i],
  imm8)` for each quadword, so `rorQwords` on each lane.
* `vpsraq`: SDM Vol. 2, "PSRAW/PSRAD/PSRAQ—Shift Packed Data Right
  Arithmetic", "VPSRAQ (EVEX versions, imm8)" with `(KL, VL) = (4, 256)`, no
  write mask and a register source: `DEST[i+63:i] :=
  ARITHMETIC_RIGHT_SHIFT_QWORDS1(SRC1[i+63:i], imm8)` for each quadword, so
  `sraQwords` on each lane.
* `vmovdqa64`: SDM Vol. 2, "MOVDQA,VMOVDQA32/64—Move Aligned Packed Integer
  Values", "VMOVDQA64 (EVEX encoded versions, register-copy form)" with
  `(KL, VL) = (4, 256)` and no write mask: `DEST[i+63:i] := SRC[i+63:i]` for
  each quadword, and `DEST[MAXVL-1:VL] := 0`. -/
def EOp.exec : EOp → State → State
  | .bin op d a b, s => s.setVy d (lanes256 op.sse.eval (s.vy a) (s.vy b))
  | .shift op d a n, s =>
    s.setVy d (lanes256 (fun x _ => op.sse.eval x n) (s.vy a) (s.vy a))
  | .vpermq d a o, s => s.setVy d (permQwords (s.vy a) o)
  | .valignq d a b n, s => s.setVy d (alignQwords (s.vy a) (s.vy b) n)
  | .vpbroadcastq d a, s =>
    let q := qword256 (s.vy a) 0
    s.setVy d (q ++ q ++ q ++ q)
  | .vmovq d r, s => s.setVy d ((0 : BitVec 192) ++ s.gpr r)
  | .vmovqx d r, s => s.setVy d ((0 : BitVec 192) ++ qword256 (s.vy r) 0)
  | .vpmadd52 hi d a b, s =>
    let dv := s.vy d
    let av := s.vy a
    let bv := s.vy b
    s.setVy d (madd52 hi (lane256 dv 1) (lane256 av 1) (lane256 bv 1) ++
      madd52 hi (lane256 dv 0) (lane256 av 0) (lane256 bv 0))
  | .vpternlogq d a b n, s =>
    let dv := s.vy d
    let av := s.vy a
    let bv := s.vy b
    s.setVy d (ternlog (lane256 dv 1) (lane256 av 1) (lane256 bv 1) n ++
      ternlog (lane256 dv 0) (lane256 av 0) (lane256 bv 0) n)
  | .vprorq d a n, s => s.setVy d (lanes256 (fun x _ => rorQwords x n) (s.vy a) (s.vy a))
  | .vpsraq d a n, s => s.setVy d (lanes256 (fun x _ => sraQwords x n) (s.vy a) (s.vy a))
  | .vmovdqa64 d a, s => s.setVy d (s.vy a)

/-! ## `EVEX.512` forms, on `zmm0`–`zmm31`

The forms with 512-bit operands (`EVEX.L'L = 10`) of instructions above, and
`vinserti64x4`, of all thirty-two registers (`VReg`), unmasked and without
embedded broadcast: each writes all 512 bits of its destination. -/

namespace State

/-- Lane `i` (bits `128i+127:128i`, `i` from 0 to 3) of `zmm` register `r`,
of all thirty-two. -/
def vz (s : State) : VReg → Nat → BitVec 128
  | .lo r, i => s.zlane r i
  | .hi r, i => s.zlaneH r i

/-- Write the four lanes of the destination of an unmasked `EVEX.512`
instruction, of all thirty-two registers (`setZ`, `setZH`). -/
def setVz (s : State) (r : VReg) (l0 l1 l2 l3 : BitVec 128) : State :=
  match r with
  | .lo r => s.setZ r l0 l1 l2 l3
  | .hi r => s.setZH r l0 l1 l2 l3

end State

/-- SDM Vol. 2, "VINSERTI128/VINSERTI32x4/VINSERTI64x2/VINSERTI32x8/
VINSERTI64x4—Insert Packed Integer Values", "VINSERTI64x4 (EVEX.512 Encoded
Version)", no write mask: `TEMP_DEST[VL-1:0] := SRC1[VL-1:0]; CASE (imm8[0])
OF 0: TMP_DEST[255:0] := SRC2[255:0]; 1: TMP_DEST[511:256] := SRC2[255:0];
ESAC`, and `DEST` is `TMP_DEST`. Here `a i` is lane `i` of `SRC1`, `b` the
256 bits of `SRC2` (`ymm3/m256`), and the result is lane `j` of `DEST`. -/
def insert64x4 (a : Nat → BitVec 128) (b : BitVec 256) (imm : BitVec 8) (j : Nat) : BitVec 128 :=
  if imm.getLsbD 0 then (if j < 2 then a j else lane256 b (j - 2))
  else (if j < 2 then lane256 b j else a j)

/-- EVEX-encoded instructions with 512-bit operands (for `vinserti64x4`, a
256-bit second source) that write only a vector register. -/
inductive E5Op
  /-- `vop zmm1, zmm2, zmm3`: `vpaddq` (`EVEX.512.66.0F.W1 D4 /r`), `vpxorq`
  (`EF /r`), `vpandq` (`DB /r`) or `vporq` (`EB /r`) -/
  | bin (op : EBinOp) (dst src1 src2 : VReg)
  /-- `vpsllq zmm1, zmm2, imm8` (`EVEX.512.66.0F.W1 73 /6 ib`) or `vpsrlq
  zmm1, zmm2, imm8` (`EVEX.512.66.0F.W1 73 /2 ib`) -/
  | shift (op : ZShiftOp) (dst src : VReg) (count : BitVec 8)
  /-- `vpermq zmm1, zmm2, imm8` (`EVEX.512.66.0F3A.W1 00 /r ib`) -/
  | vpermq (dst src : VReg) (order : BitVec 8)
  /-- `vpmadd52luq zmm1, zmm2, zmm3` (`EVEX.512.66.0F38.W1 B4 /r`), or with
  `hi` `vpmadd52huq zmm1, zmm2, zmm3` (`EVEX.512.66.0F38.W1 B5 /r`) -/
  | vpmadd52 (hi : Bool) (dst src1 src2 : VReg)
  /-- `vinserti64x4 zmm1, zmm2, ymm3, imm8` (`EVEX.512.66.0F3A.W1 3A /r ib`) -/
  | vinserti64x4 (dst src1 src2 : VReg) (imm : BitVec 8)
  deriving DecidableEq, Repr

/-- Semantics of the `EVEX.512` instructions on registers: what `ZOp.exec`
gives the forms it has for `zmm0`–`zmm15`, of all thirty-two registers. SDM
Vol. 2 (no flags are affected, there is no write mask, and all of
`DEST[511:0]` is written):

* `bin`: `EBinOp.sse` on each lane: the "EVEX encoded versions" pseudocode
  of "PADDB/PADDW/PADDD/PADDQ", "PXOR", "PAND" and "POR" with `(KL, VL) =
  (8, 512)` and a register `SRC2`, `DEST[i+63:i] := SRC1[i+63:i] op
  SRC2[i+63:i]` for each of the eight quadwords.
* `shift`: "PSLLW/PSLLD/PSLLQ" and "PSRLW/PSRLD/PSRLQ", "VPSLLQ (EVEX
  versions, imm8)" and "VPSRLQ (EVEX versions, imm8)" with `(KL, VL) = (8,
  512)` and a register source: each quadword shifted by `imm8` (a count above
  63 gives zero), which on each lane is what PSLLQ and PSRLQ compute
  (`ZShiftOp.sse`).
* `vpermq`: "VPERMQ—Qwords Element Permutation", "VPERMQ (EVEX - imm8 control
  forms)" with `VL = 512` (quoted at `ZOp.exec`): each 256-bit half of `DEST`
  is the same half of `SRC` permuted as the VEX.256 form permutes a register
  (`permQwords`).
* `vpmadd52`: "VPMADD52LUQ" and "VPMADD52HUQ" with `(KL, VL) = (8, 512)` and a
  register `SRC3` (quoted at `ZOp.exec`): `madd52` on each lane.
* `vinserti64x4`: `insert64x4`, with `SRC2` the 256 bits of `ymm3`. -/
def E5Op.exec : E5Op → State → State
  | .bin op d a b, s =>
    let f (i : Nat) := op.sse.eval (s.vz a i) (s.vz b i)
    s.setVz d (f 0) (f 1) (f 2) (f 3)
  | .shift op d r n, s =>
    let f (i : Nat) := op.sse.eval (s.vz r i) n
    s.setVz d (f 0) (f 1) (f 2) (f 3)
  | .vpermq d r o, s =>
    let lo := permQwords (s.vz r 1 ++ s.vz r 0) o
    let hi := permQwords (s.vz r 3 ++ s.vz r 2) o
    s.setVz d (lo.extractLsb' 0 128) (lo.extractLsb' 128 128) (hi.extractLsb' 0 128)
      (hi.extractLsb' 128 128)
  | .vpmadd52 hi d a b, s =>
    let f (i : Nat) := madd52 hi (s.vz d i) (s.vz a i) (s.vz b i)
    s.setVz d (f 0) (f 1) (f 2) (f 3)
  | .vinserti64x4 d a b n, s =>
    let f := insert64x4 (s.vz a) (s.vy b) n
    s.setVz d (f 0) (f 1) (f 2) (f 3)

end VG.X86_64
