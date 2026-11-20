module
public import VerifiedGarbage.Impl.MlKem.X86_64.Cbd
import VerifiedGarbage.Impl.MlKem.X86_64.Cbd16


/-!
# ML-KEM on x86-64: `vg_mlkem16_cbd2_avx2`

`vg_mlkem16_cbd2` (`Cbd16.lean`) on 32 bytes at a time: each 128-bit lane of
the `ymm` registers does what that function does to an `xmm` register
(`toY`), on the sixteen bytes it loads (`cbd16Lane`), so that lane `l` of the
four registers it would store, `ymm7`, `ymm4`, `ymm5` and `ymm0` (from the
low doublewords of the first pair, the high, then the second pair's), holds
coefficients `32 l` to `32 l + 31`, eight in each. `vperm2i128` pairs the
first lanes of `ymm7` and `ymm4` (coefficients 0 to 15), of `ymm5` and `ymm0`
(16 to 31), then their second lanes, for four 32-byte stores. There are no
multiplications. Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The constants of `cbd16Consts` in both lanes. -/
def cbd16YConsts : List Instr :=
  yconst .xmm15 0x0D010D01 ++ yconst .xmm8 0x00FF00FF ++ yconst .xmm9 0x00550055 ++
    yconst .xmm10 0x00330033 ++ yconst .xmm11 0x00220022 ++ yconst .xmm12 0x000F000F ++
    yconst .xmm13 0x00020002

/-- `e - 2`, plus `q` if negative, in the words of `d` (`cbd16Out` without its store). -/
def cbd16Fix (d t : XReg) : List Instr :=
  [xb .psubw d .xmm13, xmov t d, .xop (.shift .psraw t 15), xb .pand t .xmm15, xb .paddw d t]

/-- Sixteen coefficients, from the even bytes' words in `a` and the odd
bytes' in `b`, to `d` and `a` (`cbd16Grp` without its stores). -/
def cbd16GrpN (d a b : XReg) : List Instr :=
  [xmov d a, xb .punpckldq d b, xb .punpckhdq a b] ++ cbd16Fix d .xmm6 ++ cbd16Fix a .xmm6

/-- What each lane does to the sixteen bytes in `xmm0`: the four registers
`vg_mlkem16_cbd2` stores, in `xmm7`, `xmm4`, `xmm5` and `xmm0`. -/
def cbd16Lane : List Instr :=
  cbdFront.tail ++ (cbd16GrpN .xmm7 .xmm4 .xmm2 ++ cbd16GrpN .xmm5 .xmm0 .xmm1)

/-- The coefficients in order: the first lanes of `ymm7` and `ymm4` (0 to 15)
to `ymm1`, of `ymm5` and `ymm0` (16 to 31) to `ymm2`, their second lanes (32
to 63) to `ymm3` and `ymm6`. -/
def cbd16Perms : List Instr :=
  [.vop (.vperm2i128 .xmm1 .xmm7 .xmm4 0x20), .vop (.vperm2i128 .xmm2 .xmm5 .xmm0 0x20),
    .vop (.vperm2i128 .xmm3 .xmm7 .xmm4 0x31), .vop (.vperm2i128 .xmm6 .xmm5 .xmm0 0x31)]

/-- The 64 coefficients to `rsi`. -/
def cbd16Stores : List Instr :=
  [.vmovdquStore .l256 (at_ .rsi 0) .xmm1, .vmovdquStore .l256 (at_ .rsi 32) .xmm2,
    .vmovdquStore .l256 (at_ .rsi 64) .xmm3, .vmovdquStore .l256 (at_ .rsi 96) .xmm6]

/-- Thirty-two bytes to 64 coefficients. -/
def cbd2_16YBody : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdi 0)] ++ toY cbd16Lane ++ cbd16Perms ++
    cbd16Stores ++ [.alu .add .rdi (.imm 32), .alu .add .rsi (.imm 128)]

def cbd2_16Avx2 : Prog isa :=
  .seq (.block cbd16YConsts) (.seq (rcxLoop 4 cbd2_16YBody) (.block [.vop .vzeroupper]))

end VG.Impl.MlKem.X86_64
