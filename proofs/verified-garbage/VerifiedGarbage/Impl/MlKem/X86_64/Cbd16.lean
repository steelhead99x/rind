module

public import VerifiedGarbage.Impl.MlKem.X86_64.Cbd

/-!
# ML-KEM on x86-64: `vg_mlkem16_cbd2`

`cbd2_16(b = rdi, f = rsi)` is `vg_mlkem_cbd2` (`Cbd.lean`) storing 16-bit
coefficients: the nibbles of sixteen bytes are split into the words of four
registers as there (`cbdFront`), and each pair of registers, the even bytes'
words and the odd bytes', is interleaved by doublewords (`punpckldq`,
`punpckhdq`), which puts the coefficients in order. Each coefficient is
`e - 2`, plus `q` if negative, in its word (`psubw`, then `psraw` by 15,
`pand` with `q`, `paddw`), and eight are stored at a time. There are no
multiplications. Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `q` and `2` in the words of `xmm15` and `xmm13`, and the masks `0xFF`,
`0x55`, `0x33`, `0x0F` and the constant `0x22` in the words of `xmm8`–`xmm12`. -/
def cbd16Consts : List Instr :=
  bcast .xmm15 0x0D010D01 ++ bcast .xmm8 0x00FF00FF ++ bcast .xmm9 0x00550055 ++
    bcast .xmm10 0x00330033 ++ bcast .xmm11 0x00220022 ++ bcast .xmm12 0x000F000F ++
    bcast .xmm13 0x00020002

/-- The words of `d`, less 2, mod `q`, to `[rsi + off]`, with a temporary `t`. -/
def cbd16Out (d t : XReg) (off : Nat) : List Instr :=
  [xb .psubw d .xmm13, xmov t d, .xop (.shift .psraw t 15), xb .pand t .xmm15, xb .paddw d t,
    .movdquStore (at_ .rsi off) d]

/-- Sixteen coefficients to `[rsi + off]`: the words of `a` are those of the
even bytes (low and high nibble in turn), those of `b` of the odd bytes. -/
def cbd16Grp (a b : XReg) (off : Nat) : List Instr :=
  [xmov .xmm7 a, xb .punpckldq .xmm7 b, xb .punpckhdq a b] ++
    cbd16Out .xmm7 .xmm6 off ++ cbd16Out a .xmm6 (off + 16)

/-- Sixteen bytes to 32 coefficients. -/
def cbd2_16Body : List Instr :=
  cbdFront ++ cbd16Grp .xmm4 .xmm2 0 ++ cbd16Grp .xmm0 .xmm1 32 ++
    [.alu .add .rdi (.imm 16), .alu .add .rsi (.imm 64), .alu .sub .rcx (.imm 1)]

def cbd2_16 : Prog isa :=
  .seq (.block (cbd16Consts ++ [.mov32 .rcx (.imm 8)])) (.loop (.block cbd2_16Body) .ne)

end VG.Impl.MlKem.X86_64
