module

public import VerifiedGarbage.Impl.MlKem.X86_64.Arith

/-!
# ML-KEM on x86-64: `vg_mlkem_cbd2`

`cbd2(b = rdi, f = rsi)` runs over the 128 bytes of `b` sixteen at a time,
with `rcx` counting down; each byte `c` gives two coefficients, from its
nibbles. The bytes are split into the words of two SSE2 registers, the even
bytes and the odd ones, so that each word holds one byte. In each word,
`t = (c ∧ 0x55) + ((c >> 1) ∧ 0x55)` holds `x₀`, `y₀`, `x₁` and `y₁` of
`SamplePolyCBD₂` in its 2-bit fields (each at most 2), and
`e = (t ∧ 0x33) + 0x22 - ((t >> 2) ∧ 0x33)` holds `x₀ - y₀ + 2` and
`x₁ - y₁ + 2` in its two nibbles (each in `[0, 4]`, so no field borrows from
the next). The nibbles are split into words, interleaved into the order of
the coefficients (`punpcklwd`, `punpckhwd`, `punpcklqdq`, `punpckhqdq`),
zero-extended to doublewords, and each coefficient is `e - 2`, plus `q` if
negative (`dcadd`). There are no multiplications. Every address and branch
depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `v` in each doubleword of `x`, through `rax`. -/
def bcast (x : XReg) (v : BitVec 32) : List Instr :=
  [.mov32 .rax (.imm v), .xop (.movq x .rax), .xop (.pshufd x x 0)]

/-- `q` and `2` in the doublewords of `xmm15` and `xmm13`, the masks `0xFF`,
`0x55`, `0x33`, `0x0F` and the constant `0x22` in the words of `xmm8`–`xmm12`,
and zero in `xmm14`. -/
def cbdConsts : List Instr :=
  dconsts ++ bcast .xmm8 0x00FF00FF ++ bcast .xmm9 0x00550055 ++ bcast .xmm10 0x00330033 ++
    bcast .xmm11 0x00220022 ++ bcast .xmm12 0x000F000F ++ bcast .xmm13 2 ++ [xb .pxor .xmm14 .xmm14]

/-- For a byte in each word of `r`: `e`, its low nibble to `r` and its high
nibble to `t`. -/
def cbdNib (r t : XReg) : List Instr :=
  [xmov t r, .xop (.shift .psrlw t 1), xb .pand t .xmm9, xb .pand r .xmm9, xb .paddw r t,
    xmov t r, .xop (.shift .psrlw t 2), xb .pand t .xmm10, xb .pand r .xmm10, xb .paddw r .xmm11,
    xb .psubw r t, xmov t r, .xop (.shift .psrlw t 4), xb .pand r .xmm12]

/-- The doublewords of `d`, less 2, mod `q`, to `[rsi + off]`, with a temporary `t`. -/
def cbdOut (d t : XReg) (off : Nat) : List Instr :=
  xb .psubd d .xmm13 :: dcadd d t ++ [.movdquStore (at_ .rsi off) d]

/-- Sixteen coefficients to `[rsi + off]`: the words of `a` are those of the
even bytes (low and high nibble in turn), those of `b` of the odd bytes. -/
def cbdGrp (a b : XReg) (off : Nat) : List Instr :=
  [xmov .xmm5 a, xb .punpcklwd .xmm5 .xmm14, xmov .xmm6 b, xb .punpcklwd .xmm6 .xmm14, xmov .xmm7 .xmm5,
    xb .punpcklqdq .xmm7 .xmm6, xb .punpckhqdq .xmm5 .xmm6] ++
  cbdOut .xmm7 .xmm6 off ++ cbdOut .xmm5 .xmm6 (off + 16) ++
  [xb .punpckhwd a .xmm14, xb .punpckhwd b .xmm14, xmov .xmm7 a, xb .punpcklqdq .xmm7 b,
    xb .punpckhqdq a b] ++
  cbdOut .xmm7 .xmm6 (off + 32) ++ cbdOut a .xmm6 (off + 48)

/-- Sixteen bytes to the words of `xmm4`, `xmm0` (the nibbles of the even
bytes, low and high in turn: those of bytes 0, 2, 4, 6, then 8, …, 14) and
`xmm2`, `xmm1` (of the odd bytes). -/
def cbdFront : List Instr :=
  [.movdquLoad .xmm0 (at_ .rdi 0), xmov .xmm1 .xmm0, .xop (.shift .psrlw .xmm1 8), xb .pand .xmm0 .xmm8] ++
    cbdNib .xmm0 .xmm2 ++ cbdNib .xmm1 .xmm3 ++
    [xmov .xmm4 .xmm0, xb .punpcklwd .xmm4 .xmm2, xb .punpckhwd .xmm0 .xmm2, xmov .xmm2 .xmm1,
      xb .punpcklwd .xmm2 .xmm3, xb .punpckhwd .xmm1 .xmm3]

/-- Sixteen bytes to 32 coefficients. -/
def cbd2Body : List Instr :=
  cbdFront ++ cbdGrp .xmm4 .xmm2 0 ++ cbdGrp .xmm0 .xmm1 64 ++
    [.alu .add .rdi (.imm 16), .alu .add .rsi (.imm 128), .alu .sub .rcx (.imm 1)]

def cbd2 : Prog isa := .seq (.block (cbdConsts ++ [.mov32 .rcx (.imm 8)])) (.loop (.block cbd2Body) .ne)

end VG.Impl.MlKem.X86_64
