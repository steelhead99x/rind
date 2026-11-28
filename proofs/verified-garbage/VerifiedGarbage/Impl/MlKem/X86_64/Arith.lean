module

public import VerifiedGarbage.Impl.MlKem.X86_64.Vec
public import VerifiedGarbage.Impl.MlKem.X86_64.Avx

/-!
# ML-KEM on x86-64: `vg_mlkem_add` and `vg_mlkem_sub`

`add(f = rdi, g = rsi)` and `sub(f = rdi, g = rsi)` compute on four
coefficients at a time, as the doublewords of SSE2 registers, with `q` in
each doubleword of `xmm15` (`dconsts`). They run over the 64 groups of four
with `rdi` and `rsi` pointing at the group of `f` and of `g`, and `rcx`
counting down. `add` computes `f[i] + g[i] - q`, in `[-q, q)`, and `sub`
`f[i] - g[i]`, in `(-q, q)`, and adds `q` to the negative ones (`dcadd`)
before storing them to `f`. There are no multiplications. Every address and
branch depends only on the pointers.

`addAvx2` and `subAvx2` do the same on eight coefficients at a time, in the
two 128-bit lanes of AVX2 registers (`toY` of the same arithmetic,
`addArith` and `subArith`), with `q` in each doubleword of `ymm15`, over the
32 groups of eight.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `q` in each doubleword of `xmm15`. -/
def dconsts : List Instr :=
  [.mov32 .rax (.imm 3329), .xop (.movq .xmm15 .rax), .xop (.pshufd .xmm15 .xmm15 0)]

/-- `d + q` in the doublewords of `d` that are negative, and `d` in the
others, with a temporary `t`: `d >>ₐ 31` is all ones exactly when `d` is
negative. -/
def dcadd (d t : XReg) : List Instr :=
  [xmov t d, .xop (.shift .psrad t 31), xb .pand t .xmm15, xb .paddd d t]

/-- Advance the two pointers and count down. -/
def dstep : List Instr :=
  [.alu .add .rdi (.imm 16), .alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 1)]

def addBody : List Instr :=
  [.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0), xb .paddd .xmm0 .xmm1,
    xb .psubd .xmm0 .xmm15] ++ dcadd .xmm0 .xmm1 ++ [.movdquStore (at_ .rdi 0) .xmm0] ++ dstep

def subBody : List Instr :=
  [.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0), xb .psubd .xmm0 .xmm1] ++
    dcadd .xmm0 .xmm1 ++ [.movdquStore (at_ .rdi 0) .xmm0] ++ dstep

def add : Prog isa := .seq (.block (dconsts ++ [.mov32 .rcx (.imm 64)])) (.loop (.block addBody) .ne)

def sub : Prog isa := .seq (.block (dconsts ++ [.mov32 .rcx (.imm 64)])) (.loop (.block subBody) .ne)

/-- The arithmetic of `add` on `xmm0` and `xmm1`, to `xmm0`. -/
def addArith : List Instr := [xb .paddd .xmm0 .xmm1, xb .psubd .xmm0 .xmm15] ++ dcadd .xmm0 .xmm1

/-- The arithmetic of `sub` on `xmm0` and `xmm1`, to `xmm0`. -/
def subArith : List Instr := xb .psubd .xmm0 .xmm1 :: dcadd .xmm0 .xmm1

/-- Eight coefficients of `f` and `g`, `ar` on each lane, to `f`. -/
def yaccBody (ar : List Instr) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdi 0), .vmovdquLoad .l256 .xmm1 (at_ .rsi 0)] ++ toY ar ++
    [.vmovdquStore .l256 (at_ .rdi 0) .xmm0, .alu .add .rdi (.imm 32), .alu .add .rsi (.imm 32)]

/-- `add` or `sub` (`ar`) with AVX2. -/
def accAvx2 (ar : List Instr) : Prog isa :=
  .seq (.block (yconst .xmm15 3329)) (.seq (rcxLoop 32 (yaccBody ar)) (.block [.vop .vzeroupper]))

def addAvx2 : Prog isa := accAvx2 addArith

def subAvx2 : Prog isa := accAvx2 subArith

end VG.Impl.MlKem.X86_64
