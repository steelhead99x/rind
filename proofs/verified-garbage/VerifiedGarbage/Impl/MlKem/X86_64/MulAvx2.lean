module

public import VerifiedGarbage.Impl.MlKem.X86_64.Mul

/-!
# ML-KEM on x86-64: products of NTTs with AVX2, the shared pieces

The AVX2 products (`KpkeAccY.lean`) run `vg_mlkem_multiply_ntts`
(`Mul.lean`) on sixteen pairs of coefficients at a time, eight in each
128-bit lane of AVX2 registers (`Avx.lean`): they load 128 bytes of each
factor into four registers (`yload4`; lane `l` of register `t` holding
coefficients `8t + 4l` to `8t + 4l + 3` of the 32), and run the SSE2
code's `deint` (`deintS`) and `vbase` on each lane, so that lane `l` holds
the pairs of coefficients `8t + 4l` to `8t + 4l + 3`, `t < 4`. The table
holds the `γ`s in that order (`gTabY`): word `e` of lane `l` of the sixteen
of iteration `i` is `γ` of pair `16i + 4⌊e/2⌋ + (e mod 2) + 2l`.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The `γ` of word `p` of the table (see above). -/
def gIdxY (p : Nat) : Nat := 16 * (p / 16) + 4 * (p % 8 / 2) + p % 2 + 2 * (p % 16 / 8)

/-- The table of the `γ`s in the order above. -/
def gTabY (p : Nat) : Nat := gTab (gIdxY p)

/-- `deint` (`Mul.lean`) on registers loaded already: the even doublewords
of `a, b, c, d` as the words of `a`, and the odd ones as those of `x`, with
the temporary `y`. -/
def deintS (a b c d x y : XReg) : List Instr :=
  [.xop (.pshufd a a 0xD8), .xop (.pshufd b b 0xD8), .xop (.pshufd c c 0xD8), .xop (.pshufd d d 0xD8),
    xmov x a, xb .punpckhqdq x b, xb .punpcklqdq a b, xmov y c, xb .punpckhqdq y d, xb .punpcklqdq c d,
    xb .packssdw a c, xb .packssdw x y]

/-- 128 bytes at `[p]` into `ymm a, b, c, d`. -/
def yload4 (p : Reg) (a b c d : XReg) : List Instr :=
  [.vmovdquLoad .l256 a (at_ p 0), .vmovdquLoad .l256 b (at_ p 32), .vmovdquLoad .l256 c (at_ p 64),
    .vmovdquLoad .l256 d (at_ p 96)]

end VG.Impl.MlKem.X86_64
