module

public import VerifiedGarbage.Impl.MlKem.X86_64.Vec
public import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM on x86-64: `vg_mlkem_multiply_ntts`

`multiplyNTTs(h = rdi, f = rsi, g = rdx, scratch = rcx)` computes on the
pairs of eight pairs of coefficients at a time, as the words of SSE2
registers (see `Vec.lean`), with `scratch` in `r10`. It stores the 128 words
`γᵢ · 2¹⁶ mod q`, `γᵢ = ζ^(2 BitRev7(i) + 1)`, to `scratch` (`gTab`, with
immediates: the code has no other memory), and `R² mod q = 1353` in each
word of `xmm12`. Then, 16 times, with `rsi`, `rdx` and `rdi` at 16
coefficients of `f`, `g` and `h`, `r8` at their eight `γ`s and `rcx`
counting down:

* `deint` loads the 16 coefficients of `f` and puts the words of the even
  ones (`a₀` of each pair) in `xmm0` and of the odd ones (`a₁`) in `xmm4`,
  and those of `g` (`b₀`, `b₁`) in `xmm6` and `xmm10`;
* with `mont(x, y) = x · y · 2⁻¹⁶ mod q` (`vmont`), `h₀ = mont(mont(a₀, b₀) +
  mont(mont(a₁, b₁), γ · 2¹⁶), R²)` and `h₁ = mont(mont(a₀, b₁) + mont(a₁,
  b₀), R²)`, each brought into `[0, q)` (`vcadd`);
* `h₀` and `h₁` are interleaved and stored as `u32`s.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `γᵢ = ζ^(2 BitRev7(i) + 1) mod q`. -/
def gammaTab (i : Nat) : Nat := 17 ^ (2 * Spec.MlKem.bitRev7 i + 1) % 3329

/-- `γᵢ · 2¹⁶ mod q`. -/
def gTab (i : Nat) : Nat := gammaTab i * 65536 % 3329

/-- The 16 `u32`s at `[p]`: the even ones as the words of `a`, and the odd
ones as the words of `x`, with temporaries `b`, `c`, `d` and `y`. -/
def deint (p : Reg) (a b c d x y : XReg) : List Instr :=
  [.movdquLoad a (at_ p 0), .movdquLoad b (at_ p 16), .movdquLoad c (at_ p 32), .movdquLoad d (at_ p 48),
    .xop (.pshufd a a 0xD8), .xop (.pshufd b b 0xD8), .xop (.pshufd c c 0xD8), .xop (.pshufd d d 0xD8),
    xmov x a, xb .punpcklqdq a b, xb .punpckhqdq x b, xmov y c, xb .punpcklqdq c d, xb .punpckhqdq y d,
    xb .packssdw a c, xb .packssdw x y]

/-- `h₀` in `xmm1` and `h₁` in `xmm2`, from `a₀, a₁, b₀, b₁` in `xmm0,
xmm4, xmm6, xmm10` and the `γ · 2¹⁶` in `xmm13`. -/
def vbase : List Instr :=
  (xmov .xmm1 .xmm4 :: vmont .xmm1 .xmm10 .xmm2) ++ vmont .xmm1 .xmm13 .xmm2 ++
    (xmov .xmm2 .xmm0 :: vmont .xmm2 .xmm6 .xmm3) ++ (xb .paddw .xmm1 .xmm2 :: xmov .xmm2 .xmm0 ::
      vmont .xmm2 .xmm10 .xmm3) ++ vmont .xmm4 .xmm6 .xmm3 ++ (xb .paddw .xmm2 .xmm4 ::
      vmont .xmm1 .xmm12 .xmm3) ++ vcadd .xmm1 .xmm3 ++ vmont .xmm2 .xmm12 .xmm3 ++ vcadd .xmm2 .xmm3

/-- `h₀` and `h₁` interleaved and stored to `[rdi]` as 16 `u32`s. -/
def vinter : List Instr :=
  [xmov .xmm3 .xmm1, xb .punpcklwd .xmm1 .xmm2, xb .punpckhwd .xmm3 .xmm2, xb .pxor .xmm4 .xmm4,
    xmov .xmm5 .xmm1, xb .punpcklwd .xmm1 .xmm4, xb .punpckhwd .xmm5 .xmm4, xmov .xmm6 .xmm3,
    xb .punpcklwd .xmm3 .xmm4, xb .punpckhwd .xmm6 .xmm4, .movdquStore (at_ .rdi 0) .xmm1,
    .movdquStore (at_ .rdi 16) .xmm5, .movdquStore (at_ .rdi 32) .xmm3, .movdquStore (at_ .rdi 48) .xmm6]

def mulBody : List Instr :=
  deint .rsi .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5 ++ deint .rdx .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11 ++
    [.movdquLoad .xmm13 (at_ .r8 0)] ++ vbase ++ vinter ++
    [.alu .add .rsi (.imm 64), .alu .add .rdx (.imm 64), .alu .add .rdi (.imm 64), .alu .add .r8 (.imm 16)]

/-- The table, the constants, and `r8` at the table. -/
def mulPro : List Instr :=
  wordTab gTab 128 .r10 0 ++ vconsts ++
    [.mov32 .rax (.imm 0x05490549), .xop (.movq .xmm12 .rax), .xop (.pshufd .xmm12 .xmm12 0), .mov .r8 (.reg .r10)]

def multiplyNTTs : Prog isa :=
  .seq (.block [.mov .r10 (.reg .rcx)]) (.seq (.block mulPro) (rcxLoop 16 mulBody))

end VG.Impl.MlKem.X86_64
