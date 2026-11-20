module

public import VerifiedGarbage.Impl.MlKem.X86_64.NttAvx2
public import VerifiedGarbage.Impl.MlKem.X86_64.MulAvx2
public import VerifiedGarbage.Impl.MlKem.X86_64.Arith
public import VerifiedGarbage.Impl.MlKem.X86_64.NttRegs

/-!
# ML-KEM on x86-64: sums of products in words, with AVX2

The pieces of `Bodies.avx2` (`KpkeMul.lean`) that keep a sum of products
`ŝ[j] ×_T ŷ[j]` as 256 words (an *accumulator*) rather than as 256 `u32`s:
the products of `MulAvx2.lean`'s loads and `vbase` are added to
it where `vbase` leaves them, and `NTT⁻¹` starts from it rather than from
the `u32`s it would pack.

`vbase` leaves the products of the 32 coefficients of an iteration `i` in
two registers, in an order of their own: word `e` of lane `l` of `ymm1`
holds coefficient `2 p` and that of `ymm2` coefficient `2 p + 1`, for the
pair `p = 16i + 4⌊e/2⌋ + (e mod 2) + 2l`. The accumulator keeps them in
that order: `ymm1` at byte `64 i` and `ymm2` at `64 i + 32`
(`accIdx`).

* `zeroAccY(acc = rdi)`: the accumulator of the zero polynomial.
* `tabAccY(scratch = rcx)`: the `γ`s in `vbase`'s order
  (`gTabY`) at `scratch + 3328`, once for all the products.
* `mulAccY(acc = rdi, f = rsi, g = rdx, scratch = rcx)`: `acc += f ×_T g`,
  8 times on 32 coefficients: the loads of `MulAvx2.lean` and
  `vbase`, with the table at `scratch + 3328`, then each of `ymm1` and
  `ymm2` added to its 32 bytes of the accumulator, reduced (`vcsub`).
* `mulSetY(acc = rdi, f = rsi, g = rdx, scratch = rcx)`: `acc = f ×_T g`:
  `mulAccY`, but storing `ymm1` and `ymm2` as they are.
* `finAccY(f = rdi, acc = rsi)`: `f += acc`, to the `u32`s at `f`, 32
  coefficients at a time: `vpunpcklwd` and `vpunpckhwd` of the
  accumulator's two registers put coefficients `4l + {0, …, 3}` and
  `8 + 4l + {0, …, 3}` (and those sixteen higher) in lane `l` (as in
  `nttInvAccY`), and `vpunpcklwd` and `vpunpckhwd` of each with zero extend
  them to eight `u32`s in order, which `vg_mlkem_add_avx2`'s arithmetic adds
  to those of `f`.
* `nttInvAccY(acc = rdi, scratch = rsi)`: `NTT⁻¹` on registers
  (`NttRegs.lean`) reading the accumulator, to the `u32`s at `rdi`: pass B
  loads each iteration's two registers and interleaves their words
  (`vpunpck{l,h}wd`), which puts coefficients `4l + {0, …, 3}` and
  `8 + 4l + {0, …, 3}` (and those sixteen higher) in lane `l`, the order
  `vpackssdw` leaves `u32`s in.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The offset of the table of `mulAccY` in `scratch`. -/
def oTabY : Nat := 3328

/-- The coefficient at word `w` of the accumulator. -/
def accIdx (w : Nat) : Nat :=
  2 * (16 * (w / 32) + 4 * (w % 8 / 2) + w % 2 + 2 * (w % 16 / 8)) + w % 32 / 16

def zeroAccY : Prog isa :=
  .block (yb .vpxor .xmm0 .xmm0 .xmm0 ::
    (List.range 16).map fun i => .vmovdquStore .l256 (at_ .rdi (32 * i)) .xmm0)

def tabAccY : List Instr := leaR .r10 .rcx oTabY ++ wordTab gTabY 128 .r10 0

/-- The 32 bytes at `[rdi + off]` plus the words of `h`, reduced, and stored back. -/
def accStore (h : XReg) (off : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm5 (at_ .rdi off)] ++ toY (xb .paddw h .xmm5 :: vcsub h .xmm3) ++
    [.vmovdquStore .l256 (at_ .rdi off) h]

/-- The products of 32 coefficients of `rsi` and `rdx`, to `ymm1` and `ymm2`
(`vbase`'s order). -/
def mulProdY : List Instr :=
  yload4 .rsi .xmm0 .xmm1 .xmm2 .xmm3 ++ toY (deintS .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5) ++
    yload4 .rdx .xmm6 .xmm7 .xmm8 .xmm9 ++ toY (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11) ++
    [.vmovdquLoad .l256 .xmm13 (at_ .r8 0)] ++ toY vbase

/-- The pointers to the next 32 coefficients. -/
def mulNextY : List Instr :=
  [.alu .add .rsi (.imm 128), .alu .add .rdx (.imm 128), .alu .add .rdi (.imm 64), .alu .add .r8 (.imm 32)]

def mulAccBodyY : List Instr := mulProdY ++ accStore .xmm1 0 ++ accStore .xmm2 32 ++ mulNextY

def mulSetBodyY : List Instr :=
  mulProdY ++ [.vmovdquStore .l256 (at_ .rdi 0) .xmm1, .vmovdquStore .l256 (at_ .rdi 32) .xmm2] ++ mulNextY

/-- The constants, and `r8` at the table. -/
def mulAccProY : List Instr := yconsts ++ yconst .xmm12 0x05490549 ++ leaR .r8 .rcx oTabY

def mulAccY : Prog isa := .seq (.block mulAccProY) (rcxLoop 8 mulAccBodyY)

def mulSetY : Prog isa := .seq (.block mulAccProY) (rcxLoop 8 mulSetBodyY)

def nttInvAccY : Prog isa := nttIR NttR.passIBsAcc

/-- Eight coefficients of the sum, from the words of `w` (`op` with `ymm14`,
zero) and the `u32`s at `[rdi + off]`, to `[rdi + off]`: the arithmetic of
`vg_mlkem_add_avx2` (`addArith`). -/
def finQ (w : XReg) (op : VBinOp) (off : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdi off), yb op .xmm1 w .xmm14] ++ toY addArith ++
    [.vmovdquStore .l256 (at_ .rdi off) .xmm0]

def finAccBodyY : List Instr :=
  [.vmovdquLoad .l256 .xmm8 (at_ .rsi 0), .vmovdquLoad .l256 .xmm9 (at_ .rsi 32),
    yb .vpunpcklwd .xmm10 .xmm8 .xmm9, yb .vpunpckhwd .xmm11 .xmm8 .xmm9] ++
    finQ .xmm10 .vpunpcklwd 0 ++ finQ .xmm10 .vpunpckhwd 32 ++ finQ .xmm11 .vpunpcklwd 64 ++
    finQ .xmm11 .vpunpckhwd 96 ++ [.alu .add .rsi (.imm 64), .alu .add .rdi (.imm 128)]

def finAccY : Prog isa :=
  .seq (.block (yconst .xmm15 3329 ++ [yb .vpxor .xmm14 .xmm14 .xmm14]))
    (.seq (rcxLoop 8 finAccBodyY) (.block [.vop .vzeroupper]))


/-! ### A row of products, in registers

A row sums its `k` products before it reduces them. Doubleword `d` of a
register of `f` holds a pair of coefficients, `f₀` in its low word and `f₁`
in its high one, so `vpmaddwd` with the pairs `(g₀, g₁γ)` gives
`f₀g₀ + f₁g₁γ`, the first coefficient of `BaseCaseMultiply`, as a doubleword,
and with the pairs `(g₁, g₀)` the second, `f₀g₁ + f₁g₀`. The `k ≤ 4` products
of a coefficient add up as doublewords, less than `8q²` in magnitude, and one
Montgomery reduction of the sum (`predD`) leaves a word. -/

/-- The four doublewords of products of a lane to `d₀, …, d₃`: with the
pairs of coefficients `0, …, 3` of `f` in `xmm0` and `4, …, 7` in `xmm1`,
the coefficients `g₀` of `g` in the words of `xmm6` and `g₁` in those of
`xmm10`, and the `γ`s in `xmm13`: `g₁γ` to `xmm4` (`vmont`, with `xmm5`),
then `f₀g₀ + f₁g₁γ` of pairs `0, …, 3` to `d₀` and of `4, …, 7` to `d₁`, and
`f₀g₁ + f₁g₀` to `d₂` and `d₃`. -/
def pterm (d₀ d₁ d₂ d₃ : XReg) : List Instr :=
  (xmov .xmm4 .xmm10 :: vmont .xmm4 .xmm13 .xmm5) ++
    [xmov d₀ .xmm6, xb .punpcklwd d₀ .xmm4, xb .pmaddwd d₀ .xmm0,
      xmov d₁ .xmm6, xb .punpckhwd d₁ .xmm4, xb .pmaddwd d₁ .xmm1,
      xmov d₂ .xmm10, xb .punpcklwd d₂ .xmm6, xb .pmaddwd d₂ .xmm0,
      xmov d₃ .xmm10, xb .punpckhwd d₃ .xmm6, xb .pmaddwd d₃ .xmm1]

/-- The first product of a row, to the sums: `xmm11` and `xmm2` (the first
coefficients), `xmm12` and `xmm3` (the second). -/
def ptermSet : List Instr := pterm .xmm11 .xmm2 .xmm12 .xmm3

/-- Another product of a row, added to the sums. -/
def ptermAdd : List Instr :=
  pterm .xmm5 .xmm7 .xmm8 .xmm9 ++
    [xb .paddd .xmm11 .xmm5, xb .paddd .xmm2 .xmm7, xb .paddd .xmm12 .xmm8, xb .paddd .xmm3 .xmm9]

/-- The doublewords `x` of `x`, each less than `8q²` in magnitude, to
`(x - (x q⁻¹ mod± 2¹⁶) q) / 2¹⁶`: with `q⁻¹` in the words of `xmm14` and `q`
in the low word of each doubleword of `xmm7`, whose high word is zero, so
that `pmaddwd` multiplies the low word of each doubleword of `xmm5` by `q`. -/
def predD (x : XReg) : List Instr :=
  [xmov .xmm5 x, xb .pmullw .xmm5 .xmm14, xb .pmaddwd .xmm5 .xmm7, xb .psubd x .xmm5, .xop (.shift .psrad x 16)]

/-- The sums reduced, each to a word in `(-q, q)`: the first coefficients to
the words of `xmm11` and the second to those of `xmm12`, in `vbase`'s
order. -/
def pred : List Instr :=
  [xmov .xmm7 .xmm15, .xop (.shift .psrld .xmm7 16)] ++ predD .xmm11 ++ predD .xmm2 ++ predD .xmm12 ++
    predD .xmm3 ++ [xb .packssdw .xmm11 .xmm2, xb .packssdw .xmm12 .xmm3]

/-- `yload4` from `p + o`. -/
def yload4o (p : Reg) (o : Nat) (a b c d : XReg) : List Instr :=
  [.vmovdquLoad .l256 a (at_ p o), .vmovdquLoad .l256 b (at_ p (o + 32)), .vmovdquLoad .l256 c (at_ p (o + 64)),
    .vmovdquLoad .l256 d (at_ p (o + 96))]

/-- The 32 coefficients of block `b` of the `u32`s at `rsi + o j`, as pairs:
doubleword `d` of lane `l` of `ymm0` holds the pair `4⌊d/2⌋ + (d mod 2) + 2l`
of the sixteen (`vbase`'s order) and that of `ymm1` the pair eight higher,
which is how `vpackssdw` packs the `u32`s of each lane. -/
def rowLdY (o j : Nat) : List Instr :=
  yload4o .rsi (o * j) .xmm0 .xmm1 .xmm8 .xmm9 ++
    [yb .vpackssdw .xmm0 .xmm0 .xmm1, yb .vpackssdw .xmm1 .xmm8 .xmm9]

/-- `rowLdY` of `u16`s: the 64 bytes at `rsi + o j`, each 128-bit lane
holding the quadwords `vpermq` with `0xD8` brings it. -/
def rowLdY16 (o j : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rsi (o * j)), .vmovdquLoad .l256 .xmm1 (at_ .rsi (o * j + 32)),
    .vop (.vpermq .xmm0 .xmm0 0xD8), .vop (.vpermq .xmm1 .xmm1 0xD8)]

/-- The operands of product `j` of a block: the 32 coefficients `ld j`
loads, and those of `g = rdx + 1024 j`, the even ones in the words of `ymm6`
and the odd ones in those of `ymm10` (`vbase`'s order). -/
def rowMulYg (ld : Nat → List Instr) (j : Nat) : List Instr :=
  ld j ++ yload4o .rdx (1024 * j) .xmm6 .xmm7 .xmm8 .xmm9 ++ toY (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm5)


/-- Product `j` of a block (of the operands `mul j` loads), stored to
(`j = 0`) or added to the sums. -/
def rowSum (mul : Nat → List Instr) (j : Nat) : List Instr :=
  mul j ++ toY (if j = 0 then ptermSet else ptermAdd)

/-- The products `0, …, n - 1` of a block (`mul`), summed and reduced
(`pred`): the sums of the first coefficients, times `2⁻¹⁶`, in the words of
`ymm11`, and those of the second in `ymm12`, each in `(-q, q)`. -/
def rowSumsAux (mul : Nat → List Instr) : Nat → List Instr
  | 0 => []
  | n + 1 => rowSumsAux mul n ++ rowSum mul n

def rowSums (mul : Nat → List Instr) (n : Nat) : List Instr := rowSumsAux mul n ++ toY pred



/-- A block of row `k`: its `k` products (of the operands `rowMulYg ld`
loads) summed and reduced to the words of `ymm11` and `ymm12` (`rowSums`),
those made the coefficients (times `R² mod q`, then `vcadd`), and added to
the `u32`s at `rdi` as `finAccBodyY` does; the constants of the products
back, and `rsi` on by `sv`, the bytes of a block of `f`. -/
def rowBodyYg (ld : Nat → List Instr) (sv : BitVec 32) (k : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm13 (at_ .r8 0)] ++ rowSums (rowMulYg ld) k ++ yconst .xmm13 0x05490549 ++
    toY (vmont .xmm11 .xmm13 .xmm3 ++ vcadd .xmm11 .xmm3 ++ vmont .xmm12 .xmm13 .xmm3 ++ vcadd .xmm12 .xmm3) ++
    yconst .xmm15 3329 ++ [yb .vpxor .xmm14 .xmm14 .xmm14, yb .vpunpcklwd .xmm10 .xmm11 .xmm12,
      yb .vpunpckhwd .xmm9 .xmm11 .xmm12] ++
    finQ .xmm10 .vpunpcklwd 0 ++ finQ .xmm10 .vpunpckhwd 32 ++ finQ .xmm9 .vpunpcklwd 64 ++
    finQ .xmm9 .vpunpckhwd 96 ++ yconsts ++
    [.alu .add .rsi (.imm sv), .alu .add .rdx (.imm 128), .alu .add .rdi (.imm 128), .alu .add .r8 (.imm 32)]


/-- `t = rdi` plus the row `f = rsi` (`k` polynomials, loaded by `ld`, with
`sv` bytes to a block) times `g = rdx`, with the table of `tabAccY` at
`rcx + 3328`. -/
def rowYg (ld : Nat → List Instr) (sv : BitVec 32) (k : Nat) : Prog isa :=
  .seq (.block (yconsts ++ leaR .r8 .rcx oTabY)) (.seq (rcxLoop 8 (rowBodyYg ld sv k)) (.block [.vop .vzeroupper]))

/-- `rowYg` of `k` polynomials of `u32`s, 1024 bytes apart. -/
def rowY (k : Nat) : Prog isa := rowYg (rowLdY 1024) 128 k

/-- `rowYg` of `k` polynomials of `u16`s, 512 bytes apart. -/
def rowY16 (k : Nat) : Prog isa := rowYg (rowLdY16 512) 64 k

/-! ### A row of products to an accumulator -/

/-- The operands of product `j` of a block: the 32 coefficients `ld j`
loads, and the block of the accumulator `g = rdx + 512 j`, whose words are
already in `vbase`'s order. -/
def rowMulEg (ld : Nat → List Instr) (j : Nat) : List Instr :=
  ld j ++ [.vmovdquLoad .l256 .xmm6 (at_ .rdx (512 * j)), .vmovdquLoad .l256 .xmm10 (at_ .rdx (512 * j + 32))]

/-- A block of row `k` to an accumulator: its `k` products summed and
reduced to the words of `ymm11` and `ymm12` (`rowSums`), those made the
coefficients (times `R² mod q`, then `vcadd`), and stored to the accumulator
at `rdi`; `rsi` moves `st` bytes on. -/
def rowBodyEg (ld : Nat → List Instr) (st : BitVec 32) (k : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm13 (at_ .r8 0)] ++ rowSums (rowMulEg ld) k ++ yconst .xmm13 0x05490549 ++
    toY (vmont .xmm11 .xmm13 .xmm3 ++ vcadd .xmm11 .xmm3 ++ vmont .xmm12 .xmm13 .xmm3 ++ vcadd .xmm12 .xmm3) ++
    [.vmovdquStore .l256 (at_ .rdi 0) .xmm11, .vmovdquStore .l256 (at_ .rdi 32) .xmm12,
      .alu .add .rsi (.imm st), .alu .add .rdx (.imm 64), .alu .add .rdi (.imm 64), .alu .add .r8 (.imm 32)]

/-- The accumulator at `rdi` of the `k` products of the polynomials `ld`
loads from `f = rsi` (`st` bytes a block) and the accumulators from
`g = rdx`, 512 bytes apart, with the table of `tabAccY` at `rcx + 3328`. -/
def rowEg (ld : Nat → List Instr) (st : BitVec 32) (k : Nat) : Prog isa :=
  .seq (.block (yconsts ++ leaR .r8 .rcx oTabY)) (rcxLoop 8 (rowBodyEg ld st k))

/-- `rowEg` of polynomials of `u32`s, `o` bytes apart. -/
def rowEY (o k : Nat) : Prog isa := rowEg (rowLdY o) 128 k

/-- `rowEg` of polynomials of `u16`s, `o` bytes apart. -/
def rowEY16 (o k : Nat) : Prog isa := rowEg (rowLdY16 o) 64 k

end VG.Impl.MlKem.X86_64
