module

public import VerifiedGarbage.Impl.Bignum.X86_64.R2Squares

/-!
# `R² mod m` by word steps (x86-64)

For a modulus `m` of `w` words whose top bit is set (`2^(64 w - 1) ≤ m`)
and `w` a multiple of 4, `R² mod m` (`R = 2^(64 w)`) from `R mod m = R - m`
by `w / 4` steps `x := x 2^64 mod m`, which give `2^(16 w) R mod m`, then
two Montgomery squarings, which give `2^(64 w) R mod m`: where the doublings
of `vg_rsa_public`'s computation add one bit at a time, each step adds a
word, as a step of long division (Knuth, TAOCP vol. 2, §4.3.1, Algorithm D):

* the quotient `q = ⌊x 2^64 / m⌋` is estimated as
  `q̂ = min(⌊(u₂ 2^64 + u₁) / d⌋, 2^64 - 1)` from the top words `u₂`, `u₁` of
  `x` and `d` of `m`, which for `d ≥ 2^63` gives `q ≤ q̂ ≤ q + 2`, by
  division by the reciprocal `v = ⌊(2^128 - 1) / d⌋ - 2^64` (Möller and
  Granlund, "Improved division by invariant integers", IEEE Trans. Computers
  60(2), 2011, Algorithm 4), with its two corrections by masks (`quot`); `v`
  is computed once, by restoring division, a bit at a time (`recip`);
* `q̂` refined to the 3-by-2 estimate `min(⌊U / D⌋, 2^64 - 1)` from `x`'s top
  three words `U` and `m`'s top two `D`, which gives `q ≤ q̂ ≤ q + 1`, by
  `U - q̂ D` over three words and two corrections by masks (`refine3`);
* `t = x 2^64 - q̂ m` into the accumulator, over `w + 1` words in two's
  complement (`mulSub`);
* `m` added to `t` if it is negative, once, by a mask (`addBack`);
* `t` back into `x`.

Every branch and address depends only on `w`; the arithmetic on `m`'s words
(which are public) is branch-free. Other moduli take `vg_rsa_public`'s
computation (`old`); `choice` takes this one when it can.
-/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.R2Words

open VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-! ## A step -/

/-- The bases of `x` (`aR2`), `m`, the accumulator and the temporary (whose
first word is `v`), in `rbx`, `r10`, `r8` and `rbp`, and `w` in `r12`. -/
def bases : List Instr :=
  [.mov .rbx (.mem (hdr (sArr aR2))), .mov .r10 (.mem (hdr (sArr aN))), .mov .r8 (.mem (hdr (sArr aAcc))),
    .mov .r12 (.mem (hdr sW)), .mov .rbp (.mem (hdr (sArr aTmp)))]

/-- The divisor `d = m[w - 1]` into `rsi`, the dividend's top word
`u₂ = x[w - 1]` into `rdx` and the next `u₁ = x[w - 2]` into `rax`; `r9` all
ones if `u₂ = d` (as `x < m` has `u₂ ≤ d`, if `d - u₂ < 1`), and then `rdx`
zero. -/
def quotHead : List Instr :=
  [.mov .rsi (.mem (ix .r10 .r12 (-8))), .mov .rdx (.mem (ix .rbx .r12 (-8))), .mov .rax (.mem (ix .rbx .r12 (-16))),
    .mov .r9 (.reg .rsi), .alu .sub .r9 (.reg .rdx), .alu .cmp .r9 (.imm 1), .alu .sbb .r9 (.reg .r9),
    .mov .r11 (.reg .r9), .alu .xor .r11 (.imm (-1)), .alu .and .rdx (.reg .r11)]

/-- `⌊(u₂ 2^64 + u₁) / d⌋` into `rcx`, for `u₂ < d` in `rdx`, `u₁` in `rax`,
`d ≥ 2^63` in `rsi` and `v` at `rbp`: `(q₁, q₀) = v u₂ + (u₂, u₁)`, the
candidate `q₁ + 1` and its remainder `r = u₁ - (q₁ + 1) d mod 2^64`; one less
and `r + d` if `r > q₀`, and one more if then `r ≥ d`. -/
def quotMG : List Instr :=
  [.mov .r14 (.reg .rax), .mov .r13 (.reg .rdx), .mov .rax (.mem (at0 .rbp)), .mul .r13,
    .alu .add .rax (.reg .r14), .alu .adc .rdx (.reg .r13),
    .mov .rcx (.reg .rdx), .alu .add .rcx (.imm 1), .mov .r13 (.reg .rax), .mov .rax (.reg .rcx), .mul .rsi,
    .alu .sub .r14 (.reg .rax), .alu .cmp .r13 (.reg .r14), .alu .sbb .r15 (.reg .r15),
    .alu .add .rcx (.reg .r15), .alu .and .r15 (.reg .rsi), .alu .add .r14 (.reg .r15),
    .mov .r15 (.reg .rsi), .alu .sub .r15 (.imm 1), .alu .cmp .r15 (.reg .r14), .alu .adc .rcx (.imm 0)]

/-- `q̂` into `rcx`: the quotient, all ones if `u₂ = d`. -/
def quot : List Instr := quotHead ++ quotMG ++ ([.alu .or .rcx (.reg .r9)] : List Instr)

/-- `t = U - q̂ D` over three words, into `r15`, `r14`, `r13`, for `q̂` in
`rcx`, the top three words `U = (u₂, u₁, u₀)` of `x` and the top two
`D = (d, d₁)` of `m`: `q̂ D` into `rdx`, `rax`, `r9`, and its subtraction. -/
def quot3 : List Instr :=
  [.mov .rax (.mem (ix .r10 .r12 (-16))), .mul .rcx, .mov .r9 (.reg .rax), .mov .r11 (.reg .rdx),
    .mov .rax (.mem (ix .r10 .r12 (-8))), .mul .rcx, .alu .add .rax (.reg .r11), .alu .adc .rdx (.imm 0),
    .mov .r13 (.mem (ix .rbx .r12 (-24))), .alu .sub .r13 (.reg .r9),
    .mov .r14 (.mem (ix .rbx .r12 (-16))), .alu .sbb .r14 (.reg .rax),
    .mov .r15 (.mem (ix .rbx .r12 (-8))), .alu .sbb .r15 (.reg .rdx)]

/-- If `t` is negative (the top bit of `r15`): `q̂ := q̂ - 1` and `t := t + D`,
by a mask. -/
def fix3 : List Instr :=
  [.mov .r11 (.reg .r15), .alu .add .r11 (.reg .r11), .alu .sbb .r11 (.reg .r11), .alu .add .rcx (.reg .r11),
    .mov .rax (.mem (ix .r10 .r12 (-16))), .alu .and .rax (.reg .r11),
    .mov .rdx (.mem (ix .r10 .r12 (-8))), .alu .and .rdx (.reg .r11),
    .alu .add .r13 (.reg .rax), .alu .adc .r14 (.reg .rdx), .alu .adc .r15 (.imm 0)]

/-- `q̂` refined to `min(⌊U / D⌋, 2^64 - 1)` by the 3-by-2 estimate's two
corrections (`q̂` is at most two more), which is at least the quotient `q`
and at most `q + 1`. -/
def refine3 : List Instr := quot3 ++ fix3 ++ fix3

/-- A bit of restoring division by `d` (`rsi`) of the remainder `r < d`
(`rdx`) and the next bit of `u₁` (the top of `rax`): `r := 2 r + bit`, with
its carry; subtract `d` if the carry is set or `r ≥ d` (into `r15`, a mask),
by `cmov`; the quotient `rcx := 2 rcx + 1` if so, `2 rcx` otherwise; and the
count `r13` down. -/
def divBit : List Instr :=
  [.alu .add .rax (.reg .rax), .alu .adc .rdx (.reg .rdx), .alu .sbb .r11 (.reg .r11),
    .mov .r14 (.reg .rdx), .alu .sub .r14 (.reg .rsi), .alu .sbb .r15 (.reg .r15),
    .alu .xor .r15 (.imm (-1)), .alu .or .r15 (.reg .r11), .alu .test .r15 (.reg .r15),
    .cmov .ne .rdx (.reg .r14), .alu .add .rcx (.reg .rcx), .alu .sub .rcx (.reg .r15),
    .alu .sub .r13 (.imm 1)]

/-- `v = ⌊(2^128 - 1) / d⌋ - 2^64 = ⌊((2^64 - 1 - d) 2^64 + 2^64 - 1) / d⌋`
for `d = m[w - 1]`, by 64 bits of restoring division, into the first word of
the temporary (at `r8`). -/
def recip : Prog isa :=
  .seq (.block [.mov .rsi (.mem (ix .r10 .r12 (-8))), .mov .rdx (.reg .rsi), .alu .xor .rdx (.imm (-1)),
      .mov .rax (.imm (-1)), .mov32 .rcx (.imm 0), .mov32 .r13 (.imm 64)])
    (.seq (.loop (.block divBit) .ne) (.block [.store (at0 .r8) .rcx]))

/-- Word 0 of `t = x 2^64 - q̂ m`: `0 - lo(q̂ m₀)`, its borrow into `rbp`
(a mask) and `hi(q̂ m₀)` into `r9`. -/
def subHead : List Instr :=
  [.mov .rax (.mem (at0 .r10)), .mul .rcx, .mov .r9 (.reg .rdx), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .store (at0 .r8) .rdx, cfToRbp]

/-- Word `i = r14` of `t`: `x[i - 1] - lo(q̂ mᵢ + r9) - borrow`, and
`r9 := hi(q̂ mᵢ + r9)`. -/
def subBody : List Instr :=
  [.mov .rax (.mem (ix .r10 .r14)), .mul .rcx, .alu .add .rax (.reg .r9), .alu .adc .rdx (.imm 0),
    .mov .r9 (.reg .rdx), .mov .rdx (.mem (ix .rbx .r14 (-8))), cfFromRbp, .alu .sbb .rdx (.reg .rax), cfToRbp,
    .store (ix .r8 .r14) .rdx]

/-- Word `w` of `t`: `x[w - 1] - r9 - borrow`. -/
def subTop : List Instr :=
  [.mov .rdx (.mem (ix .rbx .r12 (-8))), cfFromRbp, .alu .sbb .rdx (.reg .r9), .store (ix .r8 .r12) .rdx]

/-- `t := x 2^64 - q̂ m` over `w + 1` words, modulo `2^(64 (w + 1))`. -/
def mulSub : Prog isa := .seq (.block subHead) (.seq (wordLoop 1 subBody) (.block subTop))

/-- The mask of `t`'s sign (the top bit of its word `w`) into `r11`, and no
carry in `rbp`. -/
def addHead : List Instr :=
  [.mov .rax (.mem (ix .r8 .r12)), .alu .add .rax (.reg .rax), .alu .sbb .r11 (.reg .r11), .mov32 .rbp (.imm 0)]

/-- Word `i = r14` of `t := t + (m & mask)`. -/
def addBody : List Instr :=
  [.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r11), cfFromRbp, .alu .adc .rax (.mem (ix .r8 .r14)),
    cfToRbp, .store (ix .r8 .r14) .rax]

/-- Word `w` of `t` plus the carry. -/
def addTop : List Instr :=
  [.mov .rax (.mem (ix .r8 .r12)), cfFromRbp, .alu .adc .rax (.imm 0), .store (ix .r8 .r12) .rax]

/-- `t := t + m` if `t` is negative, modulo `2^(64 (w + 1))`. -/
def addBack : Prog isa := .seq (.block addHead) (.seq (wordLoop 0 addBody) (.block addTop))

/-- `w` words of the accumulator (`r8`) into `x` (`rbx`), as `copyWords` copies
them from `rsi`. -/
def copyBack : Prog isa :=
  .seq (.block [.mov .rsi (.reg .r8)]) (wordLoop 0 [.mov .rax (.mem (ix .rsi .r14)), .store (ix .rbx .r14) .rax])

/-- `x := x 2^64 mod m`. -/
def step : Prog isa := seqs [.block bases, .block quot, .block refine3, mulSub, addBack, copyBack]

/-- `step` `rcx` times (a public count, at least 1), counted in `sCnt`. -/
def steps : Prog isa :=
  .seq (.block [.store (hdr sCnt) .rcx])
    (.loop (.seq step (.block [.mov .rcx (.mem (hdr sCnt)), .alu .sub .rcx (.imm 1), .store (hdr sCnt) .rcx])) .ne)

/-! ## `R² mod m` -/

/-- Word `i = r14` of `x := 0 - m`, the borrow in `rbp`. -/
def negBody : List Instr :=
  [.mov32 .rax (.imm 0), cfFromRbp, .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp, .store (ix .rbx .r14) .rax]

variable (mul : Nat → Nat → Nat → Prog isa)

/-- `x := R - m`, `v`, `w / 4` steps, and two squarings. -/
def fast : Prog isa := seqs [
  .block [.mov .rbx (.mem (hdr (sArr aR2))), .mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)),
    .mov .r8 (.mem (hdr (sArr aTmp))), .mov32 .rbp (.imm 0)],
  wordLoop 0 negBody,
  recip,
  .block [.mov .rcx (.mem (hdr sW)), .shift .shr .rcx 2],
  steps,
  R2Squares.run mul 1]

/-- `vg_rsa_public`'s computation of `R² mod m`: `2^(b - 1)` for the bit
length `b` of `m`, doubled `64 - j + w` times (for the top bit `j` of its top
word), and squared six times. -/
def old : List (Prog isa) := [
  .block [.mov .rax (.mem (ix .r10 .r12 (-8)))],
  topBit,
  .block [.store (hdr sCnt) .rcx, .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
  setWord aR2 .rcx,
  .block [.mov .rcx (.mem (hdr sCnt)), .alu .add .rcx (.mem (hdr sW))],
  doubles aN aAcc aTmp aR2 sCnt,
  R2Squares.run mul 5]

/-- ZF set iff the top bit of `m`'s top word is set and `w` (`r12`) is a
multiple of 4, for `m` at `r10`. -/
def fastTest : List Instr :=
  [.mov .rax (.mem (ix .r10 .r12 (-8))), .shift .shr .rax 63, .alu .xor .rax (.imm 1), .mov .rcx (.reg .r12),
    .alu .and .rcx (.imm 3), .alu .or .rax (.reg .rcx)]

/-- `R² mod m` by `fast` when it applies, by `old` otherwise. -/
def choice : Prog isa := .seq (.block fastTest) (.ite .e (fast mul) (seqs (old mul)))

end VG.Impl.Bignum.X86_64.R2Words
