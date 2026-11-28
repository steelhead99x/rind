module

public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.X25519.X86_64.Adx

/-!
# Montgomery arithmetic modulo an odd multiword modulus, on x86-64

Arithmetic modulo an odd `m < 2^(64 n)`, `n` 64-bit words, on
numbers below `m` held in the working space as `n` little-endian words at a
constant offset from its base, which is in `rdi`. The modulus is in the
working space too, at `M.mo`; `M.minv` is `-m⁻¹ mod 2⁶⁴`. With
`R = 2^(64 n)`:

* `mul o a b`: `[o] = [a] [b] R⁻¹ mod m`, by coarsely integrated operand
  scanning (CIOS): for each word `a_i` of `[a]`, the accumulator
  `t += a_i [b]`, then `t += u m` for `u = t₀ m' mod 2⁶⁴`, which makes the
  low word zero, and `t /= 2⁶⁴`. The `n + 2` accumulator words are
  registers (`acc n`); the division renames them (round `i`'s words are
  `win n i 0`, `win n i 1`, …), so it costs nothing. For a modulus
  `m ≡ -1 (mod 2⁶⁴)` (`Red.friendly`, P-256's `p`), `u = t₀` and
  `t + t₀ m = (t - t₀) + 2⁶⁴ t₀ m'` with `m' = (m + 1) / 2⁶⁴`, so the words
  above `t₀` get `t₀ m'`, one product per word of `m'` but those of zero
  (`redWords`); for `p`, whose `m'` is `2³² + 2¹²⁸ (2⁶⁴ − 2³² + 1)`, no
  product at all, but shifts and subtractions (`shiftRed`). For P-384's `p`
  (`M.sparse`), `u = t₀ (2³² + 1) mod 2⁶⁴` by a shift and an addition, and
  `t + u m = t - u c + 2³⁸⁴ u` for `c = 2³⁸⁴ - m` of three words: two
  products of `u` by `c`'s words, the result less `t₀` subtracted from the
  words above `t₀`, and `u` added at `2³⁸⁴` (`redSparse`; with BMI2,
  `redSparseX`, `u` and both products by `mulx`, which keeps the shift and
  the multiplications off the ports the carry chains need, and the first row
  of the product one carry chain, `mulRowS0`). With BMI2 and ADX (`M.adx`), a row
  is `mulx` for each word, its low half added through OF (`adox`) and its
  high half through CF (`adcx`), two carry chains that do not wait for each
  other (`roundX`). The accumulator stays below `2m`, and the result is
  reduced by `csub`. Four words for `p` with BMI2 and ADX are X25519's
  `mulX`'s product `a b` instead (`mulRX`), or for a square its `sqrX`'s,
  each product of two different words computed once and doubled (`sqrRX`),
  into eight registers, then four reductions of its low half in a window of
  four registers, each by two `mulx` and one carry chain (`redRoundX`), and
  its high half added (`redRX`).
* `add o a b`, `sub o a b`: `[a] ± [b] mod m`, with a conditional
  subtraction (`csub`) or addition of `m`.
* `csub`: a number below `2m` in `n` registers and a top word (0 or 1)
  reduced below `m`: the difference with `m` is computed, and taken if it
  did not borrow. For at most four words it is computed in `rax`, `rcx`,
  `rdx` and `rbp` and taken by `cmovae` (`csubC`); for P-384's `p`, in place,
  with `p` added back under the mask of the borrow, its words `rax`'s low
  half, `rax ≪ 32`, `rax ≪ 1` and `rax` (`csubS`, and `sub384` for the
  subtraction); for more, into the temporary area `[M.tmp]`, and selected by
  `cmovae` (`csubM`).

For `n ≤ 6` the accumulator is in registers (`mulR`, `addR`, `subR`). For
more words (P-521's 9) it does not fit, and `mulW`, `addW` and `subW` keep
its `n` low words in the temporary area `[M.tmp]` and its two top words in
`r9` and `r10`:

* `mulW o a b`: CIOS as above, each row adding into `[M.tmp]` word by word
  through `r8` (`memRow`), and the division by `2⁶⁴` moving the words down
  (`shiftDown`); then `csubW`.
* `csubW`: the accumulator (below `2m`, its top word in `r9`) reduced below
  `m`: the difference with `m` is computed into `[o]` (`chainW`, word by
  word through `r8`), and the accumulator selected instead under a mask if
  it borrowed.
* `addW`, `subW`: the sum (and its carry in `r9`) or the difference into
  `[M.tmp]`, then `csubW`, or `m` added under the mask of the borrow (through
  `[o]`).

* `mulP o a b`: for P-521's `p = 2⁵²¹ - 1` (its friendly reduction's words,
  `p521Ws`), Montgomery multiplication by columns (product scanning), the
  three-word accumulator in registers, each column's products loaded from
  `[a]` and `[b]`; the reduction's `u_k`, the low words of the first nine
  columns, need no multiplication by `-p⁻¹` and add `512 u_k` to column
  `k + 8`; then `csubW`. `sqrP o a`, `mulP o a a` with each product of two
  different words computed once and added twice.

* `mulF o a b`: for any other modulus of eight or nine words (P-521's order),
  Montgomery multiplication by columns too, each column also adding the
  reduction's `u_k m_j` and the first nine computing their `u` (Koç, Acar and
  Kaliski's FIPS).

`mul`, `add` and `sub` choose by `n` (and `mul` by the reduction, and whether
it squares). Every multiplication is `mul` or `mulx`, every
selection a mask or conditional move, and every address `rdi` plus a constant: nothing but `rdi`
may affect timing. The operations use the registers `rax`, `rcx`, `rdx`,
`rbp` and `acc n` (`r8`–`r13` for `n = 4`, and `r14`, `r15` for `mulRX` and `sqrRX`;
`r8`–`r15` from `n = 6`), and
write only `[o]` and `[M.tmp]`.
-/

@[expose] public section

namespace VG.Impl.Mont.X86_64

open VG.X86_64

/-- `[rdi + d]`: byte `d` of the working space. -/
def sc (d : Nat) : MemOp := { base := .rdi, disp := d }

/-- The accumulator's registers: `n + 2` of `r8`–`r15`. -/
def acc (n : Nat) : List Reg := [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15].take (n + 2)

/-- Word `j` of the accumulator in round `i`: the registers rotate by one
word each round. -/
def win (n i j : Nat) : Reg := (acc n).getD ((i + j) % (n + 2)) .r8

/-- `t:c = t + c + ai · src` (a multiply-accumulate step; it never
overflows). -/
def mulStep (t c ai : Reg) (src : Src) : List Instr :=
  [.mov .rax src, .mul ai, .alu .add .rax (.reg c), .alu .adc .rdx (.imm 0),
    .alu .add t (.reg .rax), .alu .adc .rdx (.imm 0), .mov c (.reg .rdx)]

/-- `ts, carry rbp += rcx · [d], …`: a multiply-accumulate step for each of
the words `ts` and the words at `d`, `d + 8`, …. -/
def mulSteps : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, d => mulStep t .rbp .rcx (.mem (sc d)) ++ mulSteps ts (d + 8)

/-- `ts += rcx · [d]`, its carry word in `rbp`. -/
def mulRow (ts : List Reg) (d : Nat) : List Instr := .mov32 .rbp (.imm 0) :: mulSteps ts d

/-- `mulStep` with the carry word added last: `t += lo`, then `t += c`, so
that the carry from one step to the next passes through one addition (`add`,
`adc`) rather than two. -/
def mulStepL (t c ai : Reg) (src : Src) : List Instr :=
  [.mov .rax src, .mul ai, .alu .add t (.reg .rax), .alu .adc .rdx (.imm 0),
    .alu .add t (.reg c), .alu .adc .rdx (.imm 0), .mov c (.reg .rdx)]

/-- `mulSteps` by `mulStepL`. -/
def mulStepsL : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, d => mulStepL t .rbp .rcx (.mem (sc d)) ++ mulStepsL ts (d + 8)

/-- `mulRow` by `mulStepL`. -/
def mulRowL (ts : List Reg) (d : Nat) : List Instr := .mov32 .rbp (.imm 0) :: mulStepsL ts d

/-- `mulRowL` if `late`, else `mulRow`. -/
def mulRowB (late : Bool) (ts : List Reg) (d : Nat) : List Instr := if late then mulRowL ts d else mulRow ts d

/-- Whether `mul`'s rows add the carry last: for a general modulus. A sparse
or friendly modulus (`p` of P-384, P-256, P-521, …) keeps `mulRow`, whose
order measured faster there. -/
def lateRow (M : Mod) : Bool := decide (M.red = .general) && !M.sparse

/-- The carry word `rbp` added into `t_n` and its carry into `t_{n+1}`. -/
def carryUp (tn tn1 : Reg) : List Instr := [.alu .add tn (.reg .rbp), .alu .adc tn1 (.imm 0)]

/-- The words of round `i`'s accumulator, low to high. -/
def wins (n i : Nat) : List Reg := (List.range (n + 2)).map (win n i)

/-- `ts += t₀ w` (`ts` of at least two words): the product `rdx:rax` added
to the first two words, and its carry up the others. -/
def addProd (t0 : Reg) (w : BitVec 64) : List Reg → List Instr
  | t :: t' :: rest => ([.movImm64 .rax w, .mul t0, .alu .add t (.reg .rax), .alu .adc t' (.reg .rdx)] : List Instr) ++
      rest.map fun r => .alu .adc r (.imm 0)
  | _ => []

/-- `ts += t₀ m'` for the words `ws` of `m'`: each word but zero multiplied by
`t₀` and added at its place. -/
def redWords (t0 : Reg) : List MWord → List Reg → List Instr
  | [], _ => []
  | w :: ws, ts => (if w = .zero then [] else addProd t0 (BitVec.ofNat 64 w.val) ts) ++ redWords t0 ws ts.tail

/-- `k` if `m'`'s words are `2ᵏ, 0, 2⁶⁴ − 2ᵏ + 1, 0` (P-256's `p`, `k = 32`),
which `shiftRed` multiplies by without `mul`. -/
def shiftK? : List MWord → Option Nat
  | [.pow2 k, .zero, .gen v, .zero] => if 0 < k ∧ k < 64 ∧ v = 2 ^ 64 - 2 ^ k + 1 then some k else none
  | _ => none

/-- `rdx:rax = t₀ 2ᵏ` (`t₀ << k`, `t₀ >> (64 − k)`) and `rbp:rcx = t₀ (2⁶⁴ − 2ᵏ + 1)`:
without BMI2, as `2⁶⁴ t₀ + t₀ − t₀ 2ᵏ` (`t₀ − rax`, then `t₀ − rdx` less
the borrow); with it (`x`), by `mulx`, which waits on no borrow. -/
def shiftProd (x : Bool) (t0 : Reg) (k : Nat) : List Instr :=
  if x then
    [.mov .rdx (.reg t0), .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 64 - 2 ^ k + 1)), .mulx .rbp .rcx (.reg .rcx),
      .mov .rax (.reg t0), .shift .shl .rax k, .shift .shr .rdx (64 - k)]
  else
    [.mov .rax (.reg t0), .shift .shl .rax k, .mov .rdx (.reg t0), .shift .shr .rdx (64 - k),
      .mov .rcx (.reg t0), .alu .sub .rcx (.reg .rax), .mov .rbp (.reg t0), .alu .sbb .rbp (.reg .rdx)]

/-- `ts += t₀ m'` for `m' = 2ᵏ + 2¹²⁸ (2⁶⁴ − 2ᵏ + 1)`, without `mul`
(`shiftProd`); the four words are added to the first four of `ts` in one
carry chain, its carry up the others. -/
def shiftRed (x : Bool) (t0 : Reg) (k : Nat) : List Reg → List Instr
  | w1 :: w2 :: w3 :: w4 :: rest =>
    shiftProd x t0 k ++ ([.alu .add w1 (.reg .rax), .alu .adc w2 (.reg .rdx), .alu .adc w3 (.reg .rcx),
      .alu .adc w4 (.reg .rbp)] : List Instr) ++ rest.map fun r => .alu .adc r (.imm 0)
  | _ => []

/-- `ts += t₀ m'` for the words `ws` of `m'`: by `shiftRed` if it applies, else
by `redWords`. -/
def redFriendly (x : Bool) (t0 : Reg) (ws : List MWord) (ts : List Reg) : List Instr :=
  match shiftK? ws with
  | some k => shiftRed x t0 k ts
  | none => redWords t0 ws ts

/-- The words of `c = 2³⁸⁴ - p = 2¹²⁸ + 2⁹⁶ - 2³² + 1` for P-384's `p` but the
top one, which is 1. -/
def sparseC0 : BitVec 64 := BitVec.ofNat 64 0xffffffff00000001
def sparseC1 : BitVec 32 := BitVec.ofNat 32 0xffffffff

/-- `rcx = u = t₀ (2³² + 1) mod 2⁶⁴`, P-384's `t₀ m' mod 2⁶⁴`. -/
def uSparse (t0 : Reg) : List Instr := [.mov .rcx (.reg t0), .shift .shl .rcx 32, .alu .add .rcx (.reg t0)]

/-- `rbp + 2⁶⁴ rdx + 2¹²⁸ t₀ = ⌊u c / 2⁶⁴⌋` for `u` in `rcx` (kept), whose low
word the reduction does not need. -/
def prodSparse (t0 : Reg) : List Instr :=
  [.movImm64 .rax sparseC0, .mul .rcx, .mov .rbp (.reg .rdx), .mov32 .rax (.imm sparseC1), .mul .rcx,
    .alu .add .rbp (.reg .rax), .alu .adc .rdx (.reg .rcx), .mov32 t0 (.imm 0), .alu .adc t0 (.imm 0)]

/-- `t₁ … t₇ += 2³²⁰ u - (rbp + 2⁶⁴ rdx + 2¹²⁸ t₀)`: the subtraction from
`t₁ … t₅`, its borrow taken from `u`, which is added at `t₆`. -/
def subSparse (t0 t1 t2 t3 t4 t5 t6 t7 : Reg) : List Instr :=
  [.alu .sub t1 (.reg .rbp), .alu .sbb t2 (.reg .rdx), .alu .sbb t3 (.reg t0), .alu .sbb t4 (.imm 0),
    .alu .sbb t5 (.imm 0), .alu .sbb .rcx (.imm 0), .alu .add t6 (.reg .rcx), .alu .adc t7 (.imm 0)]

/-- The reduction of P-384's round on the window `ts`: `t += u p` for
`u = t₀ (2³² + 1) mod 2⁶⁴`, as `t - u c + 2³⁸⁴ u` with `c = 2³⁸⁴ - p`, whose
low word is `t₀`: the words above `t₀` get `2³²⁰ u - ⌊u c / 2⁶⁴⌋`; then
`t₀ = 0`. -/
def redSparse : List Reg → List Instr
  | [t0, t1, t2, t3, t4, t5, t6, t7] =>
    uSparse t0 ++ prodSparse t0 ++ subSparse t0 t1 t2 t3 t4 t5 t6 t7 ++ ([.mov32 t0 (.imm 0)] : List Instr)
  | _ => []

/-! ### P-384's reduction with BMI2 -/

/-- `2³² + 1`, the factor of `u = t₀ (2³² + 1) mod 2⁶⁴`. -/
def sparseK : BitVec 64 := BitVec.ofNat 64 0x100000001

/-- `rdx = u = t₀ (2³² + 1) mod 2⁶⁴` by `imul`: the multiplier's port,
rather than a shift and an addition on the ports that the carry chains need;
unlike `mulx`, it computes no high half, which this does not need. -/
def uSparseX (t0 : Reg) : List Instr := [.movImm64 .rdx sparseK, .imul .rdx t0]

/-- `rax + 2⁶⁴ rcx + 2¹²⁸ rbp = ⌊u c / 2⁶⁴⌋` for `u` in `rdx` (kept), by
`mulx`, through `t₀`: the two products' halves added in one carry chain. -/
def prodSparseX (t0 : Reg) : List Instr :=
  [.movImm64 .rax sparseC0, .mulx .rax .rcx (.reg .rax), .mov32 .rcx (.imm sparseC1), .mulx .rcx t0 (.reg .rcx),
    .alu .add .rax (.reg t0), .alu .adc .rcx (.reg .rdx), .mov32 .rbp (.imm 0), .alu .adc .rbp (.reg .rbp)]

/-- `t₁ … t₇ += 2³²⁰ u - C` for `C = rax + 2⁶⁴ rcx + 2¹²⁸ rbp` and `u` in
`rdx`: the subtraction from `t₁ … t₅`, its borrow taken from `u`, which is
added at `t₆`. -/
def subSparseX (t1 t2 t3 t4 t5 t6 t7 : Reg) : List Instr :=
  [.alu .sub t1 (.reg .rax), .alu .sbb t2 (.reg .rcx), .alu .sbb t3 (.reg .rbp), .alu .sbb t4 (.imm 0),
    .alu .sbb t5 (.imm 0), .alu .sbb .rdx (.imm 0), .alu .add t6 (.reg .rdx), .alu .adc t7 (.imm 0)]

/-- `redSparse` with BMI2: `u` and its products by `mulx` (`uSparseX`,
`prodSparseX`). -/
def redSparseX : List Reg → List Instr
  | [t0, t1, t2, t3, t4, t5, t6, t7] =>
    uSparseX t0 ++ prodSparseX t0 ++ subSparseX t1 t2 t3 t4 t5 t6 t7 ++ ([.mov32 t0 (.imm 0)] : List Instr)
  | _ => []

/-- A round of P-384's reduction on six words `d₀ … d₅` holding `T < 2³⁸⁴`,
with BMI2: `d₁ … d₅, d₀` become `(T + u p) / 2⁶⁴`, which is below `2³⁸⁴`, so
its top word is `u` less the borrow of the subtraction (no seventh word). -/
def redShortX : List Reg → List Instr
  | [d0, d1, d2, d3, d4, d5] =>
    uSparseX d0 ++ prodSparseX d0 ++
    ([.alu .sub d1 (.reg .rax), .alu .sbb d2 (.reg .rcx), .alu .sbb d3 (.reg .rbp), .alu .sbb d4 (.imm 0),
      .alu .sbb d5 (.imm 0), .mov d0 (.reg .rdx), .alu .sbb d0 (.imm 0)] : List Instr)
  | _ => []

/-- `redShortX` without BMI2: `u` by `uSparse` (in `rcx`), its products by
`prodSparse` (through `d₀`, which `u` less the borrow then replaces). -/
def redShortM : List Reg → List Instr
  | [d0, d1, d2, d3, d4, d5] =>
    uSparse d0 ++ prodSparse d0 ++
    ([.alu .sub d1 (.reg .rbp), .alu .sbb d2 (.reg .rdx), .alu .sbb d3 (.reg d0), .alu .sbb d4 (.imm 0),
      .alu .sbb d5 (.imm 0), .mov d0 (.reg .rcx), .alu .sbb d0 (.imm 0)] : List Instr)
  | _ => []

/-- A round of P-384's reduction on six words: `redShortX` with BMI2 (`x`),
else `redShortM`. -/
def redShort (x : Bool) (ds : List Reg) : List Instr := if x then redShortX ds else redShortM ds

/-- The reduction of round `i`: `t += u m` with `u = t₀ m' mod 2⁶⁴`, after
which `t₀ = 0`; or, for a friendly modulus, the words above `t₀` get `t₀ m'`
and `t₀ = 0`; or, for P-384's `p`, `redSparse`. -/
def redRound (M : Mod) (i : Nat) : List Instr :=
  let t := win M.n i
  if M.sparse then redSparse (wins M.n i) else
  match M.red with
  | .general => ([.mov .rax (.reg (t 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax)] : List Instr) ++
      mulRowB (lateRow M) ((List.range M.n).map t) M.mo ++ carryUp (t M.n) (t (M.n + 1))
  | .friendly ws => redFriendly false (t 0) ws (wins M.n i).tail ++ ([.mov32 (t 0) (.imm 0)] : List Instr)

/-- Round `i` of `mul o a b` by `mul`: `t += a_i [b]`, then the reduction. -/
def roundM (M : Mod) (a b i : Nat) : List Instr :=
  let t := win M.n i
  let low := (List.range M.n).map t
  ([.mov .rcx (.mem (sc (a + 8 * i)))] : List Instr) ++ mulRowB (lateRow M) low b ++ carryUp (t M.n) (t (M.n + 1)) ++
    redRound M i

/-! ### With BMI2 and ADX -/

/-- `xor ebp, ebp`: `rbp = 0`, and both carries (CF and OF) clear. -/
def clearX : Instr := .alu32 .xor .rbp (.reg .rbp)

/-- `mulx rcx, rax, src`, `adox x, rax`, `adcx y, rcx`: `rdx · src` added at
`x` and `y` (the next word), the low half through OF and the high half
through CF. -/
def madd (x y : Reg) (src : Src) : List Instr :=
  [.mulx .rcx .rax src, .adox x (.reg .rax), .adcx y (.reg .rcx)]

/-- `k` products `rdx · [d]`, `rdx · [d + 8]`, … added along the words `ts`. -/
def maddSteps : Nat → List Reg → Nat → List Instr
  | k + 1, x :: y :: rest, d => madd x y (.mem (sc d)) ++ maddSteps k (y :: rest) (d + 8)
  | _, _, _ => []

/-- The carries left by `maddSteps` (`rbp = 0`): OF into `tn`, then CF and
OF into `tn1`. -/
def carriesX (tn tn1 : Reg) : List Instr :=
  [.adox tn (.reg .rbp), .adcx tn1 (.reg .rbp), .adox tn1 (.reg .rbp)]

/-- `ts += rdx · [d]`, `n` words, for `n + 2` words `ts`. -/
def rowX (n : Nat) (ts : List Reg) (d : Nat) : List Instr :=
  clearX :: maddSteps n ts d ++ carriesX (ts.getD n .r8) (ts.getD (n + 1) .r8)

/-- Round `i` of `mul o a b` with BMI2 and ADX: `t += a_i [b]` (`rowX`), then
the reduction: `t += u m` by `rowX`, `u = t₀ m' mod 2⁶⁴` in `rdx`, or as
`redRound` for a friendly modulus, or by `redSparseX` for P-384's `p`. -/
def roundX (M : Mod) (a b i : Nat) : List Instr :=
  let t := win M.n i
  ([.mov .rdx (.mem (sc (a + 8 * i)))] : List Instr) ++ rowX M.n (wins M.n i) b ++
  if M.sparse then redSparseX (wins M.n i) else
  match M.red with
  | .general => ([.mov .rax (.reg (t 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rdx (.reg .rax)] : List Instr) ++
      rowX M.n (wins M.n i) M.mo
  | .friendly ws => redFriendly true (t 0) ws (wins M.n i).tail ++ ([.mov32 (t 0) (.imm 0)] : List Instr)

/-- Round `i` of `mul o a b`. -/
def round (M : Mod) (a b i : Nat) : List Instr := if M.adx then roundX M a b i else roundM M a b i

/-- `[tmp + d] = ts - [mo + d]`, word by word, with `op` (`sub`, then
`sbb`) on the first word, through `rax`. -/
def diffs (op : AluOp) : List Reg → Nat → Nat → List Instr
  | [], _, _ => []
  | t :: ts, mo, tmp => ([.mov .rax (.reg t), .alu op .rax (.mem (sc mo)), .store (sc tmp) .rax] : List Instr) ++
    diffs .sbb ts (mo + 8) (tmp + 8)

/-- Replace `ts` by `[tmp]` when the subtraction did not borrow, preserving
its carry flag across all words. -/
def selects : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, tmp => ([.cmov .ae t (.mem (sc tmp))] : List Instr) ++ selects ts (tmp + 8)

/-- `ts` (and the top word `top`), below `2m`, reduced modulo `m`: the
difference with `m` is computed into `[tmp]`; its final borrow selects it. -/
def csubM (M : Mod) (ts : List Reg) (top : Reg) : List Instr :=
  diffs .sub ts M.mo M.tmp ++
  ([.mov .rax (.reg top), .alu .sbb .rax (.imm 0)] : List Instr) ++ selects ts M.tmp

/-- The registers `csubC` computes the difference in. -/
def cregs : List Reg := [.rax, .rcx, .rdx, .rbp]

/-- `ds = ts - [mo]`, word by word, with `op` (`sub`, then `sbb`) on the
first word: its borrow is in CF. -/
def diffsC (op : AluOp) : List Reg → List Reg → Nat → List Instr
  | t :: ts, d :: ds, mo => ([.mov d (.reg t), .alu op d (.mem (sc mo))] : List Instr) ++ diffsC .sbb ts ds (mo + 8)
  | _, _, _ => []

/-- `ts = ds` if CF is clear (`cmovae`). -/
def cmovs : List Reg → List Reg → List Instr
  | t :: ts, d :: ds => .cmov .ae t (.reg d) :: cmovs ts ds
  | _, _ => []

/-- `csubM` in registers, for at most four words: the difference with `m` in
`cregs`, the top word's borrow, and the difference moved to `ts` if it did not
borrow. -/
def csubC (M : Mod) (ts : List Reg) (top : Reg) : List Instr :=
  diffsC .sub ts cregs M.mo ++ ([.alu .sbb top (.imm 0)] : List Instr) ++ cmovs ts cregs

/-- `ts op= [b]`, word by word, with `op` on the first word and `op'` on the
others (`add` and `adc`, `sub` and `sbb`). -/
def chain (op op' : AluOp) : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, b => .alu op t (.mem (sc b)) :: chain op' op' ts (b + 8)

/-- P-384's `p` masked by `rax` (all ones or zero): its words but the three
all-ones ones, which are `rax`, in `rcx` (`2³² - 1`), `rdx` (`2⁶⁴ - 2³²`) and
`rbp` (`2⁶⁴ - 2`). -/
def p384Mask : List Instr :=
  [.mov32 .rcx (.reg .rax), .mov .rdx (.reg .rax), .shift .shl .rdx 32, .mov .rbp (.reg .rax),
    .shift .shl .rbp 1]

/-- `ts += ` the masked P-384 `p` of `p384Mask`. -/
def p384Add : List Reg → List Instr
  | [t0, t1, t2, t3, t4, t5] => [.alu .add t0 (.reg .rcx), .alu .adc t1 (.reg .rdx), .alu .adc t2 (.reg .rbp),
      .alu .adc t3 (.reg .rax), .alu .adc t4 (.reg .rax), .alu .adc t5 (.reg .rax)]
  | _ => []

/-- `csub` for P-384's `p`, in registers: `ts - p`, and `p` added back under
the mask of its borrow. -/
def csubS (M : Mod) (ts : List Reg) (top : Reg) : List Instr :=
  chain .sub .sbb ts M.mo ++ ([.alu .sbb top (.imm 0), .alu .sbb .rax (.reg .rax)] : List Instr) ++ p384Mask ++ p384Add ts

/-- `ts -= ` P-384's `p` as `p384Mask` leaves it in registers (for `rax`
all ones). -/
def p384Sub : List Reg → List Instr
  | [t0, t1, t2, t3, t4, t5] => [.alu .sub t0 (.reg .rcx), .alu .sbb t1 (.reg .rdx), .alu .sbb t2 (.reg .rbp),
      .alu .sbb t3 (.reg .rax), .alu .sbb t4 (.reg .rax), .alu .sbb t5 (.reg .rax)]
  | _ => []

/-- `csubS` without the modulus in memory: P-384's `p` into registers
(`p384Mask` of all ones), subtracted, and added back under the mask of the
borrow. -/
def csubR (ts : List Reg) (top : Reg) : List Instr :=
  ([.mov .rax (.imm (-1))] : List Instr) ++ p384Mask ++ p384Sub ts ++
    ([.alu .sbb top (.imm 0), .alu .sbb .rax (.reg .rax)] : List Instr) ++ p384Mask ++ p384Add ts

/-- `ts` (and the top word `top`), below `2m`, reduced modulo `m`: by `csubC`
for at most four words, by `csubS` for P-384's `p`, else by `csubM`. -/
def csub (M : Mod) (ts : List Reg) (top : Reg) : List Instr :=
  if ts.length ≤ 4 then csubC M ts top else if M.sparse then csubS M ts top else csubM M ts top

/-- `[o] = ts`. -/
def stores : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, o => .store (sc o) t :: stores ts (o + 8)

/-- `ts = [a]`. -/
def loads : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, a => .mov t (.mem (sc a)) :: loads ts (a + 8)

/-- `ts := 0`. -/
def zeros (ts : List Reg) : List Instr := ts.map fun t => .mov32 t (.imm 0)

/-- The words of `redRX`'s result, `(t + U m) / 2²⁵⁶`, but its top one, `r8`. -/
def sqLow : List Reg := [.r12, .r13, .r14, .r15]

/-- A round of `redRX`'s reduction, in the window `t, w₁, w₂, w₃` of four
words `W`, for `m + 1 = 2⁶⁴ m'` and `m' = 2ᵏ + 2¹²⁸ (2⁶⁴ − 2ᵏ + 1)`: the
window becomes `w₁, w₂, w₃, t` with the value `(W + t m) / 2⁶⁴`, as
`W + t m = W − t + 2⁶⁴ t m'`. `t 2ᵏ` (`rbp:rax`) by two shifts (cheaper than
a `mulx` on AMD's Zen cores) and `t (2⁶⁴ − 2ᵏ + 1)` (`t:rcx`) by `mulx`, and
added in one carry chain, which ends in the new top word `t`. -/
def redRoundX (k : Nat) (t w1 w2 w3 : Reg) : List Instr :=
  [.mov .rdx (.reg t), .mov .rax (.reg t), .shift .shl .rax k, .mov .rbp (.reg t), .shift .shr .rbp (64 - k),
    .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 64 - 2 ^ k + 1)), .mulx t .rcx (.reg .rcx),
    .alu .add w1 (.reg .rax), .alu .adc w2 (.reg .rbp), .alu .adc w3 (.reg .rcx), .alu .adc t (.imm 0)]

/-- `[o] = t R⁻¹ mod m` for the product `t = L + 2²⁵⁶ H` in `r8`–`r15` (below
`2²⁵⁶ m`), four words and `m' = 2ᵏ + 2¹²⁸ (2⁶⁴ − 2ᵏ + 1)` (P-256's `p`): four
rounds of `redRoundX` reduce the low half `L` in a window of four words that
rotates through `r8`–`r11`, which leaves `(L + U m) / 2²⁵⁶ ≤ m` there (for the
words `U` of the rounds); the high half `H < m` is added to it into
`r12`–`r15`, the carry into `r8`, and `csub` reduces the sum, below `2m`. -/
def redRX (M : Mod) (k o : Nat) : List Instr :=
  redRoundX k .r8 .r9 .r10 .r11 ++ redRoundX k .r9 .r10 .r11 .r8 ++ redRoundX k .r10 .r11 .r8 .r9 ++
    redRoundX k .r11 .r8 .r9 .r10 ++
    ([.alu .add .r12 (.reg .r8), .alu .adc .r13 (.reg .r9), .alu .adc .r14 (.reg .r10), .alu .adc .r15 (.reg .r11),
      .mov32 .r8 (.imm 0), .alu .adc .r8 (.imm 0)] : List Instr) ++ csub M sqLow .r8 ++ stores sqLow o

/-- `[o] = [a]² R⁻¹ mod m` with BMI2 and ADX: `a²` into `r8`–`r15` as X25519's
`sqrX` computes it, then `redRX`. -/
def sqrRX (M : Mod) (k o a : Nat) : List Instr :=
  Impl.X25519.X86_64.sqrA a ++ Impl.X25519.X86_64.sqrB a ++ Impl.X25519.X86_64.sqrC a ++
    Impl.X25519.X86_64.sqrD a ++ redRX M k o

/-- `[o] = [a] [b] R⁻¹ mod m` with BMI2 and ADX: `a b` into `r8`–`r15` by the
rows of X25519's `mulX` (`a_i [b]`), then `redRX`. -/
def mulRX (M : Mod) (k o a b : Nat) : List Instr :=
  Impl.X25519.X86_64.rowX0 b a ++ Impl.X25519.X86_64.rowX b a 1 ++ Impl.X25519.X86_64.rowX b a 2 ++
    Impl.X25519.X86_64.rowX b a 3 ++ redRX M k o

/-- `some k` if `mul o a b` is one that `mulRX` or `sqrRX` computes: four words,
BMI2 and ADX, and a friendly modulus whose `m'` is `shiftK?`'s. -/
def prodK? (M : Mod) : Option Nat :=
  if M.adx ∧ M.n = 4 then
    match M.red with
    | .friendly ws => shiftK? ws
    | .general => none
  else none

/-! ## P-384's squaring with BMI2 and ADX

`sqrS` computes `[a]²` in the registers the operations may change, and the
temporary area: the cross products `a_i a_j` (`i < j`) once, row by row (row 0
through CF, `accRow`, its two lowest words then stored at `[tmp + 8]`; rows 1
to 4 through OF and CF, `maddRow`, each row's top word fresh), then those
words doubled through CF and the squares `a_i²` added through OF
(`sqrDiag`), words 0 to 2 of the square into `[tmp]`. Then the high half goes
to `[o]` (the input is read by then), and six reductions of the low half by
`redShortX` in six words (`sqWin6`, where words 3 to 5 already are, rotating),
leave `(L + U p) / 2³⁸⁴ ≤ p`, to which the high half is added (`< 2p`) and
`csub` applied. -/

/-- `x :: rs = x + rdx · [d …]` through CF: each word's product, its low half
added to a register (with the carry), its high half into the next. -/
def accRow : List Reg → Nat → List Instr
  | x :: y :: rs, d => Impl.X25519.X86_64.mulAcc x y (.mem (sc d)) ++ accRow (y :: rs) (d + 8)
  | _, _ => []

/-- `x :: rs += rdx · [d …]`, the last register fresh: the low halves through
OF and the high halves through CF (`madd`), the last product's high half and
both carries into the last register (`maddLast`). -/
def maddRow : List Reg → Nat → List Instr
  | [x, y], d => Impl.X25519.X86_64.maddLast x y (.mem (sc d))
  | x :: y :: z :: rs, d => Impl.X25519.X86_64.madd x y (.mem (sc d)) ++ maddRow (y :: z :: rs) (d + 8)
  | _, _ => []

/-- Row 0 of the cross products of `[a]`: `r8–r13 = a₀ (a₁, …, a₅)`. -/
def sqrRow0 (a : Nat) : List Instr :=
  ([.mov .rdx (.mem (sc a)), Impl.X25519.X86_64.clear, .mulx .r9 .r8 (.mem (sc (a + 8)))] : List Instr) ++
    accRow [.r9, .r10, .r11, .r12, .r13] (a + 16) ++ ([.adcx .r13 (.reg .rbp)] : List Instr)

/-- `sqrRow0` without BMI2 and ADX: `r8–r12` cleared and `a₀ (a₁, …, a₅)`
added by `mulRow`, its carry word into `r13`. -/
def sqrRow0M (a : Nat) : List Instr :=
  ([.mov .rcx (.mem (sc a))] : List Instr) ++ zeros [.r8, .r9, .r10, .r11, .r12] ++ mulRow [.r8, .r9, .r10, .r11, .r12] (a + 8) ++
    ([.mov .r13 (.reg .rbp)] : List Instr)

/-- Row 0 of the cross products: `sqrRow0` with BMI2 and ADX (`x`), else
`sqrRow0M`. -/
def sqrRow0' (x : Bool) (a : Nat) : List Instr := if x then sqrRow0 a else sqrRow0M a

/-- A row of the cross products: `ts ++ [y] = ts + [d₀] · [d …]`, the last
register `y` fresh; with BMI2 and ADX (`x`) by `maddRow`, else by `mulRow`,
its carry word into `y`. -/
def crossRow (x : Bool) (d₀ : Nat) (ts : List Reg) (y : Reg) (d : Nat) : List Instr :=
  if x then ([.mov .rdx (.mem (sc d₀)), Impl.X25519.X86_64.clear] : List Instr) ++ maddRow (ts ++ [y]) d
  else ([.mov .rcx (.mem (sc d₀))] : List Instr) ++ mulRow ts d ++ ([.mov y (.reg .rbp)] : List Instr)

/-- Rows 1 to 4 of the cross products of `[a]`: row `i` adds `a_i (a_{i+1}, …)`
at the words `2i + 1` to `i + 6`, the last fresh (words 3 to 10 in `r10–r15`,
`r8`, `r9`). -/
def sqrRows (x : Bool) (a : Nat) : List Instr :=
  crossRow x (a + 8) [.r10, .r11, .r12, .r13] .r14 (a + 16) ++
    crossRow x (a + 16) [.r12, .r13, .r14] .r15 (a + 24) ++
    crossRow x (a + 24) [.r14, .r15] .r8 (a + 32) ++ crossRow x (a + 32) [.r8] .r9 (a + 40)

/-- The words `x`, `y` (`2i`, `2i + 1`) doubled through CF, and `a_i² = [d]²`
added through OF. -/
def sqrDiag (d : Nat) (x y : Reg) : List Instr :=
  ([.mov .rdx (.mem (sc d)), .mulx .rcx .rax (.reg .rdx)] : List Instr) ++ Impl.X25519.X86_64.dblAdd x .rax ++
    Impl.X25519.X86_64.dblAdd y .rcx

/-- `sqrDiag` along the pairs of words `ps`, by the words of `[d …]`. -/
def sqrDiags : List (Reg × Reg) → Nat → List Instr
  | [], _ => []
  | (x, y) :: ps, d => sqrDiag d x y ++ sqrDiags ps (d + 8)

/-- The cross products doubled and the squares added, words 0 to 2 (`[tmp + 8]`
and `[tmp + 16]` doubled, through `rdx`) into `[tmp]`: `w₀` (`rbp`) is cleared
with the flags, and the last high half and carries make `w₁₁` (`rcx`). -/
def sqrDbl (t a : Nat) : List Instr :=
  [Impl.X25519.X86_64.clear, .mov .rdx (.mem (sc a)), .mulx .rcx .rax (.reg .rdx)] ++
    Impl.X25519.X86_64.dblAdd .rbp .rax ++
    ([.store (sc t) .rbp, .mov .rdx (.mem (sc (t + 8)))] : List Instr) ++ Impl.X25519.X86_64.dblAdd .rdx .rcx ++
    ([.store (sc (t + 8)) .rdx, .mov .rdx (.mem (sc (a + 8))), .mulx .rcx .rax (.reg .rdx),
      .mov .rdx (.mem (sc (t + 16)))] : List Instr) ++ Impl.X25519.X86_64.dblAdd .rdx .rax ++
    ([.store (sc (t + 16)) .rdx] : List Instr) ++ Impl.X25519.X86_64.dblAdd .r10 .rcx ++
    sqrDiags [(.r11, .r12), (.r13, .r14), (.r15, .r8)] (a + 16) ++
    ([.mov .rdx (.mem (sc (a + 40))), .mulx .rcx .rax (.reg .rdx)] : List Instr) ++
    Impl.X25519.X86_64.dblAdd .r9 .rax ++
    ([.mov32 .rdx (.imm 0), .adcx .rcx (.reg .rdx), .adox .rcx (.reg .rdx)] : List Instr)

/-- `ts += ts`: each register added to itself, with `op` on the first and
`adc` on the rest, which doubles the number in them. -/
def dblChain (op : AluOp) : List Reg → List Instr
  | [] => []
  | t :: ts => .alu op t (.reg t) :: dblChain .adc ts

/-- A square added at two words without BMI2 and ADX: `[d]²` plus the
carry word `rbp` (which never overflows its high half) added at `lo`, `hi`,
the carry out into `rbp`. -/
def sqStepM (d : Nat) (lo hi : Reg) : List Instr :=
  [.mov .rax (.mem (sc d)), .mul .rax, .alu .add .rax (.reg .rbp), .alu .adc .rdx (.imm 0),
    .alu .add lo (.reg .rax), .alu .adc hi (.reg .rdx), .mov32 .rbp (.imm 0), .alu .adc .rbp (.imm 0)]

/-- The cross products doubled in one carry chain without BMI2 and ADX: words 1
and 2 at `[t + 8]` through `rax`, words 3 to 10 in registers, the carry out
into `rcx` (word 11). -/
def dblHalfM (t : Nat) : List Instr :=
  ([.mov .rax (.mem (sc (t + 8))), .alu .add .rax (.reg .rax), .store (sc (t + 8)) .rax,
    .mov .rax (.mem (sc (t + 16))), .alu .adc .rax (.reg .rax), .store (sc (t + 16)) .rax] : List Instr) ++
  dblChain .adc [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] ++ ([.mov32 .rcx (.imm 0), .alu .adc .rcx (.reg .rcx)] : List Instr)

/-- `a₀²` and `a₁²` added at words 0 to 3 (words 0 to 2 at `[t]`, word 3 in
`r10`) without BMI2 and ADX, the carry word out in `rbp`. -/
def sq01M (t a : Nat) : List Instr :=
  [.mov .rax (.mem (sc a)), .mul .rax, .store (sc t) .rax, .alu .add .rdx (.mem (sc (t + 8))),
    .store (sc (t + 8)) .rdx, .mov32 .rbp (.imm 0), .alu .adc .rbp (.imm 0),
    .mov .rax (.mem (sc (a + 8))), .mul .rax, .alu .add .rax (.reg .rbp), .alu .adc .rdx (.imm 0),
    .alu .add .rax (.mem (sc (t + 16))), .store (sc (t + 16)) .rax, .alu .adc .r10 (.reg .rdx),
    .mov32 .rbp (.imm 0), .alu .adc .rbp (.imm 0)]

/-- `a₂²` to `a₅²` added at words 4 to 11 by `sqStepM`. -/
def sqStepsM (a : Nat) : List Instr :=
  sqStepM (a + 16) .r11 .r12 ++ sqStepM (a + 24) .r13 .r14 ++ sqStepM (a + 32) .r15 .r8 ++
    sqStepM (a + 40) .r9 .rcx

/-- `sqrDbl` without BMI2 and ADX: the cross products doubled in one carry
chain (words 1 and 2 at `[t + 8]` through `rax`, the carry out into `rcx`,
word 11), then the squares `a_i²` added at words `2i`, `2i + 1`, each with
the carry word of the one before (`sqStepM`; words 0 to 2 at `[t]`). -/
def sqrDblM (t a : Nat) : List Instr := dblHalfM t ++ sq01M t a ++ sqStepsM a

/-- The cross products doubled and the squares added: `sqrDbl` with BMI2
and ADX (`x`), else `sqrDblM`. -/
def sqrDbl' (x : Bool) (t a : Nat) : List Instr := if x then sqrDbl t a else sqrDblM t a

/-- The registers of the square's high half, words 6 to 11. -/
def sqHigh6 : List Reg := [.r13, .r14, .r15, .r8, .r9, .rcx]

/-- The window of `sqrS`'s reductions: the square's words 0 to 2 (from
`[tmp]`) and 3 to 5. -/
def sqWin6 : List Reg := [.r13, .r14, .r15, .r10, .r11, .r12]

/-- Word `j` of the window of round `i`: `sqWin6` rotated by one word each
round (six bring it back). -/
def sqW (i j : Nat) : Reg := sqWin6.getD ((i + j) % 6) .r13

/-- The window of round `i`. -/
def sqWins (i : Nat) : List Reg := (List.range 6).map (sqW i)

/-- `k` rounds of `redShort` from the window `sqWin6`. -/
def redsShort (x : Bool) (k : Nat) : List Instr := (List.range k).flatMap fun i => redShort x (sqWins i)

/-- `sqrS` but its final reduction: the square, its high half stored at `[o]`,
the low half reduced by six rounds of `redShort` and the high half added, into
`sqWin6` and its carry into `r8`. -/
def sqrSA (M : Mod) (o a : Nat) : List Instr :=
  sqrRow0' M.adx a ++ stores [.r8, .r9] (M.tmp + 8) ++ sqrRows M.adx a ++ sqrDbl' M.adx M.tmp a ++
    stores sqHigh6 o ++ loads [.r13, .r14, .r15] M.tmp ++ redsShort M.adx 6 ++ ([.mov32 .r8 (.imm 0)] : List Instr) ++
    chain .add .adc sqWin6 o ++ ([.alu .adc .r8 (.imm 0)] : List Instr)

/-- `[o] = [a]² R⁻¹ mod p` for P-384's `p`, with BMI2 and ADX or without (the
parts chosen by `M.adx`): the square's words 0 to 2 at `[tmp]` and 3 to 11 in
`r10–r15`, `r8`, `r9`, `rcx`; its high half stored at `[o]`, the low half into
the six words `sqWin6` and reduced by six rounds of `redShort`, the high half
added (its carry into `r8`), and `csub`. -/
def sqrS (M : Mod) (o a : Nat) : List Instr :=
  sqrSA M o a ++ csub M sqWin6 .r8 ++ stores sqWin6 o

/-- `r8 … r14 = rdx · [b]` in one carry chain (`r15 = 0`), with no
accumulator to clear or add to. -/
def rowS0 (b : Nat) : List Instr :=
  [Impl.X25519.X86_64.clear, .mulx .r9 .r8 (.mem (sc b))] ++
    accRow [.r9, .r10, .r11, .r12, .r13, .r14] (b + 8) ++ ([.adcx .r14 (.reg .rbp), .mov32 .r15 (.imm 0)] : List Instr)

/-- Row 0 of P-384's multiplication with BMI2 and ADX: `r8 … r14 = a₀ [b]`
by `rowS0`. -/
def mulRowS0 (a b : Nat) : List Instr := .mov .rdx (.mem (sc a)) :: rowS0 b

/-- The rounds of `mul o a b` with the accumulator in registers: the
accumulator cleared and the rounds `0 … n-1`; for P-384's `p` with BMI2 and
ADX, row 0 by `mulRowS0` and its reduction, then the rounds `1 … 5`. -/
def mulRounds (M : Mod) (a b : Nat) : List Instr :=
  if M.adx ∧ M.sparse ∧ M.n = 6 then
    mulRowS0 a b ++ redSparseX (wins 6 0) ++ (List.range 5).flatMap (fun i => round M a b (i + 1))
  else zeros (acc M.n) ++ (List.range M.n).flatMap (round M a b)

/-- `[o] = [a] [b] R⁻¹ mod m` by the rounds of `mulRounds`, then `csub`, the
result stored. (A function of its own, deciding nothing on the offsets, so
that the code of every product is one template: `materialize_template`.) -/
def mulG (M : Mod) (o a b : Nat) : List Instr :=
  let low := (List.range M.n).map (win M.n M.n)
  mulRounds M a b ++ csub M low (win M.n M.n M.n) ++ stores low o

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`), the accumulator in
registers; by `sqrRX`, `mulRX` or (P-384's square) `sqrS` if they apply,
else `mulG`. -/
def mulR (M : Mod) (o a b : Nat) : List Instr :=
  match prodK? M with
  | some k => if a = b then sqrRX M k o a else mulRX M k o a b
  | none => if M.sparse ∧ M.n = 6 ∧ a = b then sqrS M o a else mulG M o a b


/-- The low words and the top word of the sums and differences. -/
def low (n : Nat) : List Reg := (acc n).take n
def top (n : Nat) : Reg := (acc n).getD n .r8

/-- `[o] = [a] + [b] mod m`, in registers. -/
def addR (M : Mod) (o a b : Nat) : List Instr :=
  loads (low M.n) a ++ ([.mov32 (top M.n) (.imm 0)] : List Instr) ++ chain .add .adc (low M.n) b ++
    ([.alu .adc (top M.n) (.imm 0)] : List Instr) ++ csub M (low M.n) (top M.n) ++ stores (low M.n) o

/-- `[tmp] = [mo]` masked with `rax`, `n` words. -/
def masked : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, mo, tmp => ([.mov .rdx (.mem (sc mo)), .alu .and .rdx (.reg .rax),
      .store (sc tmp) .rdx] : List Instr) ++ masked k (mo + 8) (tmp + 8)

/-- `[o] = [a] - [b] mod m`: the difference, and `m` added under the mask
`rax` of its borrow (through `[tmp]`), in registers. -/
def subR (M : Mod) (o a b : Nat) : List Instr :=
  loads (low M.n) a ++ chain .sub .sbb (low M.n) b ++ ([.alu .sbb .rax (.reg .rax)] : List Instr) ++
    masked M.n M.mo M.tmp ++ chain .add .adc (low M.n) M.tmp ++ stores (low M.n) o


/-- The four words of `(p + 1) / 2⁶⁴` for P-256. -/
def p256Ws : List MWord :=
  [.pow2 32, .zero, .gen 0xffffffff00000001, .zero]

/-- P-256 masked by the borrow in `rax`: its nonzero words in `rax`, `rcx`, `rdx`. -/
def p256SubMask : List Instr :=
  [.mov32 .rcx (.reg .rax),
   .movImm64 .rdx 0xffffffff00000001, .alu .and .rdx (.reg .rax)]

/-- Add the masked modulus to the difference in `r8`–`r11`. -/
def p256SubAdd : List Instr :=
  [.alu .add .r8 (.reg .rax), .alu .adc .r9 (.reg .rcx),
   .alu .adc .r10 (.imm 0), .alu .adc .r11 (.reg .rdx)]

/-- `[o] = [a] - [b] mod p` for P-256, without a temporary-memory round trip. -/
def sub256 (o a b : Nat) : List Instr :=
  loads (low 4) a ++ chain .sub .sbb (low 4) b ++ ([.alu .sbb .rax (.reg .rax)] : List Instr) ++
    p256SubMask ++ p256SubAdd ++ stores (low 4) o

/-! ## More than six words: the accumulator in the temporary area -/

/-- `[t] = [t] + rcx · src + rbp` and its carry word in `rbp`, through `r8`. -/
def memStep (t : Nat) (src : Src) : List Instr :=
  .mov .r8 (.mem (sc t)) :: mulStep .r8 .rbp .rcx src ++ ([.store (sc t) .r8] : List Instr)

/-- `k` words at `t`, `t + 8`, … `+= rcx · [d]`, …, the carry word in `rbp`. -/
def memSteps : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, t, d => memStep t (.mem (sc d)) ++ memSteps k (t + 8) (d + 8)

/-- `[t] += rcx · [d]` (`k` words), its carry word in `rbp`. -/
def memRow (k t d : Nat) : List Instr := .mov32 .rbp (.imm 0) :: memSteps k t d

/-- `[t] = [t + 8]`, …: `k` words moved down by one word, through `r8`. -/
def moveDown : Nat → Nat → List Instr
  | 0, _ => []
  | k + 1, t => ([.mov .r8 (.mem (sc (t + 8))), .store (sc t) .r8] : List Instr) ++ moveDown k (t + 8)

/-- The accumulator divided by `2⁶⁴` (its low word is zero): its words moved
down, `r9` stored on top, and `r10` moved into `r9`. -/
def shiftDown (M : Mod) : List Instr :=
  moveDown (M.n - 1) M.tmp ++ ([.store (sc (M.tmp + 8 * (M.n - 1))) .r9, .mov .r9 (.reg .r10),
    .mov32 .r10 (.imm 0)] : List Instr)

/-- Round `i` of `mulW o a b`: `T += a_i [b]`, then `T += u m` with
`u = t₀ m' mod 2⁶⁴`, after which `t₀ = 0`, and `T /= 2⁶⁴`. -/
def roundW (M : Mod) (a b i : Nat) : List Instr :=
  ([.mov .rcx (.mem (sc (a + 8 * i)))] : List Instr) ++ memRow M.n M.tmp b ++ carryUp .r9 .r10 ++
  ([.mov .r8 (.mem (sc M.tmp)), .mov .rax (.reg .r8), .movImm64 .rcx M.minv, .mul .rcx,
    .mov .rcx (.reg .rax)] : List Instr) ++
    memRow M.n M.tmp M.mo ++ carryUp .r9 .r10 ++ shiftDown M

/-- `k` words of zeros at `t`, through `r8`. -/
def zeroWords (k t : Nat) : List Instr :=
  .mov32 .r8 (.imm 0) :: (List.range k).map fun j => .store (sc (t + 8 * j)) .r8

/-- `[t] = [a] op [b]`, word by word, with `op` on the first word and `op'`
on the others, through `r8`. -/
def chainW (op op' : AluOp) : Nat → Nat → Nat → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, t, a, b => ([.mov .r8 (.mem (sc a)), .alu op .r8 (.mem (sc b)), .store (sc t) .r8] : List Instr) ++
    chainW op' op' k (t + 8) (a + 8) (b + 8)

/-- `[o] = [x]` where the mask `rax` is all zeros (`[o]` kept where it is all
ones), word by word. -/
def selectsW : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, x, o => ([.mov .rdx (.mem (sc o)), .mov .r8 (.mem (sc x)), .alu .xor .rdx (.reg .r8),
      .alu .and .rdx (.reg .rax), .alu .xor .rdx (.reg .r8), .store (sc o) .rdx] : List Instr) ++
      selectsW k (x + 8) (o + 8)

/-- `[o] = T mod m` for `T = [tmp] + 2^(64 n) r9 < 2m`: the difference with
`m` into `[o]`, and `[tmp]` selected instead if it borrowed. -/
def csubW (M : Mod) (o : Nat) : List Instr :=
  chainW .sub .sbb M.n o M.tmp M.mo ++
  ([.mov .rax (.reg .r9), .alu .sbb .rax (.imm 0), .alu .sbb .rax (.reg .rax),
    .alu .xor .rax (.imm (-1))] : List Instr) ++
  selectsW M.n M.tmp o

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`), the accumulator in
`[tmp]`, `r9` and `r10`. -/
def mulW (M : Mod) (o a b : Nat) : List Instr :=
  zeroWords M.n M.tmp ++ ([.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0)] : List Instr) ++
    (List.range M.n).flatMap (roundW M a b) ++ csubW M o

/-- `[o] = [a] + [b] mod m`, the sum in `[tmp]` and `r9`. -/
def addW (M : Mod) (o a b : Nat) : List Instr :=
  ([.mov32 .r9 (.imm 0)] : List Instr) ++ chainW .add .adc M.n M.tmp a b ++ ([.alu .adc .r9 (.imm 0)] : List Instr) ++ csubW M o

/-- `[o] = [a] - [b] mod m`: the difference in `[tmp]`, then `m` masked with
the borrow into `[o]`, and their sum into `[o]`. -/
def subW (M : Mod) (o a b : Nat) : List Instr :=
  chainW .sub .sbb M.n M.tmp a b ++ ([.alu .sbb .rax (.reg .rax)] : List Instr) ++ masked M.n M.mo o ++
    chainW .add .adc M.n o M.tmp o

/-! ## P-521's modulus: the product by columns -/

/-- The words of `(p + 1) / 2⁶⁴ = 2⁴⁵⁷` for P-521's `p = 2⁵²¹ - 1`, its friendly
reduction (`Red.ofModulus 9 p`). -/
def p521Ws : List MWord := [.zero, .zero, .zero, .zero, .zero, .zero, .zero, .pow2 9, .zero]

/-- The accumulator's registers in column `c` of `mulP`: they rotate, the low
word of one column becoming the top word of the next once stored. -/
def pAcc (c k : Nat) : Reg := [Reg.r9, .r10, .r11].getD ((c + k) % 3) .r9

/-- A term's second factor: the word at `d` (`some d`), or 512. -/
def pSrc : Option Nat → Src
  | some d => .mem (sc d)
  | none => .imm 512

/-- `[dx] · y` added to the accumulator of column `c`, `y` (`pSrc dy`) into
`rcx` and `[dx]` into `rax`. -/
def pTerm (c dx : Nat) (dy : Option Nat) : List Instr :=
  [.mov .rcx (pSrc dy), .mov .rax (.mem (sc dx)),
    .mul .rcx, .alu .add (pAcc c 0) (.reg .rax), .alu .adc (pAcc c 1) (.reg .rdx),
    .alu .adc (pAcc c 2) (.imm 0)]

/-- The terms of column `c` of `mulP o a b`: the products `[a + 8i] [b + 8j]`
with `i + j = c`, and for `8 ≤ c ≤ 16` the reduction's `512 u_{c-8}`, with
`u_{c-8}` in the temporary area. -/
def pTerms (M : Mod) (a b c : Nat) : List (Nat × Option Nat) :=
  ((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map (fun i => (a + 8 * i, some (b + 8 * (c - i)))) ++
    if 8 ≤ c ∧ c ≤ 16 then [(M.tmp + 8 * (c - 8), none)] else []

/-- Column `c` of `mulP o a b`: its terms, then its low word stored at
`[tmp + 8 (c mod 9)]` and cleared. -/
def pCol (M : Mod) (a b c : Nat) : List Instr :=
  (pTerms M a b c).flatMap (fun t => pTerm c t.1 t.2) ++
    ([.store (sc (M.tmp + 8 * (c % 9))) (pAcc c 0), .mov32 (pAcc c 0) (.imm 0)] : List Instr)

/-- A Montgomery multiplication by columns into `[o]`: the accumulator
`r9`–`r11` cleared, the eighteen columns `col c`, then `csubW`. -/
def prodCols (M : Mod) (o : Nat) (col : Nat → List Instr) : List Instr :=
  ([.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0)] : List Instr) ++ (List.range 18).flatMap col ++ csubW M o

/-- `[o] = [a] [b] R⁻¹ mod p` for P-521's `p = 2⁵²¹ - 1` (`o` may be `a` or
`b`), by Montgomery multiplication in product scanning: column `c` sums the
products `a_i b_j` with `i + j = c` in three registers (`pAcc`). As
`p ≡ -1 (mod 2⁶⁴)`, the reduction's `u_k` is the low word of column `k`
(`k ≤ 8`), stored at `[tmp + 8k]`, and adding `u_k p = 2^(521 + 64k) u_k - u_k`
clears it and adds `2⁹ u_k = 512 u_k` to column `k + 8`. Columns 9 to 17 are
the result, `(a b + U p) / 2⁵⁷⁶ < 2p`, stored over the `u`s no longer needed
(column `c` at `[tmp + 8 (c - 9)]`), with its top word in `r9`; `csubW`
reduces it into `[o]`. -/
def mulP (M : Mod) (o a b : Nat) : List Instr := prodCols M o (pCol M a b)

/-- A squaring's term `[dx] · y`, added twice if `two`: the product's
`rdx:rax` added again. -/
def sTerm (c dx : Nat) (dy : Option Nat) (two : Bool) : List Instr :=
  pTerm c dx dy ++ if two then [.alu .add (pAcc c 0) (.reg .rax), .alu .adc (pAcc c 1) (.reg .rdx),
    .alu .adc (pAcc c 2) (.imm 0)] else []

/-- The terms of column `c` of `sqrP o a`: the products `[a + 8i] [a + 8j]`
with `i < j`, `i + j = c`, twice, the square `[a + 4c]²` for even `c`, and
for `8 ≤ c ≤ 16` the reduction's `512 u_{c-8}`. -/
def sTerms (M : Mod) (a c : Nat) : List (Nat × Option Nat × Bool) :=
  ((List.range 9).filter fun i => 2 * i < c ∧ c - i < 9).map (fun i => (a + 8 * i, some (a + 8 * (c - i)), true)) ++
    (if c % 2 = 0 ∧ c / 2 < 9 then [(a + 8 * (c / 2), some (a + 8 * (c / 2)), false)] else []) ++
    if 8 ≤ c ∧ c ≤ 16 then [(M.tmp + 8 * (c - 8), none, false)] else []

/-- Column `c` of `sqrP o a`: its terms, then its low word stored at
`[tmp + 8 (c mod 9)]` and cleared. -/
def sCol (M : Mod) (a c : Nat) : List Instr :=
  (sTerms M a c).flatMap (fun t => sTerm c t.1 t.2.1 t.2.2) ++
    ([.store (sc (M.tmp + 8 * (c % 9))) (pAcc c 0), .mov32 (pAcc c 0) (.imm 0)] : List Instr)

/-- `[o] = [a]² R⁻¹ mod p` for P-521's `p`: `mulP o a a`, but each product
of two different words computed once and added twice (`sTerm`), 45
products in place of 81. -/
def sqrP (M : Mod) (o a : Nat) : List Instr := prodCols M o (sCol M a)

/-! ## P-521's modulus with BMI2 and ADX: the product by rows -/

/-- `[rdi + d - c]`: the word at `d` in the working space while `rdi` is
`c` bytes past its base, which `mulPX` and `sqrPX` move to their operand so
that its words are at displacements of a byte. -/
def rc (c d : Nat) : MemOp := { base := .rdi, disp := (d : Int) - c }

/-- `[r + d - c]`: `rc` through the register `r`, `c` bytes past the base of
the memory the operand is in. The products read their operands through
`rdi` inline, and through the registers their pointers are passed in when
called (`a` in `rsi`, `b` in `rbx`). -/
def rcR (r : Reg) (c d : Nat) : MemOp := { base := r, disp := (d : Int) - c }

/-- How far `mulPX` and `sqrPX` move `rdi`: to the operand at `d`, if that
is within an immediate's reach. -/
def cOf (d : Nat) : Nat := if d < 2 ^ 31 then d else 0

/-- `rdi += c` and `rdi -= c`. -/
def rdiAdd (c : Nat) : Instr := .alu .add .rdi (.imm (BitVec.ofNat 32 c))
def rdiSub (c : Nat) : Instr := .alu .sub .rdi (.imm (BitVec.ofNat 32 c))

/-- `rdi` from `c` to `c'` bytes past its base. -/
def rdiMove (c c' : Nat) : Instr := .alu .add .rdi (.imm (BitVec.ofInt 32 ((c' : Int) - c)))

/-- `stores` while `rdi` is `c` bytes past its base (`rc`). -/
def storesC (c : Nat) : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, o => .store (rc c o) t :: storesC c ts (o + 8)

/-- `maddSteps` reading through `r`, `c` bytes past its base (`rcR`). -/
def maddStepsC (r : Reg) (c : Nat) : Nat → List Reg → Nat → List Instr
  | k + 1, x :: y :: rest, d => madd x y (.mem (rcR r c d)) ++ maddStepsC r c k (y :: rest) (d + 8)
  | _, _, _ => []

/-- `loads` and `chain` while `rdi` is `c` bytes past its base (`rc`). -/
def loadsC (c : Nat) : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, a => .mov t (.mem (rc c a)) :: loadsC c ts (a + 8)

def chainC (c : Nat) (op op' : AluOp) : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, b => .alu op t (.mem (rc c b)) :: chainC c op' op' ts (b + 8)

/-- The registers of `mulPX`'s accumulator. -/
def xRegs : List Reg := [.rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The register of word `k` of `mulPX`'s accumulator: the nine words of a
row's accumulator are in distinct registers, word `k + 9` taking the
register of word `k` once that is stored. -/
def xAcc (k : Nat) : Reg := xRegs.getD (k % 9) .rbp

/-- The nine registers of words `k` to `k + 8`. -/
def xWin (k : Nat) : List Reg := (List.range 9).map fun j => xAcc (k + j)

/-- `mov eax, 0`, `adox t, rax`: the carry OF added into `t`. -/
def xTail (t : Reg) : List Instr := [.mov32 .rax (.imm 0), .adox t (.reg .rax)]

/-- Row `i` of `mulPX o a b`: `rdx = a_i`, both carries cleared
(`xor eax, eax`), `t += a_i [b]` with the first product's word `i` stored at
`[tmp + 8i]` once final and its register cleared for word `i + 9`, then the
eight other products (`maddSteps`), and the carry OF into word `i + 9`. -/
def xRow (M : Mod) (ra rb : Reg) (c a b i : Nat) : List Instr :=
  ([.mov .rdx (.mem (rcR ra c (a + 8 * i))), .alu32 .xor .rax (.reg .rax)] : List Instr) ++
    madd (xAcc i) (xAcc (i + 1)) (.mem (rcR rb c b)) ++
    ([.store (rc c (M.tmp + 8 * i)) (xAcc i), .mov32 (xAcc i) (.imm 0)] : List Instr) ++
    maddStepsC rb c 8 (xWin (i + 1)) (b + 8) ++ xTail (xAcc (i + 9))

/-- `xRow` but its first instruction: the row once `rdx = a_i`. -/
def xRowR (M : Mod) (rb : Reg) (c b i : Nat) : List Instr :=
  ([.alu32 .xor .rax (.reg .rax)] : List Instr) ++
    madd (xAcc i) (xAcc (i + 1)) (.mem (rcR rb c b)) ++
    ([.store (rc c (M.tmp + 8 * i)) (xAcc i), .mov32 (xAcc i) (.imm 0)] : List Instr) ++
    maddStepsC rb c 8 (xWin (i + 1)) (b + 8) ++ xTail (xAcc (i + 9))

/-- `k` products `rdx · [d]`, `rdx · [d + 8]`, … into the words `j … j + k`
of the accumulator (`xAcc`), whatever those held but word `j`: each
product's high half into the next word (`mulx`), its low half added through
CF (`adcx`). -/
def mulAccs (r : Reg) (c : Nat) : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, j, d => ([.mulx (xAcc (j + 1)) .rax (.mem (rcR r c d)), .adcx (xAcc j) (.reg .rax)] : List Instr) ++
      mulAccs r c k (j + 1) (d + 8)

/-- Row 0 of `mulPX o a b`, before the accumulator holds anything: `rdx = a_0`,
CF cleared (`xor eax, eax`), `a_0 b_0`'s low half stored at `[tmp]` and its
high half into word 1, the eight other products (`mulAccs`), and the carry
CF into word 9. -/
def xRow0 (M : Mod) (ra rb : Reg) (c a b : Nat) : List Instr :=
  ([.mov .rdx (.mem (rcR ra c a)), .alu32 .xor .rax (.reg .rax), .mulx (xAcc 1) .rax (.mem (rcR rb c b)),
    .store (rc c M.tmp) .rax] : List Instr) ++ mulAccs rb c 8 1 (b + 8) ++ ([.alu .adc (xAcc 9) (.imm 0)] : List Instr)

/-- Row `i` of `mulPX o a b`: `xRow0` for the first, else `xRow`. -/
def xRowV (M : Mod) (ra rb : Reg) (c a b i : Nat) : List Instr :=
  if i = 0 then xRow0 M ra rb c a b else xRow M ra rb c a b i

/-- CF set and OF clear: `xor eax, eax`, then `cmp rax, -1` (`0 < 2⁶⁴ - 1`,
without signed overflow), for a sum with a carry of one in. -/
def setCF : List Instr := [.alu32 .xor .rax (.reg .rax), .alu .cmp .rax (.imm (-1))]

/-- The reduction of `mulPX`, for `P = a b` with its low words `P₀ … P₈` at
`[tmp]` and its high words in `xWin 9`: `(P + U p) / 2⁵⁷⁶ + 1` for
`U = P₀ … P₇, u₈` with `u₈ = P₈ + 512 P₀ mod 2⁶⁴` (stored over `P₈`), as
`U p = 2⁵²¹ U - U`: `512 U` added at word 8 (`rdx = 512`), the low words
cancelling, and the one (`xCanon`'s) as the carry CF into word 9 (`setCF`). -/
def xRed (M : Mod) (c : Nat) : List Instr :=
  ([.mov32 .rdx (.imm 512)] : List Instr) ++ setCF ++ ([.mulx .rcx .rax (.mem (rc c M.tmp)),
    .adox .rax (.mem (rc c (M.tmp + 64))), .store (rc c (M.tmp + 64)) .rax, .adcx (xAcc 9) (.reg .rcx)] : List Instr) ++
    maddStepsC .rdi c 8 (xWin 9) (M.tmp + 8) ++ xTail (xAcc 17)

/-- `xWin 9`, `S + 1` for a number `S < 2p` for P-521's `p = 2⁵²¹ - 1`, as
its producer leaves it, `S` reduced and stored at `[o]`: bit 521 `c` of
`S + 1` (in `rax`) is whether `S ≥ p`; `1 - c` subtracted leaves `S + c`, and
its bits from 521 cleared: `S - p` if `S ≥ p`, else `S`. -/
def xCanon (c o : Nat) : List Instr :=
    ([.mov .rax (.reg (xAcc 17)), .shift .shr .rax 9, .alu .xor .rax (.imm 1),
      .alu .sub (xAcc 9) (.reg .rax)] : List Instr) ++
    (List.range 8).map (fun k => .alu .sbb (xAcc (10 + k)) (.imm 0)) ++
    ([.alu .and (xAcc 17) (.imm 511)] : List Instr) ++ storesC c (xWin 9) o

/-- `[o] = [a] [b] R⁻¹ mod p` for P-521's `p = 2⁵²¹ - 1` (`o` may be `a` or
`b`), with BMI2 and ADX: the product `a b` by rows (operand scanning,
`xRowV`): the first's products into nine registers through one carry chain
(`xRow0`), each later one's added through the two (`adox`, `adcx`, `xRow`),
each row's low word stored in the temporary area; then the reduction (`xRed`), which leaves `(a b + U p) / 2⁵⁷⁶ < 2p`, plus
one, in the registers; then `xCanon`, which reduces it below `p` into `[o]`.
The rows run with `rdi` moved to `[b]` (`rc`), whose words their 81 `mulx`
read at displacements of a byte: the code is bound by its decoding, and
each is three bytes shorter. -/
def mulPX (M : Mod) (o a b : Nat) : List Instr :=
  [rdiAdd (cOf b)] ++ (List.range 9).flatMap (xRowV M .rdi .rdi (cOf b) a b) ++ [rdiMove (cOf b) (cOf M.tmp)] ++
    xRed M (cOf M.tmp) ++ [rdiMove (cOf M.tmp) (cOf o)] ++ xCanon (cOf o) o ++ [rdiSub (cOf o)]

/-! ## P-521's modulus with BMI2 and ADX: the square

The products of two different words by rows (`sRow`, 36 products), doubled
and the squares added in one pass (`sDiag`: CF doubles, OF adds), then
`mulPX`'s reduction and final reduction. -/

/-- The registers of row `i < 8` of `sqrPX`'s products: words `2i + 1 … i + 9`. -/
def sWin (i : Nat) : List Reg := (List.range (9 - i)).map fun j => xAcc (2 * i + 1 + j)

/-- Row `i < 8` of `sqrPX`'s products of two different words: word `i`, final,
stored at `[tmp + 8i]` and its register cleared for word `i + 9`; `rdx = a_i`,
both carries cleared, `t += a_i [a + 8 (i + 1)]` (`8 - i` products into words
`2i + 1 … i + 9`), and the carry OF into word `i + 9`. -/
def sRow (M : Mod) (ra : Reg) (c a i : Nat) : List Instr :=
  ([.store (rc c (M.tmp + 8 * i)) (xAcc i), .mov32 (xAcc i) (.imm 0), .mov .rdx (.mem (rcR ra c (a + 8 * i))),
    .alu32 .xor .rax (.reg .rax)] : List Instr) ++ maddStepsC ra c (8 - i) (sWin i) (a + 8 * (i + 1)) ++ xTail (xAcc (i + 9))

/-- Row 0 of `sqrPX`'s products of two different words, before the
accumulator holds anything: word 0, zero, stored at `[tmp]` (from `rax`,
cleared with CF), `rdx = a_0`, `a_0 a_1` into words 1 and 2, the seven other
products (`mulAccs`), and the carry CF into word 9. -/
def sRow0 (M : Mod) (ra : Reg) (c a : Nat) : List Instr :=
  ([.alu32 .xor .rax (.reg .rax), .store (rc c M.tmp) .rax, .mov .rdx (.mem (rcR ra c a)),
    .mulx (xAcc 2) (xAcc 1) (.mem (rcR ra c (a + 8)))] : List Instr) ++ mulAccs ra c 7 2 (a + 16) ++
    ([.alu .adc (xAcc 9) (.imm 0)] : List Instr)

/-- Row `i` of `sqrPX`'s products: `sRow0` for the first, else `sRow`. -/
def sRowV (M : Mod) (ra : Reg) (c a i : Nat) : List Instr := if i = 0 then sRow0 M ra c a else sRow M ra c a i

/-- Word `w` of the square: `t_w = 2 t_w + d` (`adcx t, t`, `adox t, d`), in
the temporary area for `w ≤ 8` (through `rdx`), else in its register. -/
def sDbl (M : Mod) (c w : Nat) (d : Reg) : List Instr :=
  if w ≤ 8 then
    [.mov .rdx (.mem (rc c (M.tmp + 8 * w))), .adcx .rdx (.reg .rdx), .adox .rdx (.reg d),
      .store (rc c (M.tmp + 8 * w)) .rdx]
  else [.adcx (xAcc w) (.reg (xAcc w)), .adox (xAcc w) (.reg d)]

/-- Step `k` of the squares: `a_k²` into `rcx:rax`, added to words `2k` and
`2k + 1` of twice the products (CF doubles, OF adds). -/
def sDiagK (M : Mod) (ra : Reg) (c a k : Nat) : List Instr :=
  ([.mov .rdx (.mem (rcR ra c (a + 8 * k))), .mulx .rcx .rax (.reg .rdx)] : List Instr) ++ sDbl M c (2 * k) .rax ++
    sDbl M c (2 * k + 1) .rcx

/-- Word 8 stored and its register cleared for word 17, both carries cleared,
then the squares. -/
def sDiag (M : Mod) (ra : Reg) (c a : Nat) : List Instr :=
  ([.store (rc c (M.tmp + 64)) (xAcc 8), .mov32 (xAcc 17) (.imm 0), .alu32 .xor .rax (.reg .rax)] : List Instr) ++
    (List.range 9).flatMap (sDiagK M ra c a)

/-- `[o] = [a]² R⁻¹ mod p` for P-521's `p`, with BMI2 and ADX: the products
of two different words by rows (`sRowV`), doubled and the squares added
(`sDiag`), then `mulPX`'s reduction and final reduction. The products and
the squares run with `rdi` moved to `[a]` (`rc`), as in `mulPX`. -/
def sqrPX (M : Mod) (o a : Nat) : List Instr :=
  [rdiAdd (cOf a)] ++ (List.range 8).flatMap (sRowV M .rdi (cOf a) a) ++ sDiag M .rdi (cOf a) a ++
    [rdiMove (cOf a) (cOf M.tmp)] ++ xRed M (cOf M.tmp) ++ [rdiMove (cOf M.tmp) (cOf o)] ++
    xCanon (cOf o) o ++ [rdiSub (cOf o)]

/-! ## P-521's modulus: the sum and the difference in registers

As `p = 2⁵²¹ - 1`, the sum or difference below `2p` is reduced in place by
`xCanon` (no load of `p`, no temporary area), from the sum or difference
plus one: `[a] + [b] + 1` with a carry in, and `[a] - [b] + 2⁵²¹`, which is
`[a] + (p - [b]) + 1`. Each moves `rdi` to the operand it reads or writes
next (`rc`), so that its nine words are at displacements of a byte. -/

/-- `[o] = [a] + [b] mod p` for P-521's `p = 2⁵²¹ - 1` and `[a] + [b] < 2p`:
`[a] + [b] + 1` in `xWin 9` (`[a]` loaded, CF set, `[b]` added with `adc`),
reduced by `xCanon`. -/
def addMer (o a b : Nat) : List Instr :=
  [rdiAdd (cOf a)] ++ loadsC (cOf a) (xWin 9) a ++ [rdiMove (cOf a) (cOf b)] ++ setCF ++
    chainC (cOf b) .adc .adc (xWin 9) b ++ [rdiMove (cOf b) (cOf o)] ++ xCanon (cOf o) o ++ [rdiSub (cOf o)]

/-- `[o] = 2 [a] mod p` for P-521's `p` and `[a] < p`: `2 [a] < 2⁵²²` in
`xWin 9` (`dblChain`), its bit 521 moved into its bit 0, which is clear. That
is `[a]`'s 521 bits rotated by one, below `p` as `[a]` is. -/
def dblMer (o a : Nat) : List Instr :=
  [rdiAdd (cOf a)] ++ loadsC (cOf a) (xWin 9) a ++ dblChain .add (xWin 9) ++
    ([.mov .rax (.reg (xAcc 17)), .shift .shr .rax 9, .alu .add (xAcc 9) (.reg .rax),
      .alu .and (xAcc 17) (.imm 511)] : List Instr) ++ [rdiMove (cOf a) (cOf o)] ++ storesC (cOf o) (xWin 9) o ++
    [rdiSub (cOf o)]

/-- `[o] = [a] - [b] mod p` for P-521's `p` and `[a]`, `[b]` below `p`:
`[a] - [b] + 2⁵²¹` in `xWin 9` (`[a]` loaded, `[b]` subtracted, 512 added to
the top word), which is `[a] + (p - [b]) + 1 < 2p + 1`, reduced by `xCanon`. -/
def subMer (o a b : Nat) : List Instr :=
  [rdiAdd (cOf a)] ++ loadsC (cOf a) (xWin 9) a ++ [rdiMove (cOf a) (cOf b)] ++
    chainC (cOf b) .sub .sbb (xWin 9) b ++ ([.alu .add (xAcc 17) (.imm 512)] : List Instr) ++ [rdiMove (cOf b) (cOf o)] ++
    xCanon (cOf o) o ++ [rdiSub (cOf o)]

/-! ## Nine words: the product by columns for any modulus -/

/-- The terms of column `c` of `mulF o a b`: the products `[a + 8i] [b + 8j]`
with `i + j = c`, and the reduction's `u_k [mo + 8j]` with `k + j = c` and
`k < c`, `u_k` in the temporary area. -/
def fTerms (M : Mod) (a b c : Nat) : List (Nat × Option Nat) :=
  ((List.range M.n).filter fun i => i ≤ c ∧ c - i < M.n).map (fun i => (a + 8 * i, some (b + 8 * (c - i)))) ++
    ((List.range M.n).filter fun k => k < c ∧ c - k < M.n).map
      (fun k => (M.tmp + 8 * k, some (M.mo + 8 * (c - k))))

/-- The end of column `c < n` of `mulF`: `u_c = t₀ m' mod 2⁶⁴` into `rcx` and
`[tmp + 8c]`, and `u_c [mo]` added, which clears the low word. -/
def fRed (M : Mod) (c : Nat) : List Instr :=
  [.mov .rax (.reg (pAcc (c + M.n) 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax),
    .store (sc (M.tmp + 8 * c)) .rcx, .mov .rax (.mem (sc M.mo)), .mul .rcx,
    .alu .add (pAcc (c + M.n) 0) (.reg .rax), .alu .adc (pAcc (c + M.n) 1) (.reg .rdx),
    .alu .adc (pAcc (c + M.n) 2) (.imm 0)]

/-- Column `c` of `mulF o a b`, its accumulator `pAcc (c + n)`: its terms,
then for `c < n` the reduction's `u_c` (`fRed`), and for `c ≥ n` its low word
stored at `[tmp + 8 (c - n)]` and cleared. -/
def fCol (M : Mod) (a b c : Nat) : List Instr :=
  (fTerms M a b c).flatMap (fun t => pTerm (c + M.n) t.1 t.2) ++
    if c < M.n then fRed M c
    else [.store (sc (M.tmp + 8 * (c - M.n))) (pAcc (c + M.n) 0), .mov32 (pAcc (c + M.n) 0) (.imm 0)]

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`) for a modulus of eight or nine
words, by Montgomery multiplication in product scanning (Koç, Acar and
Kaliski's FIPS): column `c` sums the products `a_i b_j` and the reduction's
`u_k m_j` with `i + j = k + j = c` in three registers (`pAcc`); at the end of
column `c < n`, `u_c = t₀ m' mod 2⁶⁴` is stored at `[tmp + 8c]` and `u_c m_0`
clears the low word. Columns `n` to `2n - 1` are `(a b + U m) / R < 2m`,
stored over the `u`s no longer needed (column `c` at `[tmp + 8 (c - n)]`),
with its top word in `r9`; `csubW` reduces it into `[o]`. -/
def mulF (M : Mod) (o a b : Nat) : List Instr :=
  ([.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0)] : List Instr) ++
    (List.range (2 * M.n)).flatMap (fCol M a b) ++ csubW M o

/-! ## The operations -/

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`). -/
def mul (M : Mod) (o a b : Nat) : List Instr :=
  if M.n < 7 then mulR M o a b
  else if M.red = .friendly p521Ws then
    (if M.adx then (if a = b then sqrPX M o a else mulPX M o a b)
      else if a = b then sqrP M o a else mulP M o a b)
  else if M.n = 8 ∨ M.n = 9 then mulF M o a b else mulW M o a b

/-- `[o] = [a] + [b] mod m`. -/
def add (M : Mod) (o a b : Nat) : List Instr :=
  if M.n < 7 then addR M o a b
  else if M.red = .friendly p521Ws then (if a = b then dblMer o a else addMer o a b)
  else addW M o a b

/-- `[o] = [a] - [b] mod p` for P-384, the masked `p` in registers. -/
def sub384 (o a b : Nat) : List Instr :=
  loads (low 6) a ++ chain .sub .sbb (low 6) b ++ ([.alu .sbb .rax (.reg .rax)] : List Instr) ++ p384Mask ++
    p384Add (low 6) ++ stores (low 6) o

/-- `[o] = [a] - [b] mod m`. The BMI2/ADX P-256 backend and P-384 use the
register-only masked modulus; other backends retain their existing subtraction. -/
def sub (M : Mod) (o a b : Nat) : List Instr :=
  if M.adx ∧ M.red = .friendly p256Ws then sub256 o a b
  else if M.sparse ∧ M.n = 6 then sub384 o a b
  else if M.n < 7 then subR M o a b else if M.red = .friendly p521Ws then subMer o a b else subW M o a b

end VG.Impl.Mont.X86_64
