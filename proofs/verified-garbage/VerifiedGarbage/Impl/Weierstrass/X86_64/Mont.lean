module

public import VerifiedGarbage.Impl.Mont.X86_64
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-!
# Shared Montgomery products on x86-64

`vg_p521_mul_mod_p(ws, o, a, b)` and `vg_p521_mul_mod_p_adx`
(`Proof/Weierstrass/MontContract.lean`; System V: `ws` in `rdi`, the offsets `o`,
`a` and `b` in `esi`, `edx` and `ecx`): the inline products of
`Impl/Mont/X86_64.lean` with their operands read through registers.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Mont

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64

/-- The temporary area of the function's products: the last nine words
below byte 4096. -/
def fnTmp : Nat := 4096 - 72

/-- The callee-saved registers the function writes, which it keeps in
`xmm0`–`xmm5`, in that order. -/
def saved : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- P-521's `p` as the function takes it. -/
def fnMod (adx : Bool) : Mod where
  n := 9
  mo := 0
  tmp := fnTmp
  minv := BitVec.ofNat 64 1
  red := .friendly p521Ws
  adx := adx

/-- The offsets zero-extended. -/
def zext : List Instr := [.mov32 .rsi (.reg .rsi), .mov32 .rdx (.reg .rdx), .mov32 .rcx (.reg .rcx)]

/-- The callee-saved registers into `xmm0`–`xmm5`. -/
def saves : List Instr :=
  [.xop (.movq .xmm0 .rbx), .xop (.movq .xmm1 .rbp), .xop (.movq .xmm2 .r12),
    .xop (.movq .xmm3 .r13), .xop (.movq .xmm4 .r14), .xop (.movq .xmm5 .r15)]

/-- The callee-saved registers back from `xmm0`–`xmm5`. -/
def restores : List Instr :=
  [.movqR .rbx .xmm0, .movqR .rbp .xmm1, .movqR .r12 .xmm2, .movqR .r13 .xmm3, .movqR .r14 .xmm4,
    .movqR .r15 .xmm5]

/-- The registers saved, `rbx = ws + a`, `rcx = ws + b`, and ZF set iff
`a = b`; `o` stays in `rsi` throughout. -/
def setup : List Instr :=
  saves ++ [.mov .rbx (.reg .rdx), .alu .add .rbx (.reg .rdi), .alu .add .rcx (.reg .rdi),
    .alu .cmp .rbx (.reg .rcx)]

/-- Words `i … i + k - 1` of `[a]` (through `rbx`) into the temporary area,
through `rax`. -/
def copyW : Nat → Nat → List Instr
  | 0, _ => []
  | k + 1, i => [.mov .rax (.mem (rcR .rbx 0 (8 * i))), .store (sc (fnTmp + 8 * i)) .rax] ++ copyW k (i + 1)

/-- The product by rows: `[a]` copied into the temporary area, where row `i`
reads `a_i` before it stores its low word over it, `rbx = ws + b`, the rows
into the temporary area and `xWin 9`, then the reduction. -/
def mulX : List Instr :=
  copyW 9 0 ++ [.mov .rbx (.reg .rcx)] ++ (List.range 9).flatMap (xRowV (fnMod true) .rdi .rbx 0 fnTmp 0) ++
    xRed (fnMod true) 0

/-- The square and its reduction, `[a]` through `rbx`. -/
def sqrCore : List Instr :=
  (List.range 8).flatMap (sRowV (fnMod true) .rbx 0 0) ++ sDiag (fnMod true) .rbx 0 0 ++
    xRed (fnMod true) 0

/-- The square. -/
def sqrX : List Instr := sqrCore

/-- From `o` in `rsi`: `rdi = ws + o`, the result reduced and stored there,
`rdi = ws`, the registers restored from `xmm0`–`xmm5`. -/
def exit : List Instr :=
  [.alu .add .rdi (.reg .rsi)] ++ xCanon 0 0 ++ [.alu .sub .rdi (.reg .rsi)] ++ restores

/-- `vg_p521_mul_mod_p_adx`. -/
def mulFnX : Prog isa :=
  .seq (.block zext) (.seq (.block setup) (.seq (.ite .e (.block sqrX) (.block mulX)) (.block exit)))

/-! ## Without BMI2 and ADX: the product by columns

The columns of `mulP` and `sqrP` (`Impl/Mont/X86_64.lean`), their operands
read through `rbx = ws + a` and `rbp = ws + b`; the result plus one then into
`xWin 9`, for `exit`. -/

/-- `[a + 8 i]`, through `rbx`. -/
def opA (i : Nat) : MemOp := rcR .rbx 0 (8 * i)

/-- `[b + 8 j]`, through `rbp`. -/
def opB (j : Nat) : MemOp := rcR .rbp 0 (8 * j)

/-- `mx · sy` added to the accumulator of column `c`, `sy` into `rcx` and
`[mx]` into `rax` (`pTerm` with its operands given). -/
def termR (c : Nat) (mx : MemOp) (sy : Src) : List Instr :=
  [.mov .rcx sy, .mov .rax (.mem mx), .mul .rcx, .alu .add (pAcc c 0) (.reg .rax),
    .alu .adc (pAcc c 1) (.reg .rdx), .alu .adc (pAcc c 2) (.imm 0)]

/-- `termR`, the product added twice if `two` (`sTerm`). -/
def termR2 (c : Nat) (mx : MemOp) (sy : Src) (two : Bool) : List Instr :=
  termR c mx sy ++ if two then [.alu .add (pAcc c 0) (.reg .rax), .alu .adc (pAcc c 1) (.reg .rdx),
    .alu .adc (pAcc c 2) (.imm 0)] else []

/-- The reduction's term of column `c`: `512 u_{c-8}`, for `8 ≤ c ≤ 16`. -/
def redTerms (c : Nat) : List (MemOp × Src × Bool) :=
  if 8 ≤ c ∧ c ≤ 16 then [(sc (fnTmp + 8 * (c - 8)), .imm 512, false)] else []

/-- The terms of column `c` of the product (`pTerms`). -/
def mulTerms (c : Nat) : List (MemOp × Src × Bool) :=
  ((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map (fun i => (opA i, .mem (opB (c - i)), false)) ++
    redTerms c

/-- The terms of column `c` of the square (`sTerms`). -/
def sqrTerms (c : Nat) : List (MemOp × Src × Bool) :=
  ((List.range 9).filter fun i => 2 * i < c ∧ c - i < 9).map (fun i => (opA i, .mem (opA (c - i)), true)) ++
    (if c % 2 = 0 ∧ c / 2 < 9 then [(opA (c / 2), .mem (opA (c / 2)), false)] else []) ++ redTerms c

/-- Column `c`: its terms, then its low word stored at `[fnTmp + 8 (c mod 9)]`
and cleared. -/
def colR (ts : Nat → List (MemOp × Src × Bool)) (c : Nat) : List Instr :=
  (ts c).flatMap (fun t => termR2 c t.1 t.2.1 t.2.2) ++
    [.store (sc (fnTmp + 8 * (c % 9))) (pAcc c 0), .mov32 (pAcc c 0) (.imm 0)]

/-- The accumulator cleared, then the eighteen columns. -/
def colsR (ts : Nat → List (MemOp × Src × Bool)) : List Instr :=
  [.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0)] ++ (List.range 18).flatMap (colR ts)

/-- The result `S`, in the temporary area, plus one into `xWin 9`: what
`xCanon` takes. -/
def plusOne : List Instr :=
  loads (xWin 9) fnTmp ++ [.alu .add (xAcc 9) (.imm 1)] ++
    (List.range 8).map (fun k => .alu .adc (xAcc (10 + k)) (.imm 0))

/-- The columns, from `rbx = ws + a` and `rbp = ws + b`. -/
def colsO (ts : Nat → List (MemOp × Src × Bool)) : List Instr := [.mov .rbp (.reg .rcx)] ++ colsR ts

/-- `vg_p521_mul_mod_p`. -/
def mulFn : Prog isa :=
  .seq (.block zext) (.seq (.block setup)
    (.seq (.seq (.ite .e (.block (colsO sqrTerms)) (.block (colsO mulTerms))) (.block plusOne)) (.block exit)))

/-- A call of `f`, whose code is `body`: `rsi`, which the function changes,
kept in `r12`, which it does not, and the offsets into `esi`, `edx` and
`ecx`. -/
def mulCall (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .r12 (.reg .rsi), .mov32 .rsi (.imm (BitVec.ofNat 32 o)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 a)), .mov32 .rcx (.imm (BitVec.ofNat 32 b))])
    (.seq (.call f body) (.block [.mov .rsi (.reg .r12)]))

/-! ## P-384's `p`: the inline product, relocated

`vg_p384_mul_mod_p(ws, o, a, b)` and `vg_p384_mul_mod_p_adx` run the inline
products of `Impl/Mont/X86_64.lean` for P-384's `p` (`mulRounds`, `sqrSA`),
which use every register but `rbx`, `rsi`, `rdi` and `rsp`, with their
operands read through registers: the inline code, made at the offsets `mA`,
`mB` and `mO` (markers, which no operand may be at), with each operand at a
marker moved to a register (`relocTo`), `[a]` through `rbx = ws + a`, `[b]`
through `rsi = ws + b` and `[o]` through `rsi = ws + o` (`o` kept in `xmm6`
meanwhile, for a product); the temporary area stays at `rdi = ws`. The
final reduction is `csubR`, which builds `p` in registers, as the function
has no modulus in memory. -/

/-- The temporary area of the function's products: the last six words below
byte 4096. -/
def fnTmp6 : Nat := 4096 - 48

/-- P-384's `p` as the function takes it. -/
def fnMod6 (adx : Bool) : Mod where
  n := 6
  mo := 0
  tmp := fnTmp6
  minv := BitVec.ofNat 64 0x100000001
  adx := adx
  sparse := true

/-- The memory operand with `f` applied to its memory operand, if any. -/
def _root_.VG.X86_64.Src.mapMem (f : MemOp → MemOp) : Src → Src
  | .mem m => .mem (f m)
  | s => s

/-- The instruction with `f` applied to its memory operand (those of the
integer instructions). -/
def _root_.VG.X86_64.Instr.mapMem (f : MemOp → MemOp) : Instr → Instr
  | .mov d s => .mov d (s.mapMem f)
  | .mov32 d s => .mov32 d (s.mapMem f)
  | .store m r => .store (f m) r
  | .store32 m r => .store32 (f m) r
  | .store8 m r => .store8 (f m) r
  | .alu op d s => .alu op d (s.mapMem f)
  | .alu32 op d s => .alu32 op d (s.mapMem f)
  | .movzx8 d m => .movzx8 d (f m)
  | .mulx hi lo s => .mulx hi lo (s.mapMem f)
  | .adcx d s => .adcx d (s.mapMem f)
  | .adox d s => .adox d (s.mapMem f)
  | .cmov c d s => .cmov c d (s.mapMem f)
  | i => i

/-- The markers: where the inline code the function runs has `[a]`, `[b]`
and `[o]`. -/
def mA : Nat := 1048576
def mB : Nat := 2097152
def mO : Nat := 4194304

/-- An operand `[rdi + d]` with `d` within 4096 bytes past a marker `V`
of `ps`, through that marker's register instead: `[r + d - V]`. -/
def relocTo (ps : List (Nat × Reg)) (m : MemOp) : MemOp :=
  match m.index, ps.find? (fun p => decide ((p.1 : Int) ≤ m.disp ∧ m.disp < p.1 + 4096)) with
  | none, some p => if m.base = .rdi then { m with base := p.2, disp := m.disp - p.1 } else m
  | _, _ => m

/-- Code with its operands at the markers `ps` relocated. -/
def reloc (ps : List (Nat × Reg)) (is : List Instr) : List Instr := is.map (Instr.mapMem (relocTo ps))

/-- The low words and the top word of the product's accumulator. -/
def low6 : List Reg := (List.range 6).map (win 6 6)
def top6 : Reg := win 6 6 6

/-- The square: `rsi = ws + o`, `sqrSA` with `[a]` through `rbx` and `[o]`
through `rsi`, `csubR`, and the result stored through `rsi`. -/
def sqr6 (adx : Bool) : List Instr :=
  [.alu .add .rsi (.reg .rdi)] ++ reloc [(mA, .rbx), (mO, .rsi)] (sqrSA (fnMod6 adx) mO mA) ++
    csubR sqWin6 .r8 ++ reloc [(mO, .rsi)] (stores sqWin6 mO)

/-- The product: `o` into `xmm6` and `rsi = ws + b`, `mulRounds` with `[a]`
through `rbx` and `[b]` through `rsi`, `csubR`, then `rsi = ws + o` and the
result stored through it. -/
def mul6 (adx : Bool) : List Instr :=
  [.xop (.movq .xmm6 .rsi), .mov .rsi (.reg .rcx)] ++ reloc [(mA, .rbx), (mB, .rsi)] (mulRounds (fnMod6 adx) mA mB) ++
    csubR low6 top6 ++ [.movqR .rsi .xmm6, .alu .add .rsi (.reg .rdi)] ++ reloc [(mO, .rsi)] (stores low6 mO)

/-- `vg_p384_mul_mod_p` (`adx` false) and `vg_p384_mul_mod_p_adx`. -/
def mulFn6 (adx : Bool) : Prog isa :=
  .seq (.block zext) (.seq (.block setup) (.seq (.ite .e (.block (sqr6 adx)) (.block (mul6 adx))) (.block restores)))

/-! ## P-521's `n`: the product by columns, relocated

`vg_p521_mul_mod_n(ws, o, a, b)` runs the inline product by columns of
`Impl/Mont/X86_64.lean` (`mulF`), which reads the modulus from the working
space: the function stores P-521's `n` in its own working space (`fnMoN`,
below the temporary area `fnTmp`), the eighty bytes from `fnMoN - 8` kept in
`xmm6`–`xmm10` meanwhile and restored after, and reads its operands through
`rbx = ws + a`, `rbp = ws + b` and `rsi = ws + o` (`relocTo`). It changes
`[o]` and its temporary area only, as the inline product does. -/

/-- Where the function of P-521's `n` stores it: the nine words below its
temporary area. -/
def fnMoN : Nat := fnTmp - 72

/-- P-521's `n`. -/
def n521 : Nat :=
  6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449

/-- P-521's `n` as the function takes it. -/
def fnModN : Mod where
  n := 9
  mo := fnMoN
  tmp := fnTmp
  minv := BitVec.ofNat 64 2103001588584519111
  fnN := true

/-- `n`'s words into `[fnMoN]`, through `rax` (`setConst`). -/
def storeN : List Instr :=
  (List.range 9).flatMap fun j =>
    [.movImm64 .rax (BitVec.ofNat 64 (n521 >>> (64 * j))), .store (sc (fnMoN + 8 * j)) .rax]

/-- Where the function keeps word `j` of the bytes it stores `n` over. -/
def keepX (j : Nat) : XReg :=
  [XReg.xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14].getD j .xmm6

/-- The words at `fnMoN` into `xmm6`–`xmm14`, through `rax`: `movq` keeps
what the constant-time analysis knows public there public (the bits of
`p - 2` that the inversions' callers keep there). -/
def saveN : List Instr :=
  (List.range 9).flatMap fun j => [.mov .rax (.mem (sc (fnMoN + 8 * j))), .xop (.movq (keepX j) .rax)]

/-- And back. -/
def restoreN : List Instr :=
  (List.range 9).flatMap fun j => [.movqR .rax (keepX j), .store (sc (fnMoN + 8 * j)) .rax]

/-- `rbp = ws + b`, `rsi = ws + o`, the bytes kept and `n` stored, `mulF`
with its operands through `rbx`, `rbp` and `rsi`, and the bytes restored. -/
def mulN : List Instr :=
  [.mov .rbp (.reg .rcx), .alu .add .rsi (.reg .rdi)] ++ saveN ++ storeN ++
    reloc [(mA, .rbx), (mB, .rbp), (mO, .rsi)] (mulF fnModN mO mA mB) ++ restoreN

/-- `vg_p521_mul_mod_n`. -/
def mulFnN : Prog isa :=
  .seq (.block zext) (.seq (.block setup) (.seq (.block mulN) (.block restores)))

/-! ## P-384's `n`: the inline product, relocated

`vg_p384_mul_mod_n(ws, o, a, b)` runs the inline product of
`Impl/Mont/X86_64.lean` for a six-word modulus of general form (`mulG`:
`mulRounds`, then `csub`), which reads the modulus from the working space
and uses every register but `rbx`, `rsi`, `rdi` and `rsp`: the function
stores P-384's `n` in its own working space (`fnMoN6`, below the temporary
area `fnTmp6`), the forty-eight bytes there kept in `xmm7`–`xmm12`
meanwhile and restored after, and reads `[a]` through `rbx = ws + a` and
`[b]` through `rsi = ws + b`, then stores the result through
`rsi = ws + o` (`o` kept in `xmm6` meanwhile), as `mul6` does. It changes
`[o]` and its temporary area only, as the inline product does. -/

/-- Where the function of P-384's `n` stores it: the six words below its
temporary area. -/
def fnMoN6 : Nat := fnTmp6 - 48

/-- P-384's `n`. -/
def n384 : Nat :=
  39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643

/-- P-384's `n` as the function takes it, with or without BMI2 and ADX. -/
def fnModN6 (adx : Bool) : Mod where
  n := 6
  mo := fnMoN6
  tmp := fnTmp6
  minv := BitVec.ofNat 64 7986114184663260229
  adx := adx
  fnN := true

/-- `n`'s words into `[fnMoN6]`, through `rax` (`setConst`). -/
def storeN6 : List Instr :=
  (List.range 6).flatMap fun j =>
    [.movImm64 .rax (BitVec.ofNat 64 (n384 >>> (64 * j))), .store (sc (fnMoN6 + 8 * j)) .rax]

/-- Where the function keeps word `j` of the bytes it stores `n` over. -/
def keepX6 (j : Nat) : XReg :=
  [XReg.xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12].getD j .xmm7

/-- The words at `fnMoN6` into `xmm7`–`xmm12`, through `rax`. -/
def saveN6 : List Instr :=
  (List.range 6).flatMap fun j => [.mov .rax (.mem (sc (fnMoN6 + 8 * j))), .xop (.movq (keepX6 j) .rax)]

/-- And back. -/
def restoreN6 : List Instr :=
  (List.range 6).flatMap fun j => [.movqR .rax (keepX6 j), .store (sc (fnMoN6 + 8 * j)) .rax]

/-- `o` into `xmm6` and `rsi = ws + b`, the bytes kept and `n` stored,
`mulRounds` with `[a]` through `rbx` and `[b]` through `rsi`, `csub`, then
`rsi = ws + o`, the result stored through it, and the bytes restored. -/
def mulN6 (adx : Bool) : List Instr :=
  [.xop (.movq .xmm6 .rsi), .mov .rsi (.reg .rcx)] ++ saveN6 ++ storeN6 ++
    reloc [(mA, .rbx), (mB, .rsi)] (mulRounds (fnModN6 adx) mA mB) ++ csub (fnModN6 adx) low6 top6 ++
    [.movqR .rsi .xmm6, .alu .add .rsi (.reg .rdi)] ++ reloc [(mO, .rsi)] (stores low6 mO) ++ restoreN6

/-- `vg_p384_mul_mod_n` (`adx` false) and `vg_p384_mul_mod_n_adx`. -/
def mulFnN6 (adx : Bool) : Prog isa :=
  .seq (.block zext) (.seq (.block setup) (.seq (.block (mulN6 adx)) (.block restores)))

/-! ## Eight-word general moduli

The wide inline product, with operands passed by offset. The modulus is
saved in caller-saved vector registers while the product uses it.
-/
namespace Wide8

def tmp : Nat := 4032
def mo : Nat := 3968

def modulus (order : Bool) : Nat :=
  if order then Impl.Weierstrass.Mont.brainpoolp512r1n.m
  else Impl.Weierstrass.Mont.brainpoolp512r1p.m

def mod (order : Bool) : Mod where
  n := 8
  mo := mo
  tmp := tmp
  minv := BitVec.ofNat 64 (if order then 12486603934235586599 else 9483228555485245381)

/-- Save the modulus workspace before installing the constant. -/
def save : List Instr :=
  (List.range 8).flatMap fun j => [.mov .rax (.mem (sc (mo + 8 * j))), .xop (.movq (keepX j) .rax)]

def store (order : Bool) : List Instr :=
  (List.range 8).flatMap fun j =>
    [.movImm64 .rax (BitVec.ofNat 64 (modulus order >>> (64 * j))), .store (sc (mo + 8 * j)) .rax]

def restore : List Instr :=
  (List.range 8).flatMap fun j => [.movqR .rax (keepX j), .store (sc (mo + 8 * j)) .rax]

def body (order : Bool) : List Instr :=
  [.mov .r12 (.reg .rcx), .alu .add .rsi (.reg .rdi)] ++ save ++ store order ++
    reloc [(mA, .rbx), (mB, .r12), (mO, .rsi)] (mulF (mod order) mO mA mB) ++ restore

def fn (order : Bool) : Prog isa :=
  .seq (.block zext) (.seq (.block setup) (.seq (.block (body order)) (.block restores)))

end Wide8

/-- The function the products modulo `M` call, and its code: P-521's `p`, with
the temporary area the functions' (`fnTmp`), or P-384's (`fnTmp6`) unless its
products are written out (`Mod.inl`), with or without BMI2 and ADX; P-521's
`n` (`Mod.fnN`), with the temporary area `fnTmp`; P-384's `n` (`Mod.fnN`),
with the temporary area `fnTmp6`, with or without BMI2 and ADX; BrainpoolP512r1's
field prime or group order, identified by `fnMod`, with `Wide8.tmp`; none otherwise. -/
def callOf (M : Mod) : Option (String × Prog isa) :=
  if M.n = 9 ∧ M.red = .friendly p521Ws ∧ M.tmp = fnTmp then
    some (if M.adx then ("vg_p521_mul_mod_p" ++ "_adx", mulFnX)
      else ("vg_p521_mul_mod_p", mulFn))
  else if M.n = 6 ∧ M.sparse ∧ M.tmp = fnTmp6 ∧ M.inl = false then
    some (if M.adx then ("vg_p384_mul_mod_p" ++ "_adx", mulFn6 true)
      else ("vg_p384_mul_mod_p", mulFn6 false))
  else if M.n = 9 ∧ M.fnN ∧ M.tmp = fnTmp then
    some ("vg_p521_mul_mod_n", mulFnN)
  else if M.n = 6 ∧ M.fnN ∧ M.tmp = fnTmp6 then
    some (if M.adx then ("vg_p384_mul_mod_n" ++ "_adx", mulFnN6 true)
      else ("vg_p384_mul_mod_n", mulFnN6 false))
  else if M.n = 8 ∧ M.tmp = Wide8.tmp then
    if M.fnMod = some (Wide8.modulus false) then
      some ("vg_brainpoolp512r1_mul_mod_p", Wide8.fn false)
    else if M.fnMod = some (Wide8.modulus true) then
      some ("vg_brainpoolp512r1_mul_mod_n", Wide8.fn true)
    else none
  else none

/-- Whether a product's offsets suit the functions of `n` words: below their
own working space for nine or eight words; for six, apart from their temporary area
and the modulus `n` that `vg_p384_mul_mod_n` stores below it (`fnMoN6`), and
within an immediate's reach. -/
def lowArgs (n o a b : Nat) : Bool :=
  if n = 9 then o + 72 ≤ 3520 && a + 72 ≤ 3520 && b + 72 ≤ 3520
  else if n = 8 then o + 64 ≤ 3584 && a + 64 ≤ 3584 && b + 64 ≤ 3584
  else (o + 96 ≤ fnTmp6 || 4096 ≤ o && o < 2 ^ 31) && (a + 96 ≤ fnTmp6 || 4096 ≤ a && a < 2 ^ 31) &&
    (b + 96 ≤ fnTmp6 || 4096 ≤ b && b < 2 ^ 31)

end VG.Impl.Weierstrass.X86_64.Mont
