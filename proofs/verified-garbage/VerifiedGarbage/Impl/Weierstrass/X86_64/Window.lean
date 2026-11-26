module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.TComb
public import VerifiedGarbage.Impl.Weierstrass.JacMul

/-!
# Short Weierstrass curves on x86-64: scalar multiplication by windows

`[k]P` for a point `P` known only at run time and `k < 2^(64 n)`, by
signed 4-bit windows, as on AArch64 (`Impl/Weierstrass/AArch64/Window.lean`).
The scalar is recoded as `k' = k + 8 Σ_{j<J} 16^j` (`addConst`, `J = 16 n + 1`
digits, so `k' < 16^J`), whose nibbles `k'_j` give the digits
`d_j = k'_j - 8 ∈ [-8, 7]` with `k = Σ_j d_j 16^j`. The table `[m]P` for
`m = 1 … 8` is built in the working space (`build`: `P`, then a loop of
seven complete additions, each copied into its entry); then, from `R = O`,
for `j = J - 1` down to `0`, `R = 16 R + [d_j]P`: four doublings (in
Jacobian coordinates, `quad`), the entry of `|d_j|` selected in constant time
and negated for a negative digit, and a complete addition. The formulas are those for `a = -3` (`dblJ`, `rcb3`,
with `b` in `S.b3`).

The digits are secret. Their magnitudes and signs are read as the comb's
(`TCombCfg.digit`, `TCombCfg.signMask`, `Impl/Weierstrass/X86_64/TComb.lean`,
for windows of 4 bits), and the entry is selected as the comb selects one
(`selPassAt`), from the table at `rdx = rdi + tbl`, whose eight points are
`24 n` bytes apart, 16 bytes at a time: `⌈3 n / 2⌉` pieces of each entry,
the last its last 16 bytes (for odd `n`, overlapping the one before it by a
word); then `y = R` for a zero digit (the entry `(0 : 1 : 0)`).
The counter `rbx` is public, as are every address and branch.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

namespace WinCfg

variable (K : WinCfg)

/-- `8 Σ_{j<J} 16^j`, the recoding's offset. -/
def offset (J : Nat) : Nat := 8 * ((16 ^ J - 1) / 15)

/-- `[dst] = [src] + c`, `n + 1` words from `n` (`c < 2^(64 (n + 1))`): `c` to
`dst`, then `src` added word by word, and the carry into the top word,
through `r8`. -/
def addConst (n src dst c : Nat) : List Instr :=
  setConst (n + 1) dst c ++ chainW .add .adc n dst dst src ++
    [.mov .r8 (.mem (sc (dst + 8 * n))), .alu .adc .r8 (.imm 0), .store (sc (dst + 8 * n)) .r8]

/-- `D` into entry `8 - rbx` of the table, for `rbx ≤ j`: a chain of
`cmp rbx, i` and `je` for `i = j, …, 1`, and entry `8` for `rbx = 0`. -/
def storeEntry : Nat → Prog isa
  | 0 => .block (copyPt K.M.n (K.tblPt 8) K.D)
  | j + 1 => .seq (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 (j + 1)))])
      (.ite .e (.block (copyPt K.M.n (K.tblPt (7 - j)) K.D)) (storeEntry j))

/-- An entry of the table, with `E = [m]P` and `rbx = 8 - m`: `D = E + P`
(`[m + 1]P`), then `E = D`, and `D` into entry `m + 1`. -/
def buildStep : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <| .seq (fprogB K.M (rcb3 K.S K.E K.P K.D)) <|
  .seq (.block (copyPt K.M.n K.E K.D)) <| .seq (storeEntry K 6) (.block [.alu .test .rbx (.reg .rbx)])

/-- The table: `[1]P = P`, then `[m + 1]P = [m]P + P` by a loop of seven
additions into `D`, each copied into its entry (`storeEntry`). -/
def build : Prog isa :=
  .seq (.block (copyPt K.M.n (K.tblPt 1) K.P ++ copyPt K.M.n K.E K.P ++ [.mov32 .rbx (.imm 7)]))
    (.loop (buildStep K) .ne)

/-- The window method as the comb sees it, for the digits and their
negation: windows of 4 bits at `bits`. -/
def tc : TCombCfg where
  M := K.M
  S := K.S
  A := K.R
  E := K.E
  D := K.D
  neg := K.neg
  zero := K.zero
  bits := K.bits
  kbytes := 4 * K.J
  tsym := ""
  w := 4
  J := K.J
  start := (0, 0)
  one := K.one

/-- The 16-byte pieces of an entry of the table: `⌈3 n / 2⌉`. -/
def np : Nat := (3 * K.M.n + 1) / 2

/-- Piece `c` of an entry is at `16 c` bytes into it, but the last at its last
16 bytes (which for odd `n` overlap the piece before it by a word). -/
def po (c : Nat) : Nat := if c + 1 < np K then 16 * c else 24 * K.M.n - 16

/-- `rdx = rdi + tbl`, the table's address. -/
def selSetup : List Instr := [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl))]

/-- `y = R` if the magnitude in `r8` is zero (when the selected entry is
zero), through `rax` and `rcx`. -/
def ySel0 : List Instr :=
  [.mov .rcx (.reg .r8), .alu .cmp .rcx (.imm 1), .alu .sbb .rcx (.reg .rcx)] ++
  (List.range K.M.n).flatMap fun i =>
    [.movImm64 .rax (wordOf K.one i), .alu .and .rax (.reg .rcx), .alu .or .rax (.mem (sc (K.E.y + 8 * i))),
      .store (sc (K.E.y + 8 * i)) .rax]

/-- The entry for the magnitude in `r8` into `E`: `(0 : 1 : 0)` for `0`. -/
def select : List Instr := selSetup K ++ selPassAt K.E.x 8 (24 * K.M.n) (np K) (po K) ++ ySel0 K

/-- The slots of zero, as a point (`toJ` and `fromJ` add zero to copy). -/
def zeroPt : Pt := ⟨K.zero, K.zero, K.zero⟩

/-- The mask `rdx` of `[E.z] = 0` (all ones if it is). -/
def zeroMask : List Instr :=
  [.mov .rdx (.mem (sc K.E.z))] ++
    ((List.range (K.M.n - 1)).map fun j => .alu .or .rdx (.mem (sc (K.E.z + 8 * (j + 1))))) ++
  [.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)]

/-- `R.y` = Montgomery's one where the mask `rdx` is all ones, word `w`:
through `rax` and `r8`. -/
def ySelWord (w : Nat) : List Instr :=
  [.mov .rax (.mem (sc (K.R.y + 8 * w))), .movImm64 .r8 (wordOf K.one w), .alu .xor .r8 (.reg .rax),
    .alu .and .r8 (.reg .rdx), .alu .xor .rax (.reg .r8), .store (sc (K.R.y + 8 * w)) .rax]

/-- `R = (0 : 1 : 0)` where `E.z` is zero: `R.x` and `R.z` are zero then already. -/
def ySel : List Instr := zeroMask K ++ (List.range K.M.n).flatMap (ySelWord K)

/-- `dblJS`'s operations in the order that runs fastest on x86-64 for
nine-word numbers, whose products are calls of `vg_p521_mul_mod_p`: the
chain to `X'` (`X ∓ Z²`, their product and its triple) starts right after
`Z²`, and the additions run between the products they do not feed (the
order measured fastest of those tried). -/
def dblJX (S : RcbSlots) (p o : Pt) : List FOp :=
  [.mul S.t0 p.z p.z, .sub S.t3 p.x S.t0, .add o.x p.x S.t0, .add o.z p.y p.z, .mul S.t1 p.y p.y,
   .mul S.t3 S.t3 o.x, .mul S.t2 p.x S.t1, .add o.x S.t3 S.t3, .add S.t3 o.x S.t3,
   .mul o.z o.z o.z, .add S.t2 S.t2 S.t2, .mul o.x S.t3 S.t3, .add S.t2 S.t2 S.t2,
   .sub o.z o.z S.t1, .sub o.x o.x S.t2, .mul S.t1 S.t1 S.t1, .sub o.x o.x S.t2, .sub o.z o.z S.t0,
   .add S.t1 S.t1 S.t1, .sub o.y S.t2 o.x, .add S.t1 S.t1 S.t1, .add S.t1 S.t1 S.t1,
   .mul o.y S.t3 o.y, .sub o.y o.y S.t1]

/-- Up to six limbs, form `2YZ` directly and scale `Y²` by two first, which
saves four field additions and subtractions for one square that becomes a
product; for more, `dblJ` ordered for the processor's overlap (`dblJX`). -/
def double (p o : Pt) : List FOp :=
  if (K.M.n ≤ 6 : Bool) then dblJMul K.S p o else dblJX K.S p o

/-- A pair of Jacobian doublings, with a public count in the bits above the
window index in `rbx`. The window index is less than 4096. -/
def jacPair : Prog isa :=
  .seq (fprogB K.M (double K K.E K.D)) <|
  .seq (fprogB K.M (double K K.D K.E)) <|
  .block [.alu .sub .rbx (.imm 4096), .alu .cmp .rbx (.imm 4096)]

/-- `R = 16 R` but where it is `O`: into Jacobian coordinates in `E`, two
pairs of doublings between `E` and `D`, and back. The pair loop restores
`rbx` to the window index without an additional scratch slot. -/
def jac : Prog isa :=
  .seq (fprogB K.M (toJ K.S K.R (zeroPt K) K.E)) <|
  .seq (.block [.alu .add .rbx (.imm 8192)]) <|
  .seq (.loop (jacPair K) .ae) <|
  fprogB K.M (fromJ K.S K.E (zeroPt K) K.R)

/-- `R = 16 R`. -/
def quad : Prog isa := .seq (jac K) (.block (ySel K))

/-- Iteration `j = rbx - 1` (with `rbx` counting down from `J`):
`R = 16 R + [d_j]P`. -/
def step : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (quad K) <|
  .seq (.block ((tc K).digit ++ select K)) <|
  .seq (.block (tc K).negY) <|
  .seq (.seq (fprogB K.M (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))) <|
  .block [.alu .test .rbx (.reg .rbx)]

/-- `R = O` and the counter. -/
def init : List Instr :=
  setConst K.M.n K.R.x 0 ++ setConst K.M.n K.R.y K.one ++ setConst K.M.n K.R.z 0 ++
    [.mov32 .rbx (.imm (BitVec.ofNat 32 K.J))]

/-- `[k]P` into `R`, for the table of the bits of `k + offset J` at `K.bits`. -/
def window : Prog isa := .seq (build K) (.seq (.block (init K)) (.loop (step K) .ne))

end WinCfg

end VG.Impl.Weierstrass.X86_64
