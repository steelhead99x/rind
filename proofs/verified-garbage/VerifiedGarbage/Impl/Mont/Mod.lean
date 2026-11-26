module

/-!
# A modulus for Montgomery arithmetic, on any target

What the Montgomery arithmetic of each target (`Impl/Mont/<Target>.lean`)
needs of an odd multiword modulus `m`: its number of 64-bit words `n`, where
it is in the working space (`mo`, `n` words), the working space's temporary
area (`tmp`, `n` words), `minv = -m⁻¹ mod 2⁶⁴`, and how a reduction step
may add a multiple of `m` (`red`).

A reduction step adds `u m` to the accumulator `T` for the `u` that makes
its low word zero, and divides by `2⁶⁴`. When `m ≡ -1 (mod 2⁶⁴)` (P-256's
`p`), `u` is `T`'s low word `t₀`, and `(T + t₀ m) / 2⁶⁴ = ⌊T / 2⁶⁴⌋ + t₀ m'`
for `m' = (m + 1) / 2⁶⁴`, whose words may be zero or powers of two, which
need no multiplication (`Red.friendly`, with `m'`'s words as `MWord`s).
-/

@[expose] public section

namespace VG.Impl.Mont

/-- A word of a constant multiplicand, as the code multiplies by it: zero,
one, `2^k` (`0 < k < 64`), or any other value. -/
inductive MWord
  | zero
  | one
  | pow2 (k : Nat)
  | gen (v : Nat)
  deriving DecidableEq, Repr

namespace MWord

/-- The word's value. -/
def val : MWord → Nat
  | zero => 0
  | one => 1
  | pow2 k => 2 ^ k
  | gen v => v

/-- The word `w` (below `2⁶⁴`), classified. -/
def ofNat (w : Nat) : MWord :=
  if w = 0 then zero
  else if w = 1 then one
  else match (List.range 64).find? (fun k => 2 ^ k == w) with
    | some k => pow2 k
    | none => gen w

end MWord

/-- How a reduction step adds a multiple of the modulus: `general` (by
`u = t₀ minv`, and the modulus's words in the working space), or `friendly`
for `m ≡ -1 (mod 2⁶⁴)`, with the words of `m' = (m + 1) / 2⁶⁴`. -/
inductive Red
  | general
  | friendly (ws : List MWord)
  deriving DecidableEq, Repr

/-- The reduction of the `n`-word modulus `m`: `friendly` if
`m ≡ -1 (mod 2⁶⁴)`, else `general`. -/
def Red.ofModulus (n m : Nat) : Red :=
  if m % 2 ^ 64 = 2 ^ 64 - 1 then
    .friendly ((List.range n).map fun j => MWord.ofNat ((m + 1) / 2 ^ 64 / 2 ^ (64 * j) % 2 ^ 64))
  else .general

/-- `(2⁶⁴ + 1) m ≤ 2^(64 (n + 1))`: a number below `2m` plus a word times
one below `m` fits in `n + 1` words (`m`'s top word is not all ones). -/
def tightOk (n m : Nat) : Bool := (2 ^ 64 + 1) * m ≤ 2 ^ (64 * (n + 1))

/-- P-384's `p = 2³⁸⁴ - 2¹²⁸ - 2⁹⁶ + 2³² - 1`, of six words, which a reduction
step may add a multiple of without multiplying by its words (`Mod.sparse`):
`2³⁸⁴ - p = 2¹²⁸ + 2⁹⁶ - 2³² + 1` has three, and `-p⁻¹ mod 2⁶⁴ = 2³² + 1`. -/
def sparseOk (n m : Nat) : Bool :=
  n == 6 && m == 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

/-- P-521's order `n`, of nine words, or P-384's, of six, whose products a
function computes with `n` stored in its own working space (`Mod.fnN`). -/
def fnNOk (n m : Nat) : Bool :=
  n == 9 && m == 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449 ||
    n == 6 && m == 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643

/-- A modulus: its number of words `n`, where it is (`mo`, `n` words), the
working space's temporary area (`tmp`, `n` words), `minv = -m⁻¹ mod 2⁶⁴`,
its reduction (`red`), whether it is `tightOk` (`tight`), which only
some targets use, whether to multiply with BMI2 and ADX (`adx`, x86-64
only), and whether it is P-384's `p`, reduced by `2³⁸⁴ - p` (`sparse`, x86-64
only, which needs `sparseOk`), whether its products are written out
in full even where a function computes them (`inl`, x86-64 only, for the
loops that run the most products), and whether it is P-521's `n`, whose
products are calls of a function that stores it (`fnN`, x86-64 only, which
needs `fnNOk`). -/
structure Mod where
  n : Nat
  mo : Nat
  tmp : Nat
  minv : BitVec 64
  red : Red := .general
  tight : Bool := false
  adx : Bool := false
  sparse : Bool := false
  inl : Bool := false
  fnN : Bool := false
  /-- A named modulus for a shared arithmetic function; `Mod.ok` checks the name's value. -/
  fnMod : Option Nat := none

end VG.Impl.Mont
