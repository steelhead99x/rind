module

public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Field

/-!
# P-256 on x86-64 with AVX512_IFMA: the accumulator of the joint multiplication

The accumulator is a Jacobian point `(X, Y, Z)`, kept as four field vectors
`[u, zn, n3, q3]`:

* `u`, in lane 0, not carried: `Y = 4 u`;
* `zn`, in lane 1, carried (limbs in `[0, 2⁵²)`): `Z = 2 zn`;
* `n3`, carried: `An` in lane 1 (`Z² = 4 An`) and `Xn` in lane 3 (`X = 4 Xn`);
* `q3`, a product: `An²` in lane 1 and `Xn²` in lane 3.

A table's entry for the point `(X₂, Y₂, Z₂)` is carried: `ta` holds
`(Z₂², X₂, Z₂, 2 Y₂)` in its lanes, and `tb` `Z₂³` in lane 0.

Each block is a list of stages (`Seg`), each a function from the field
vectors that are still needed to those needed after it, a product or the
carried operands of the next one at its end:

* `dblSegs`: three stages of four squares each, for `a = -3`, with no
  halving: the new point is `(4 X₃, 8 Y₃, 2 Z₃)` of the usual formulas.
* `addSegs`: four stages of four products each, from `[u, zn, n3, q3, ta,
  tb, sgn]`. `sgn` is zero, or all ones in lanes 0 and 1 to add the entry's
  negative. The sum is scaled too (`(X₃ / 4, Y₃ / 8, Z₃ / 2)` of the usual
  formulas).
* `setSegs`: the entry's point (or its negative) as the accumulator, from
  `[ta, sgn]`.
* `outSegs`: `(Y, Z, _, X)` in the lanes, carried, in Montgomery form with
  `R = 2²⁵⁶` (below `2 p`).

None of them is right where the usual formulas are not (the accumulator or
the entry at infinity, or equal or opposite points): there `Z` comes out
zero modulo `p`, and stays so.
-/

@[expose] public section

namespace VG.Impl.P256.X86_64.Ifma

open VG VG.X86_64

section
variable {m : Type → Type} [Monad m] {α : Type}

/-- A stage: from the field vectors still needed to those needed after it. -/
abbrev Seg (m : Type → Type) (α : Type) := List (F5 α) → m (List (F5 α))

/-- The stages one after the other. -/
def runSegs : List (Seg m α) → List (F5 α) → m (List (F5 α))
  | [], xs => pure xs
  | s :: ss, xs => do runSegs ss (← s xs)

/-- The same value in each limb. -/
def F5.rep (x : α) : F5 α := ⟨x, x, x, x, x⟩

/-- `b` in the lanes where `c` is all ones, `a` where it is zero. -/
def fsel (o : Ops m α) (c : α) (a b : F5 α) : m (F5 α) := a.zipM b fun x y => o.sel c x y

/-- `-a`. -/
def fneg (o : Ops m α) (a : F5 α) : m (F5 α) := do
  let z ← o.zero
  a.mapM fun x => o.sub z x

/-! ### Doubling -/

/-- `[Y, Y + Z, _, D]`: `Y = 4 u`, `Z = 2 zn`, `D = 48 (XX' - AA')`. -/
def dbl1g (o : Ops m α) (u zn q3 : F5 α) : m (F5 α) := do
  let v3 ← fsub o q3 (← fperm o q3 2 1 2 1)
  let d48 ← fadd o (← fshl o v3 5) (← fshl o v3 4)
  let tn ← fperm o (← fshl o u 2) 0 0 0 0
  let tn ← fmadd o tn (← fadd o zn zn) 2
  let tn ← fblend o tn d48 8
  fbias o tn 80 80 80 96

/-- `O1 = [Y, Y + Z, _, D]`, carried. -/
def dbl1 (o : Ops m α) : Seg m α
  | [u, zn, n3, q3] => do
    let o1 ← norm o (← dbl1g o u zn q3)
    pure [o1, q3, n3]
  | _ => pure []

/-- `[B, S, _, DD]`, the squares of `O1`. -/
def dbl2 (o : Ops m α) : Seg m α
  | [o1, q3, n3] => do
    let q1 ← sqrCore o o1
    pure [q1, o1, q3, n3]
  | _ => pure []

/-- `[B, Z3 = S - B - A, X + B, _]`. -/
def dbl3g (o : Ops m α) (q1 n3 : F5 α) : m (F5 α) := do
  let p1 ← fperm o q1 0 0 0 3
  let o3s ← fshl o n3 2                                     -- [_, A, _, X]
  let pxs ← fperm o o3s 0 1 3 3
  let acc ← fblend o q1 p1 4                                -- [B, S, B, DD]
  let acc ← fmsub o acc p1 2
  let acc ← fmsub o acc o3s 2
  let acc ← fmadd o acc pxs 4
  fbias o acc 0 10 0 0

/-- `O2 = [B, Z3 = S - B - A, X + B, _]`, carried. -/
def dbl3 (o : Ops m α) : Seg m α
  | [q1, o1, q3, n3] => do
    let o2 ← norm o (← dbl3g o q1 n3)
    pure [o2, q1, o1, q3]
  | _ => pure []

/-- `[BB, A3, XB2, _]`, the squares of `O2`. -/
def dbl4 (o : Ops m α) : Seg m α
  | [o2, q1, o1, q3] => do
    let q2 ← sqrCore o o2
    pure [q2, o2, q1, o1, q3]
  | _ => pure []

/-- `[E, A3, D + E, X3]`, with `BB` and `DD` in every lane: `W = XB2 - BB - XX`, `X3 = DD - 4 W`, `E = 2 W - X3`. -/
def dbl5g (o : Ops m α) (q2 q1 o1 q3 : F5 α) : m (F5 α × F5 α × F5 α) := do
  let px ← fperm o q2 2 1 2 2
  let pbb ← fperm o q2 0 0 0 0
  let pdd ← fperm o q1 3 3 3 3
  let xx16 ← fshl o (← fperm o q3 3 3 3 3) 4
  let w ← fsub o (← fsub o px pbb) xx16
  let w2 ← fadd o w w
  let w4 ← fadd o w2 w2
  let x3r ← fsub o pdd w4
  let acc ← fmrsub o x3r w2 5
  let acc ← fmadd o acc (← fperm o o1 3 3 3 3) 4
  let acc ← fblend o acc q2 2
  let acc ← fbias o acc 200 0 200 5
  pure (acc, pdd, pbb)

/-- `O3 = [E, A3, D + E, X3]`, carried. -/
def dbl5 (o : Ops m α) : Seg m α
  | [q2, o2, q1, o1, q3] => do
    let (acc, pdd, pbb) ← dbl5g o q2 q1 o1 q3
    let o3 ← norm o acc
    pure [o3, o2, pdd, pbb]
  | _ => pure []

/-- `u' = DE2 - EE - DD - 16 BB`. -/
def dbl6u (o : Ops m α) (q3 pdd pbb : F5 α) : m (F5 α) := do
  let v ← fsub o (← fperm o q3 2 1 2 1) q3
  fsub o (← fsub o v pdd) (← fshl o pbb 4)

/-- `[EE, AA', DE2, XX']`, the squares of `O3`, and `u'`. -/
def dbl6 (o : Ops m α) : Seg m α
  | [o3, o2, pdd, pbb] => do
    let q3 ← sqrCore o o3
    let un ← dbl6u o q3 pdd pbb
    pure [un, o2, o3, q3]
  | _ => pure []

def dblSegs (o : Ops m α) : List (Seg m α) := [dbl1 o, dbl2 o, dbl3 o, dbl4 o, dbl5 o, dbl6 o]

/-! ### Addition -/

/-- `[Xn, An, zn, zn]`. -/
def add1g (o : Ops m α) (zn n3 : F5 α) : m (F5 α) := do
  fblend o (← fperm o n3 3 1 1 1) (← fperm o zn 1 1 1 1) 12

/-- `[Xn, An, zn, zn] · [ZZ2, X2, Z2, Y2'] = [U1, U2, T, V]`. -/
def add1 (o : Ops m α) : Seg m α
  | [u, zn, n3, _, ta, tb, sgn] => do
    let a1 ← add1g o zn n3
    let q1 ← mulCore o a1 ta
    pure [q1, u, n3, tb, sgn]
  | _ => pure []

/-- `[u, ±V, H = U2 - U1, T]`, and `U1` in every lane. -/
def add2g (o : Ops m α) (q1 u : F5 α) (sgn : α) : m (F5 α × F5 α) := do
  let pu1 ← fperm o q1 0 0 0 0
  let x ← fmsub o (← fperm o q1 0 3 1 2) pu1 4              -- [U1, V, H, T]
  let x ← fsel o sgn x (← fneg o x)                         -- V or -V
  let x ← fblend o x u 1
  let x ← fbias o x 20 3 3 0
  pure (x, pu1)

/-- `[u, ±V, H = U2 - U1, T]`, carried. -/
def add2 (o : Ops m α) : Seg m α
  | [q1, u, n3, tb, sgn] => do
    let (x, pu1) ← add2g o q1 u sgn.l0
    let al ← norm o x
    pure [al, pu1, n3, tb]
  | _ => pure []

/-- `[ZZZ2, An, H, H]`, and `H` in every lane. -/
def add3g (o : Ops m α) (al n3 tb : F5 α) : m (F5 α × F5 α) := do
  let ph ← fperm o al 2 2 2 2
  let b2 ← fblend o (← fblend o tb n3 2) ph 12
  pure (b2, ph)

/-- `[u, V, H, T] · [ZZZ2, An, H, H] = [S1, S2, HH, Zh]`. -/
def add3 (o : Ops m α) : Seg m α
  | [al, pu1, n3, tb] => do
    let (b2, ph) ← add3g o al n3 tb
    let q2 ← mulCore o al b2
    pure [q2, ph, pu1]
  | _ => pure []

/-- `[r = S2 - S1, Z3 = 2 Zh, U1, HH]`. -/
def add4g (o : Ops m α) (q2 pu1 : F5 α) : m (F5 α) := do
  let pb ← fperm o q2 1 3 0 2                               -- [S2, Zh, S1, HH]
  let y ← fmadd o pb pb 2
  let y ← fmsub o y q2 1
  let y ← fblend o y pu1 4
  fbias o y 2 0 0 0

/-- `[r = S2 - S1, Z3 = 2 Zh, U1, HH]` and `S1`, carried. -/
def add4 (o : Ops m α) : Seg m α
  | [q2, ph, pu1] => do
    let y ← add4g o q2 pu1
    let be ← norm o y
    let de ← norm o q2
    pure [be, de, ph]
  | _ => pure []

/-- `[r, Z3, U1, H]` and `[r, Z3, HH, HH]`. -/
def add5g (o : Ops m α) (be ph : F5 α) : m (F5 α × F5 α) := do
  let a3 ← fblend o be ph 8
  let b3 ← fblend o be (← fperm o be 3 3 3 3) 4
  pure (a3, b3)

/-- `[r, Z3, U1, H] · [r, Z3, HH, HH] = [rr, A3, UHH, HHH]`. -/
def add5 (o : Ops m α) : Seg m α
  | [be, de, ph] => do
    let (a3, b3) ← add5g o be ph
    let q3s ← mulCore o a3 b3
    pure [q3s, be, de]
  | _ => pure []

/-- `[W = 4 UHH - X3, A3, HHH, X3 = rr - 8 UHH - 4 HHH]`. -/
def add6g (o : Ops m α) (q3s : F5 α) : m (F5 α) := do
  let puh ← fperm o q3s 2 2 2 2
  let phh ← fperm o q3s 3 3 3 3
  let prr ← fperm o q3s 0 0 0 0
  let k ← fadd o (← fshl o puh 3) (← fshl o phh 2)
  let g ← fsub o prr k
  let g0 ← fsub o (← fadd o k (← fshl o puh 2)) prr
  let g ← fblend o g g0 1
  let g ← fblend o g q3s 2
  let g ← fblend o g phh 4
  fbias o g 2 0 0 13

/-- `[W = 4 UHH - X3, A3, HHH, X3 = rr - 8 UHH - 4 HHH]`, carried. -/
def add6 (o : Ops m α) : Seg m α
  | [q3s, be, de] => do
    let ga ← norm o (← add6g o q3s)
    pure [ga, be, de]
  | _ => pure []

/-- `[r, A3, S1, X3]`. -/
def add7g (o : Ops m α) (ga be de : F5 α) : m (F5 α) := do
  fblend o (← fblend o ga be 1) (← fperm o de 0 0 0 0) 4

/-- `u' = 2 (l0 - 4 l1)`. -/
def add7u (o : Ops m α) (q4 : F5 α) : m (F5 α) := do
  let t ← fsub o q4 (← fshl o (← fperm o q4 2 2 2 2) 2)
  fadd o t t

/-- `[r, A3, S1, X3] · [W, A3, HHH, X3] = [l0, AA, l1, XX]`, and `u' = 2 (l0 - 4 l1)`. -/
def add7 (o : Ops m α) : Seg m α
  | [ga, be, de] => do
    let a4 ← add7g o ga be de
    let q4 ← mulCore o a4 ga
    let un ← add7u o q4
    pure [un, be, ga, q4]
  | _ => pure []

def addSegs (o : Ops m α) : List (Seg m α) := [add1 o, add2 o, add3 o, add4 o, add5 o, add6 o, add7 o]

/-! ### The first point -/

/-- The entry's `An = ZZ2`, `Xn = X2`, `zn = Z2` and `u = ±Y2'`. -/
def set1 (o : Ops m α) : Seg m α
  | [ta, sgn] => do
    let ta ← norm o ta
    let n3 ← fperm o ta 0 0 1 1
    let zn ← fperm o ta 2 2 2 2
    let u ← fperm o ta 3 3 3 3
    let u ← fsel o sgn.l0 u (← fneg o u)
    pure [u, zn, n3]
  | _ => pure []

def set2 (o : Ops m α) : Seg m α
  | [u, zn, n3] => do
    let q3 ← sqrCore o n3
    pure [u, zn, n3, q3]
  | _ => pure []

def setSegs (o : Ops m α) : List (Seg m α) := [set1 o, set2 o]

/-! ### Out of the vectors -/

/-- `4 · 2²⁵⁶` and `2 · 2²⁵⁶` modulo `p`. -/
def c4R : Nat := 4 * 2 ^ 256 % pN
def c2R : Nat := 2 * 2 ^ 256 % pN

/-- `[u, zn, _, Xn]`, carried. -/
def out1 (o : Ops m α) : Seg m α
  | [u, zn, n3, _] => do
    let x ← fblend o (← fblend o u zn 2) n3 8
    let x ← fbias o x 20 0 0 0
    let n ← norm o x
    pure [n]
  | _ => pure []

def out2 (o : Ops m α) : Seg m α
  | [n] => do
    let q ← mulCore o n (← fconst o c4R c2R 0 c4R)
    pure [q]
  | _ => pure []

def out3 (o : Ops m α) : Seg m α
  | [q] => do
    let r ← norm o q
    pure [r]
  | _ => pure []

def outSegs (o : Ops m α) : List (Seg m α) := [out1 o, out2 o, out3 o]

/-! ### An entry from the words of field elements -/

/-- The five limbs of `2^s` times the numbers whose words are the lanes of
`w0`, …, `w3` (below `2²⁵⁶`): the top limb is not cut. -/
def limbs (o : Ops m α) (w0 w1 w2 w3 : α) (s : Nat) : m (F5 α) := do
  let c0 ← o.andc (← o.sll w0 s) kMask
  let c1 ← o.andc (← o.add (← o.srl w0 (52 - s)) (← o.sll w1 (12 + s))) kMask
  let c2 ← o.andc (← o.add (← o.srl w1 (40 - s)) (← o.sll w2 (24 + s))) kMask
  let c3 ← o.andc (← o.add (← o.srl w2 (28 - s)) (← o.sll w3 (36 + s))) kMask
  let c4 ← o.srl w3 (16 - s)
  pure ⟨c0, c1, c2, c3, c4⟩

/-- Word `j` of each of four numbers, one to a lane. -/
def col (o : Ops m α) (v0 v1 v2 v3 : α) (j : Nat) : m α := do
  let a ← o.perm v0 (85 * j)
  let b ← o.perm v1 (85 * j)
  let t ← o.blend a b 2
  let c ← o.perm v2 (85 * j)
  let t ← o.blend t c 4
  let d ← o.perm v3 (85 * j)
  o.blend t d 8

/-- `[4 Z², 4 X, 8 Z, 4 Y]` before the carry, from the words of `X`, `Y`, `Z` and `Z²`. -/
def convQg (o : Ops m α) (vx vy vz vzz : α) : m (F5 α) := do
  let w0 ← col o vzz vx vz vy 0
  let w1 ← col o vzz vx vz vy 1
  let w2 ← col o vzz vx vz vy 2
  let w3 ← col o vzz vx vz vy 3
  let t ← limbs o w0 w1 w2 w3 2
  fmadd o t t 4

/-- `2 Z³` in the first lane, from its words. -/
def convQb (o : Ops m α) (vzzz : α) : m (F5 α) := do
  let z1 ← o.perm vzzz 85
  let z2 ← o.perm vzzz 170
  let z3 ← o.perm vzzz 255
  limbs o vzzz z1 z2 z3 1

/-- The entry of a Jacobian point `(X, Y, Z)` with `Z²` and `Z³`, from their words
(`raw`: the words of `X`, `Y`, `Z`, `Z²` and `Z³`, four lanes each): `ta = [4 Z², 4 X, 8 Z, 4 Y]`,
carried, and `tb = [2 Z³, …]`. As numbers over `2²⁶⁰` these are a quarter of `Z²`, `X`, `2 Z` and `Y`,
and an eighth of `Z³`, of the same numbers over `2²⁵⁶`. -/
def convQ (o : Ops m α) : Seg m α
  | [u, zn, n3, q3, raw] => do
    let ta ← norm o (← convQg o raw.l0 raw.l1 raw.l2 raw.l3)
    let tb ← convQb o raw.l4
    pure [u, zn, n3, q3, ta, tb]
  | _ => pure []

/-- A half, a quarter and an eighth, over `2²⁶⁰`. -/
def cHalf : Nat := 2 ^ 259 % pN
def cQuarter : Nat := 2 ^ 258 % pN
def cEighth : Nat := 2 ^ 257 % pN

/-- `[_, 4 x, _, 4 y]`, from the words of `x` and `y`. -/
def convGg (o : Ops m α) (vx vy : α) : m (F5 α) := do
  let w0 ← o.blend (← o.perm vx 0) (← o.perm vy 0) 8
  let w1 ← o.blend (← o.perm vx 85) (← o.perm vy 85) 8
  let w2 ← o.blend (← o.perm vx 170) (← o.perm vy 170) 8
  let w3 ← o.blend (← o.perm vx 255) (← o.perm vy 255) 8
  limbs o w0 w1 w2 w3 2

/-- The entry of an affine point `(x, y)`, from their words (`raw`): `ta = [1/4, 4 x, 1/2, 4 y]` and
`tb = [1/8, …]`. -/
def convG (o : Ops m α) : Seg m α
  | [u, zn, n3, q3, raw] => do
    let t ← convGg o raw.l0 raw.l1
    let ta ← fblend o t (← fconst o cQuarter 0 cHalf 0) 5
    let tb ← fconst o cEighth 0 0 0
    pure [u, zn, n3, q3, ta, tb]
  | _ => pure []

/-! ### An entry kept as limbs -/

/-- An entry from its seven vectors (`raw`: the vector of `tb`'s first four limbs, then that of its
last): `packT0`'s inverse, in `tb`'s first lane. -/
def unpackT (o : Ops m α) : Seg m α
  | [u, zn, n3, q3, ta, raw] => do
    let t1 ← o.perm raw.l0 85
    let t2 ← o.perm raw.l0 170
    let t3 ← o.perm raw.l0 255
    pure [u, zn, n3, q3, ta, ⟨raw.l0, t1, t2, t3, raw.l1⟩]
  | _ => pure []

/-! ### `Q`'s odd multiples, in vectors

The table of `Q`, `3 Q`, …, `15 Q` as entries, from `Q`'s affine coordinates: `Q`'s entry (`tabG`),
`2 Q` and `Q` with one `Z` (`dbluSegs`), then seven times the sum of `2 Q` and the entry before, which
have one `Z`, with `2 Q` brought to the sum's (`zadduSegs`). Between these the points are `r`, not
carried, `[x₁, y₁, y₂, _]`, and `c`, carried, `[_, _, z, x₂]`: `(x₁, y₁, z)` is `2 Q` and `(x₂, y₂, z)`
the entry's point. -/

/-- The entry of the affine point whose words are `raw`'s first two rows: `convG`'s. -/
def tabG (o : Ops m α) : Seg m α
  | [raw] => do
    let t ← convGg o raw.l0 raw.l1
    let ta ← fblend o t (← fconst o cQuarter 0 cHalf 0) 5
    let tb ← fconst o cEighth 0 0 0
    pure [ta, tb]
  | _ => pure []

/-- An entry as the seven vectors it is kept as: `ta`, and for `tb`, whose first lane alone counts,
its first four limbs as the lanes of one vector, then its last (in the places of `tb`'s first and
last rows; the three between are left as they are). -/
def packT0 (o : Ops m α) : Seg m α
  | [ta, tb, r, c] => do
    let v ← col o tb.l0 tb.l1 tb.l2 tb.l3 0
    pure [ta, ⟨v, tb.l1, tb.l2, tb.l3, tb.l4⟩, r, c]
  | _ => pure []

/-- The squares of the entry's `[zz, x, z, y']`: `[zz², XX, _, YY]`. -/
def dblu1 (o : Ops m α) : Seg m α
  | [ta, tb] => do
    let sq ← sqrCore o ta
    pure [sq, ta, tb]
  | _ => pure []

/-- `[x, YY, M = 6 (XX - zz²), YY]`. -/
def dblu2g (o : Ops m α) (sq ta : F5 α) : m (F5 α) := do
  let d ← fsub o (← fperm o sq 1 1 1 1) (← fperm o sq 0 0 0 0)
  let m6 ← fadd o (← fshl o d 2) (← fshl o d 1)
  let acc ← fblend o (← fperm o sq 3 3 3 3) (← fperm o ta 1 1 1 1) 1
  let acc ← fblend o acc m6 4
  fbias o acc 80 80 80 96

def dblu2 (o : Ops m α) : Seg m α
  | [sq, ta, tb] => do
    let n1 ← norm o (← dblu2g o sq ta)
    pure [n1, ta, tb]
  | _ => pure []

/-- `[x, YY, M, YY] · [YY, YY, M, YY] = [S, YY², M², YY²]`. -/
def dblu3 (o : Ops m α) : Seg m α
  | [n1, ta, tb] => do
    let q2 ← mulCore o n1 (← fperm o n1 1 1 2 1)
    pure [q2, n1, ta, tb]
  | _ => pure []

/-- `[12 S - M², 4 S, _, _]`: `4 S - X₃` for `X₃ = M² - 8 S`, and `2 Q`'s `x`. -/
def dblu4g (o : Ops m α) (q2 : F5 α) : m (F5 α) := do
  let ps ← fperm o q2 0 0 0 0
  let s4 ← fshl o ps 2
  let s12 ← fadd o (← fshl o ps 3) s4
  let acc ← fsub o s12 (← fperm o q2 2 2 2 2)
  let acc ← fblend o acc s4 2
  fbias o acc 80 80 80 96

def dblu4 (o : Ops m α) : Seg m α
  | [q2, n1, ta, tb] => do
    let n2 ← norm o (← dblu4g o q2)
    pure [n2, q2, n1, ta, tb]
  | _ => pure []

/-- `[M² - 8 S, M (4 S - X₃) - 4 YY², 4 YY², _]`, for `q3 = [M (4 S - X₃), …]`. -/
def dblu5r (o : Ops m α) (q3 q2 : F5 α) : m (F5 α) := do
  let ps ← fperm o q2 0 0 0 0
  let pyy ← fshl o (← fperm o q2 1 1 1 1) 2
  let xt ← fsub o (← fperm o q2 2 2 2 2) (← fshl o ps 3)
  let yt ← fsub o (← fperm o q3 0 0 0 0) pyy
  let r ← fblend o (← fblend o xt yt 2) pyy 4
  fbias o r 80 80 80 96

/-- `2 Q = (M² - 8 S, M (4 S - X₃) - 4 YY², y')` and `Q = (4 S, 4 YY², y')`. -/
def dblu5 (o : Ops m α) : Seg m α
  | [n2, q2, n1, ta, tb] => do
    let q3 ← mulCore o (← fperm o n1 2 2 2 2) n2
    let r ← dblu5r o q3 q2
    let c ← fblend o (← fperm o ta 3 3 3 3) (← fperm o n2 1 1 1 1) 8
    pure [ta, tb, r, c]
  | _ => pure []

def dbluSegs (o : Ops m α) : List (Seg m α) := [dblu1 o, dblu2 o, dblu3 o, dblu4 o, dblu5 o]

/-- `[x₁ - x₂, y₁ - y₂, z, x₁]`. -/
def zaddu1g (o : Ops m α) (r c : F5 α) : m (F5 α) := do
  let acc ← fblend o r c 4
  let acc ← fmsub o acc (← fperm o c 3 3 3 3) 1
  let acc ← fmsub o acc (← fperm o r 2 2 2 2) 2
  let acc ← fblend o acc (← fperm o r 0 0 0 0) 8
  fbias o acc 80 80 80 96

def zaddu1 (o : Ops m α) : Seg m α
  | [_, _, r, c] => do
    let o1 ← norm o (← zaddu1g o r c)
    pure [o1, r, c]
  | _ => pure []

/-- `[dx, dy, z, x₁] · [dx, dy, dx, x₁] = [C, D, z₃, _]`. -/
def zaddu2 (o : Ops m α) : Seg m α
  | [o1, r, c] => do
    let q1 ← mulCore o o1 (← fperm o o1 0 1 0 3)
    pure [q1, o1, r, c]
  | _ => pure []

/-- `[C, D, z₃, y₁]`, carried. -/
def zaddu3 (o : Ops m α) : Seg m α
  | [q1, o1, r, c] => do
    let n1 ← norm o (← fblend o q1 (← fperm o r 1 1 1 1) 8)
    pure [n1, o1, c]
  | _ => pure []

/-- `[x₁, x₂, z₃, x₁] · [C, C, z₃, C] = [W₁, W₂, zz₃, _]`. -/
def zaddu4 (o : Ops m α) : Seg m α
  | [n1, o1, c] => do
    let a2 ← fblend o (← fblend o (← fperm o o1 3 3 3 3) (← fperm o c 3 3 3 3) 2) n1 4
    let q2 ← mulCore o a2 (← fperm o n1 0 0 2 0)
    pure [q2, n1, o1]
  | _ => pure []

/-- `[W₁ - W₂, 2 W₁ + W₂ - D, zz₃, x₃ = D - W₁ - W₂]`. -/
def zaddu5g (o : Ops m α) (q2 n1 : F5 α) : m (F5 α) := do
  let pw1 ← fperm o q2 0 0 0 0
  let pw2 ← fperm o q2 1 1 1 1
  let pdd ← fperm o n1 1 1 1 1
  let acc ← fmsub o q2 pw2 1
  let acc ← fmadd o acc (← fshl o pw1 1) 2
  let acc ← fmsub o acc pdd 2
  let acc ← fmrsub o acc pdd 8
  let acc ← fmsub o acc pw2 8
  fbias o acc 80 80 80 96

def zaddu5 (o : Ops m α) : Seg m α
  | [q2, n1, o1] => do
    let n2 ← norm o (← zaddu5g o q2 n1)
    pure [n2, q2, n1, o1]
  | _ => pure []

/-- `[y₁, dy, z₃, y₁] · [W₁ - W₂, W₁ - x₃, zz₃, x₃] = [A, E, zzz₃, _]`. -/
def zaddu6 (o : Ops m α) : Seg m α
  | [n2, q2, n1, o1] => do
    let a3 ← fblend o (← fblend o (← fperm o n1 3 3 3 3) o1 2) n1 4
    let q3 ← mulCore o a3 n2
    pure [q3, n2, q2, n1]
  | _ => pure []

/-- `[zzz₃, _, _, 2 (E - A)]`, before the carry (`pa`: `A` in every lane). -/
def zaddu7v (o : Ops m α) (q3 pa : F5 α) : m (F5 α) := do
  let v ← fmsub o (← fperm o q3 2 1 2 1) pa 8
  let v ← fmadd o v v 8
  fbias o v 80 80 80 96

/-- `[W₁, A, E - A, _]`. -/
def zaddu7r (o : Ops m α) (q3 q2 pa : F5 α) : m (F5 α) := do
  let r ← fblend o (← fperm o q3 0 0 1 0) q2 1
  let r ← fmsub o r pa 4
  fbias o r 80 80 80 96

/-- The sum's entry, `[zz₃, x₃, z₃, 2 y₃]` and `zzz₃` for `y₃ = E - A`, and the points after it:
`2 Q = (W₁, A, z₃)` and the sum `(x₃, y₃, z₃)`. -/
def zaddu7 (o : Ops m α) : Seg m α
  | [q3, n2, q2, n1] => do
    let pa ← fperm o q3 0 0 0 0
    let nv ← norm o (← zaddu7v o q3 pa)
    let ta ← fblend o (← fblend o (← fperm o n2 2 3 2 3) n1 4) nv 8
    let r ← zaddu7r o q3 q2 pa
    let c ← fblend o n1 n2 8
    pure [ta, nv, r, c]
  | _ => pure []

def zadduSegs (o : Ops m α) : List (Seg m α) :=
  [zaddu1 o, zaddu2 o, zaddu3 o, zaddu4 o, zaddu5 o, zaddu6 o, zaddu7 o]

end

/-! ## The blocks -/

/-- What five registers from `r` hold. -/
def regs5 (r : Nat) : B (F5 Nat) := do
  let a ← emit (.reg r); let b ← emit (.reg (r + 1)); let c ← emit (.reg (r + 2))
  let d ← emit (.reg (r + 3)); let e ← emit (.reg (r + 4))
  pure ⟨a, b, c, d, e⟩

/-- Five times 32 bytes from `b + d`, `n` bytes apart. -/
def load5 (b : Reg) (d n : Nat) : B (F5 Nat) := do
  let x0 ← emit (.ld b d); let x1 ← emit (.ld b (d + n)); let x2 ← emit (.ld b (d + 2 * n))
  let x3 ← emit (.ld b (d + 3 * n)); let x4 ← emit (.ld b (d + 4 * n))
  pure ⟨x0, x1, x2, x3, x4⟩

/-- The accumulator in `ymm0`–`ymm19`: `u`, `zn`, `n3`, `q3`. -/
def stIn : B (List (F5 Nat)) := do
  let u ← regs5 0; let zn ← regs5 5; let n3 ← regs5 10; let q3 ← regs5 15
  pure [u, zn, n3, q3]

/-- The entry in `ymm20`–`ymm24` (the five rows of `ta`) and `ymm25`–`ymm29` (`tb`, where `tb` is set), and
the mask of its sign at `r9`. -/
def entIn (tb : Bool) : B (List (F5 Nat)) := do
  let ta ← regs5 20
  let t ← if tb then (do let x ← regs5 25; pure [x]) else pure []
  let sgn ← emit (.ld .r9 0)
  pure (ta :: t ++ [F5.rep sgn])

/-- A block in stages: its operations, the places where a new stage starts
with the values needed from there, and the values it leaves with their
registers. -/
structure Staged where
  ops : List Op
  cuts : List (Nat × List Nat)
  outs : List (Nat × Nat)

def stagedGo : List (Seg B Nat) → List (F5 Nat) → List (Nat × List Nat) → B (List (Nat × List Nat) × List Nat)
  | [], xs, cuts => pure (cuts.reverse, xs.flatMap F5.toList)
  | [s], xs, cuts => do
    let ys ← s xs
    pure (cuts.reverse, ys.flatMap F5.toList)
  | s :: ss, xs, cuts => do
    let ys ← s xs
    let b ← get
    stagedGo ss ys ((b.n, ys.flatMap F5.toList) :: cuts)

/-- The stages `segs` from the values `ins`, the last one's results into the registers from 0. -/
def staged (ins : B (List (F5 Nat))) (segs : List (Seg B Nat)) : Staged :=
  let r := (do let xs ← ins; stagedGo segs xs []).run ⟨0, []⟩
  ⟨r.2.ops.reverse, r.1.1, r.1.2.zipIdx⟩

def dblBlk : Staged := staged stIn (dblSegs ssa)

def addBlk : Staged := staged (do let s ← stIn; let e ← entIn true; pure (s ++ e)) (addSegs ssa)

def setBlk : Staged := staged (entIn false) (setSegs ssa)

/-- The rows of `(Y, Z, _, X)` in `ymm0`–`ymm4`. -/
def outBlk : Staged := staged stIn (outSegs ssa)

/-- The words of a Jacobian point at `rcx` (`X`, `Y`, `Z`) with `Z²` and `Z³` at `rdx`. -/
def rawQ : B (F5 Nat) := do
  let x ← emit (.ld .rcx 0); let y ← emit (.ld .rcx 32); let z ← emit (.ld .rcx 64)
  let zz ← emit (.ld .rdx 0); let zzz ← emit (.ld .rdx 32)
  pure ⟨x, y, z, zz, zzz⟩

/-- The words of an affine point at `rdx`. -/
def rawG : B (F5 Nat) := do
  let x ← emit (.ld .rdx 0); let y ← emit (.ld .rdx 32)
  pure ⟨x, y, x, x, x⟩

/-- The entry of the point at `rcx` and `rdx`, into `ymm20`–`ymm29`. -/
def convQBlk : Staged := staged (do let s ← stIn; let r ← rawQ; pure (s ++ [r])) [convQ ssa]

/-- The entry of the affine point at `rdx`, into `ymm20`–`ymm29`. -/
def convGBlk : Staged := staged (do let s ← stIn; let r ← rawG; pure (s ++ [r])) [convG ssa]

/-- The five rows of `ta` of the entry kept as limbs, three at `rcx` and two at `rdx`, into `ymm20`–`ymm24`. -/
def loadABlk : Staged :=
  staged (do
    let s ← stIn
    let a ← emit (.ld .rcx 0); let b ← emit (.ld .rcx 32); let c ← emit (.ld .rcx 64)
    let d ← emit (.ld .rdx 0); let e ← emit (.ld .rdx 32)
    pure (s ++ [⟨a, b, c, d, e⟩])) [fun xs => pure xs]

/-- `tb` of the entry kept as limbs, its two vectors at `rdx`, into `ymm25`–`ymm29`. -/
def loadBBlk : Staged :=
  staged (do
    let s ← stIn
    let ta ← regs5 20
    let v ← emit (.ld .rdx 0); let w ← emit (.ld .rdx 32)
    pure (s ++ [ta, ⟨v, w, v, v, v⟩])) [unpackT ssa]

/-- The words of an affine point's `x` at `rcx` and `y` at `rdx`. -/
def rawP : B (F5 Nat) := do
  let x ← emit (.ld .rcx 0); let y ← emit (.ld .rdx 0)
  pure ⟨x, y, x, x, x⟩

/-- The table's blocks keep an entry in `ymm0`–`ymm9` and the points `r` and `c` in `ymm10`–`ymm19`. -/
def tabIn : B (List (F5 Nat)) := do
  let ta ← regs5 0; let tb ← regs5 5; let r ← regs5 10; let c ← regs5 15
  pure [ta, tb, r, c]

/-- `Q`'s entry, from its words. -/
def tabGBlk : Staged := staged (do let r ← rawP; pure [r]) [tabG ssa]

/-- An entry's seven vectors, from the entry in `ymm0`–`ymm9`: `ymm0`–`ymm4`, `ymm5` and `ymm9`. -/
def packT0Blk : Staged := staged tabIn [packT0 ssa]

/-- `2 Q` and `Q` with one `Z`, from `Q`'s entry. -/
def dbluBlk : Staged := staged (do let ta ← regs5 0; let tb ← regs5 5; pure [ta, tb]) (dbluSegs ssa)

/-- The next odd multiple's entry. -/
def zadduBlk : Staged := staged tabIn (zadduSegs ssa)

/-- The constants of an operation. -/
def Op.consts : Op → List K4
  | .addc _ c | .andc _ c | .maddc _ _ _ c | .const c => [c]
  | .blend _ _ m => [K4.lanes m]
  | _ => []

/-- The constants of the blocks, each once. -/
def pool : List K4 :=
  ((dblBlk.ops ++ addBlk.ops ++ setBlk.ops ++ outBlk.ops ++ convQBlk.ops ++ convGBlk.ops ++ loadABlk.ops ++ loadBBlk.ops ++ tabGBlk.ops ++ packT0Blk.ops ++ dbluBlk.ops ++ zadduBlk.ops).flatMap
      Op.consts ++
    [K4.lanes 0, K4.lanes 3]).eraseDups

/-- The code of a block, in the pieces of its stages, and the places of the
values between them. -/
def Staged.code (c : Cfg) (b : Staged) : List (List Instr) × List (List Loc) := allocCuts c b.ops b.cuts b.outs

end VG.Impl.P256.X86_64.Ifma
