module

public import VerifiedGarbage.Impl.Mont.Mod

/-!
# Short Weierstrass curves: field programs on slots, on any target

What the code of each target (`Impl/Weierstrass/<Target>.lean`) computes,
independently of its instructions. Field elements are in Montgomery form
in slots of the working space (byte offsets); a point is three slots,
projective coordinates `(X : Y : Z)`.

* `FOp`: a field operation on slots, and `rcb`, the sum of two points by the
  complete formulas of Renes, Costello and Batina (Algorithm 1, any `a`), in
  their 40 steps;
* `LadderCfg`, `PowCfg`, `CombCfg`: the slots and tables of bits that scalar
  multiplication, powers and the fixed-base comb use.
-/

@[expose] public section

namespace VG.Impl.Weierstrass

open VG.Impl.Mont

/-- A field operation on slots (byte offsets of the working space). -/
inductive FOp
  | mul (o a b : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)

/-- A point: the slots of its three coordinates. -/
structure Pt where
  x : Nat
  y : Nat
  z : Nat

/-- The slots the complete addition uses: the curve's `a` and `3b`, and six
temporaries. -/
structure RcbSlots where
  a : Nat
  b3 : Nat
  t0 : Nat
  t1 : Nat
  t2 : Nat
  t3 : Nat
  t4 : Nat
  t5 : Nat

/-- `o = p + q` (Algorithm 1 of Renes, Costello and Batina, in its stated
order; `o`'s slots are written as temporaries too, so they must be apart
from `p`'s and `q`'s). -/
def rcb (S : RcbSlots) (p q o : Pt) : List FOp :=
  [.mul S.t0 p.x q.x, .mul S.t1 p.y q.y, .mul S.t2 p.z q.z,
    .add S.t3 p.x p.y, .add S.t4 q.x q.y, .mul S.t3 S.t3 S.t4,
    .add S.t4 S.t0 S.t1, .sub S.t3 S.t3 S.t4, .add S.t4 p.x p.z,
    .add S.t5 q.x q.z, .mul S.t4 S.t4 S.t5, .add S.t5 S.t0 S.t2,
    .sub S.t4 S.t4 S.t5, .add S.t5 p.y p.z, .add o.x q.y q.z,
    .mul S.t5 S.t5 o.x, .add o.x S.t1 S.t2, .sub S.t5 S.t5 o.x,
    .mul o.z S.a S.t4, .mul o.x S.b3 S.t2, .add o.z o.x o.z,
    .sub o.x S.t1 o.z, .add o.z S.t1 o.z, .mul o.y o.x o.z,
    .add S.t1 S.t0 S.t0, .add S.t1 S.t1 S.t0, .mul S.t2 S.a S.t2,
    .mul S.t4 S.b3 S.t4, .add S.t1 S.t1 S.t2, .sub S.t2 S.t0 S.t2,
    .mul S.t2 S.a S.t2, .add S.t4 S.t4 S.t2, .mul S.t0 S.t1 S.t4,
    .add o.y o.y S.t0, .mul S.t0 S.t5 S.t4, .mul o.x S.t3 o.x,
    .sub o.x o.x S.t0, .mul S.t0 S.t3 S.t1, .mul o.z S.t5 o.z,
    .add o.z o.z S.t0]

/-- `o = p + q` for a curve with `a = -3`, the slot `S.b3` holding `b` (Algorithm 4
of Renes, Costello and Batina, in its stated order; temporaries `t0 … t4`; `o`
apart from `p` and `q`): 12 products and 2 by `b`, against Algorithm 1's 12, 3
by `a` and 2 by `3b`. -/
def rcb3 (S : RcbSlots) (p q o : Pt) : List FOp :=
  [.mul S.t0 p.x q.x, .mul S.t1 p.y q.y, .mul S.t2 p.z q.z,
    .add S.t3 p.x p.y, .add S.t4 q.x q.y, .mul S.t3 S.t3 S.t4,
    .add S.t4 S.t0 S.t1, .sub S.t3 S.t3 S.t4, .add S.t4 p.y p.z,
    .add o.x q.y q.z, .mul S.t4 S.t4 o.x, .add o.x S.t1 S.t2,
    .sub S.t4 S.t4 o.x, .add o.x p.x p.z, .add o.y q.x q.z,
    .mul o.x o.x o.y, .add o.y S.t0 S.t2, .sub o.y o.x o.y,
    .mul o.z S.b3 S.t2, .sub o.x o.y o.z, .add o.z o.x o.x,
    .add o.x o.x o.z, .sub o.z S.t1 o.x, .add o.x S.t1 o.x,
    .mul o.y S.b3 o.y, .add S.t1 S.t2 S.t2, .add S.t2 S.t1 S.t2,
    .sub o.y o.y S.t2, .sub o.y o.y S.t0, .add S.t1 o.y o.y,
    .add o.y S.t1 o.y, .add S.t1 S.t0 S.t0, .add S.t0 S.t1 S.t0,
    .sub S.t0 S.t0 S.t2, .mul S.t1 S.t4 o.y, .mul S.t2 S.t0 o.y,
    .mul o.y o.x o.z, .add o.y o.y S.t2, .mul o.x S.t3 o.x,
    .sub o.x o.x S.t1, .mul o.z S.t4 o.z, .mul S.t1 S.t3 S.t0,
    .add o.z o.z S.t1]

/-- `o = p + q` for an affine `q` (`(q.x : q.y : 1)`; `q.z` is not read) on a
curve with `a = -3`: Algorithm 5 of Renes, Costello and Batina (the mixed
addition: 11 products and 2 by `b`, with `b` in `S.b3`), which is
Algorithm 4 with `Z₂ = 1`. -/
def rcb3m (S : RcbSlots) (p q o : Pt) : List FOp :=
  [.mul S.t0 p.x q.x, .mul S.t1 p.y q.y, .add S.t3 q.x q.y, .add S.t4 p.x p.y,
    .mul S.t3 S.t3 S.t4, .add S.t4 S.t0 S.t1, .sub S.t3 S.t3 S.t4, .mul S.t4 q.y p.z,
    .add S.t4 S.t4 p.y, .mul o.y q.x p.z, .add o.y o.y p.x, .mul o.z S.b3 p.z,
    .sub o.x o.y o.z, .add o.z o.x o.x, .add o.x o.x o.z, .sub o.z S.t1 o.x,
    .add o.x S.t1 o.x, .mul o.y S.b3 o.y, .add S.t1 p.z p.z, .add S.t2 S.t1 p.z,
    .sub o.y o.y S.t2, .sub o.y o.y S.t0, .add S.t1 o.y o.y, .add o.y S.t1 o.y,
    .add S.t1 S.t0 S.t0, .add S.t0 S.t1 S.t0, .sub S.t0 S.t0 S.t2, .mul S.t1 S.t4 o.y,
    .mul S.t2 S.t0 o.y, .mul o.y o.x o.z, .add o.y o.y S.t2, .mul o.x S.t3 o.x,
    .sub o.x o.x S.t1, .mul o.z S.t4 o.z, .mul S.t1 S.t3 S.t0, .add o.z o.z S.t1]

/-- `o = 2p` in Jacobian coordinates (`(X : Y : Z)` for `(X / Z², Y / Z³)`) for
a curve with `a = -3` (dbl-2001-b: 3 products and 5 squares; temporaries `t0 … t3`;
`o` apart from `p`). -/
def dblJ (S : RcbSlots) (p o : Pt) : List FOp :=
  [.mul S.t0 p.z p.z, .mul S.t1 p.y p.y, .mul S.t2 p.x S.t1, .sub S.t3 p.x S.t0,
    .add o.x p.x S.t0, .mul S.t3 S.t3 o.x, .add o.x S.t3 S.t3, .add S.t3 o.x S.t3,
    .add S.t2 S.t2 S.t2, .add S.t2 S.t2 S.t2, .add o.z p.y p.z, .mul o.z o.z o.z,
    .sub o.z o.z S.t1, .sub o.z o.z S.t0, .mul o.x S.t3 S.t3, .sub o.x o.x S.t2,
    .sub o.x o.x S.t2, .sub o.y S.t2 o.x, .mul o.y S.t3 o.y, .mul S.t1 S.t1 S.t1,
    .add S.t1 S.t1 S.t1, .add S.t1 S.t1 S.t1, .add S.t1 S.t1 S.t1, .sub o.y o.y S.t1]

/-- `o = p + q` for a Jacobian `p` and an affine `q` (`q.z` is not read), by
the mixed Jacobian addition madd-2004-hmv (8 products, 3 squares), which
fails for equal points: `H = x₂Z₁² - X₁`, `r = y₂Z₁³ - Y₁`,
`X₃ = r² - H³ - 2X₁H²`, `Y₃ = r(X₁H² - X₃) - Y₁H³`, `Z₃ = Z₁H`. -/
def maddJ (S : RcbSlots) (p q o : Pt) : List FOp :=
  [.mul S.t0 p.z p.z, .mul S.t1 q.x S.t0, .mul S.t2 p.z S.t0, .mul S.t2 q.y S.t2,
    .sub S.t1 S.t1 p.x, .sub S.t2 S.t2 p.y, .mul S.t3 S.t1 S.t1, .mul S.t4 S.t1 S.t3,
    .mul S.t3 p.x S.t3, .mul o.x S.t2 S.t2, .sub o.x o.x S.t4, .add S.t5 S.t3 S.t3,
    .sub o.x o.x S.t5, .sub S.t3 S.t3 o.x, .mul S.t3 S.t2 S.t3, .mul S.t4 p.y S.t4,
    .sub o.y S.t3 S.t4, .mul o.z p.z S.t1]

/-- `o` = the projective `p` in Jacobian coordinates: `(XZ : YZ² : Z)` (`z.x`
holding zero; temporary `t0`). -/
def toJ (S : RcbSlots) (p z o : Pt) : List FOp :=
  [.mul o.x p.x p.z, .mul S.t0 p.z p.z, .mul o.y p.y S.t0, .add o.z p.z z.x]

/-- `o` = the Jacobian `p` in projective coordinates: `(XZ : Y : Z³)` (`z.x`
holding zero; temporary `t0`). -/
def fromJ (S : RcbSlots) (p z o : Pt) : List FOp :=
  [.mul o.x p.x p.z, .mul S.t0 p.z p.z, .mul o.z S.t0 p.z, .add o.y p.y z.x]

/-- What scalar multiplication needs: the field, the slots of `G` and of the
points, the slots of the complete addition, and the table of the scalar's
bits (byte `t` is bit `t`), with `nbits` bits. -/
structure LadderCfg where
  M : Mod
  S : RcbSlots
  G : Pt
  R : Pt
  D : Pt
  T : Pt
  bits : Nat
  nbits : Nat

/-- What a power needs: the modulus, the slots of the accumulator, of a
temporary, of the base and of `R mod m` (Montgomery's one), and the table of
the exponent's bits, with `nbits` bits. -/
structure PowCfg where
  M : Mod
  acc : Nat
  tmp : Nat
  base : Nat
  one : Nat
  bits : Nat
  nbits : Nat

/-- What the comb needs: the field, the complete addition's slots, the
accumulator `A` (the result), the slots of the selected entry `E` and of the
sum `D`, a slot for `-y` and one holding zero, the scalar's table of bits,
the tables (`tbl[j][m - 1]` is the Montgomery form of `[m 16^j]P`'s `(x, y)`),
the start `[c]P` (Montgomery `(x, y)`) and `R mod p`. -/
structure CombCfg where
  M : Mod
  S : RcbSlots
  A : Pt
  E : Pt
  D : Pt
  neg : Nat
  zero : Nat
  bits : Nat
  tbl : List (List (Nat × Nat))
  start : Nat × Nat
  one : Nat

/-- The number of the comb's tables (and of digits). -/
def CombCfg.J (K : CombCfg) : Nat := K.tbl.length

/-- What the window method needs: the field, the complete addition's slots,
the point `P` (read only), the accumulator `R` (the result), the slots of the
selected entry `E` and of the sum `D`, a slot for `-y` and one holding zero,
the table of bits of the recoded scalar (`4 J` bytes), where the table of
`[m]P` for `m = 1 … 8` goes (`tbl`: 8 points of three `n`-word slots), the
number of digits `J`, and `R mod p`. -/
structure WinCfg where
  M : Mod
  S : RcbSlots
  P : Pt
  R : Pt
  E : Pt
  D : Pt
  neg : Nat
  zero : Nat
  bits : Nat
  tbl : Nat
  J : Nat
  one : Nat

/-- Entry `m` (`1 … 8`) of the window method's table of `[m]P`. -/
def WinCfg.tblPt (K : WinCfg) (m : Nat) : Pt :=
  ⟨K.tbl + 24 * K.M.n * (m - 1), K.tbl + 24 * K.M.n * (m - 1) + 8 * K.M.n,
    K.tbl + 24 * K.M.n * (m - 1) + 16 * K.M.n⟩

end VG.Impl.Weierstrass
