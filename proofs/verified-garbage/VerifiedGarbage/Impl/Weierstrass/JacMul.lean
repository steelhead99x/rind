module

public import VerifiedGarbage.Impl.Weierstrass.Slots

@[expose] public section

namespace VG.Impl.Weierstrass

/-- Jacobian doubling with direct `2YZ` and a rescaled `Y²` intermediate.
Computing `Z' = 2YZ` directly saves two field subtractions. Scaling `Y²` by two before its product
and square also saves two field additions. -/
def dblJMul (S : RcbSlots) (p o : Pt) : List FOp :=
  [.mul S.t0 p.z p.z, .mul S.t1 p.y p.y, .add S.t1 S.t1 S.t1,
   .mul S.t2 p.x S.t1, .sub S.t3 p.x S.t0, .add o.x p.x S.t0,
   .mul S.t3 S.t3 o.x, .add o.x S.t3 S.t3, .add S.t3 o.x S.t3,
   .add S.t2 S.t2 S.t2, .mul o.z p.y p.z, .add o.z o.z o.z,
   .mul o.x S.t3 S.t3, .sub o.x o.x S.t2, .sub o.x o.x S.t2,
   .sub o.y S.t2 o.x, .mul o.y S.t3 o.y, .mul S.t1 S.t1 S.t1,
   .add S.t1 S.t1 S.t1, .sub o.y o.y S.t1]

/-- `dblJ`'s doubling (dbl-2001-b, for `a = -3`), its operations ordered so
that each product's operands are ready well before it, the cheap operations
between dependent ones: the processor overlaps a product's last carry chains
with the next independent product. -/
def dblJS (S : RcbSlots) (p o : Pt) : List FOp :=
  [.mul S.t0 p.z p.z, .mul S.t1 p.y p.y, .add o.z p.y p.z, .sub S.t3 p.x S.t0,
   .add o.x p.x S.t0, .mul S.t2 p.x S.t1, .mul o.z o.z o.z, .mul S.t3 S.t3 o.x,
   .sub o.z o.z S.t1, .sub o.z o.z S.t0, .mul S.t1 S.t1 S.t1, .add o.x S.t3 S.t3,
   .add S.t3 o.x S.t3, .add S.t2 S.t2 S.t2, .add S.t2 S.t2 S.t2, .mul o.x S.t3 S.t3,
   .add S.t1 S.t1 S.t1, .add S.t1 S.t1 S.t1, .add S.t1 S.t1 S.t1, .sub o.x o.x S.t2,
   .sub o.x o.x S.t2, .sub o.y S.t2 o.x, .mul o.y S.t3 o.y, .sub o.y o.y S.t1]

/-- Jacobian doubling for `a = 0` (dbl-2009-l, with `Z' = 2YZ` as a product),
in the order of `Impl.Weierstrass.PointOps.jacDouble0`: `A = X²`, `B = Y²`,
`C = B²`, `D = 2 ((X + B)² - A - C)`, `E = 3A`, `Z' = 2YZ`, `X' = E² - 2D`,
`Y' = E (D - X') - 8C`, 2 products and 5 squares. It reads each coordinate
of `p` for the last time before it writes `o`'s, so `o` may be `p`. -/
def dblJ0 (S : RcbSlots) (p o : Pt) : List FOp :=
  [.mul S.t0 p.x p.x, .mul S.t1 p.y p.y, .mul S.t2 S.t1 S.t1, .add S.t3 p.x S.t1,
   .mul S.t3 S.t3 S.t3, .sub S.t3 S.t3 S.t0, .sub S.t3 S.t3 S.t2, .add S.t3 S.t3 S.t3,
   .add S.t4 S.t0 S.t0, .add S.t4 S.t4 S.t0, .mul o.z p.y p.z, .add o.z o.z o.z,
   .mul o.x S.t4 S.t4, .sub o.x o.x S.t3, .sub o.x o.x S.t3, .sub o.y S.t3 o.x,
   .mul o.y S.t4 o.y, .add S.t2 S.t2 S.t2, .add S.t2 S.t2 S.t2, .add S.t2 S.t2 S.t2,
   .sub o.y o.y S.t2]

end VG.Impl.Weierstrass
