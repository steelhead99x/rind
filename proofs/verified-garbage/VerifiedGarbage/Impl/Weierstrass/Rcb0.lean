module

public import VerifiedGarbage.Impl.Weierstrass.Slots

/-!
# Complete formulas for `a = 0`, on slots

The complete formulas of Renes, Costello and Batina for a curve
`y² = x³ + b` (secp256k1's), as field operations on slots: Algorithm 8 adds
an affine point (11 products and 2 by `3b`, against Algorithm 1's 12, 3 by
`a` and 2 by `3b`), and Algorithm 9 doubles (6 products and 1 by `3b`, and 2
squares). Each is in its stated order, with `3b` in the slot `S.b3`; `S.a`
and `S.t5` are not used, and `o` must be apart from what they read.

The ladders' doubling and addition (`ladDblOps`, `ladAddOps`) are these for
`a0`, else Algorithm 1 (`rcb`).
-/

-- separate module: `Slots.lean`'s importers would all be rebuilt for formulas only the
-- ladders of curves with `a = 0` use.

@[expose] public section

namespace VG.Impl.Weierstrass

/-- `o = p + q` for an affine `q` (`(q.x : q.y : 1)`; `q.z` is not read) on a
curve with `a = 0`: Algorithm 8 (temporaries `t0 … t4`). -/
def rcb0m (S : RcbSlots) (p q o : Pt) : List FOp :=
  [.mul S.t0 p.x q.x, .mul S.t1 p.y q.y, .add S.t3 q.x q.y, .add S.t4 p.x p.y,
    .mul S.t3 S.t3 S.t4, .add S.t4 S.t0 S.t1, .sub S.t3 S.t3 S.t4, .mul S.t4 q.y p.z,
    .add S.t4 S.t4 p.y, .mul o.y q.x p.z, .add o.y o.y p.x, .add o.x S.t0 S.t0,
    .add S.t0 o.x S.t0, .mul S.t2 S.b3 p.z, .add o.z S.t1 S.t2, .sub S.t1 S.t1 S.t2,
    .mul o.y S.b3 o.y, .mul o.x S.t4 o.y, .mul S.t2 S.t3 S.t1, .sub o.x S.t2 o.x,
    .mul o.y o.y S.t0, .mul S.t1 S.t1 o.z, .add o.y S.t1 o.y, .mul S.t0 S.t0 S.t3,
    .mul o.z o.z S.t4, .add o.z o.z S.t0]

/-- `o = 2p` on a curve with `a = 0`: Algorithm 9 (temporaries `t0 … t2`). -/
def dbl0 (S : RcbSlots) (p o : Pt) : List FOp :=
  [.mul S.t0 p.y p.y, .add o.z S.t0 S.t0, .add o.z o.z o.z, .add o.z o.z o.z,
    .mul S.t1 p.y p.z, .mul S.t2 p.z p.z, .mul S.t2 S.b3 S.t2, .mul o.x S.t2 o.z,
    .add o.y S.t0 S.t2, .mul o.z S.t1 o.z, .add S.t1 S.t2 S.t2, .add S.t2 S.t1 S.t2,
    .sub S.t0 S.t0 S.t2, .mul o.y S.t0 o.y, .add o.y o.x o.y, .mul S.t1 p.x p.y,
    .mul o.x S.t0 S.t1, .add o.x o.x o.x]

/-- The ladder's doubling `D = R + R`: Algorithm 9 for `a0` (`a = 0`), else
Algorithm 1. -/
def ladDblOps (L : LadderCfg) (a0 : Bool) : List FOp :=
  if a0 then dbl0 L.S L.R L.D else rcb L.S L.R L.R L.D

/-- The ladder's addition `T = D + G`: Algorithm 8 for `a0` (`a = 0` and `G`
affine, `G.z` not read), else Algorithm 1. -/
def ladAddOps (L : LadderCfg) (a0 : Bool) : List FOp :=
  if a0 then rcb0m L.S L.D L.G L.T else rcb L.S L.D L.G L.T

end VG.Impl.Weierstrass
