module

public import VerifiedGarbage.Impl.Weierstrass.Slots

@[expose] public section

namespace VG.Impl.Weierstrass

/-- Jacobian addition header: `t2 = U1`, `t3 = H`, `t4 = S1`, `t5 = r`.
The caller handles `H = 0` before running the tail. -/
def jacHead (S : RcbSlots) (p q : Pt) : List FOp :=
  [.mul S.t0 p.z p.z, .mul S.t1 q.z q.z,
   .mul S.t2 p.x S.t1, .mul S.t3 q.x S.t0,
   .mul S.t4 p.y q.z, .mul S.t4 S.t4 S.t1,
   .mul S.t5 q.y p.z, .mul S.t5 S.t5 S.t0,
   .sub S.t3 S.t3 S.t2, .sub S.t5 S.t5 S.t4]

/-- Jacobian addition for a nonzero `H` from `jacHead`. -/
def jacTail (S : RcbSlots) (p q o : Pt) : List FOp :=
  [.mul S.t0 S.t3 S.t3, .mul S.t1 S.t0 S.t3,
   .mul S.t2 S.t2 S.t0, .mul o.x S.t5 S.t5,
   .sub o.x o.x S.t1, .sub o.x o.x S.t2, .sub o.x o.x S.t2,
   .sub o.y S.t2 o.x, .mul o.y S.t5 o.y,
   .mul S.t4 S.t4 S.t1, .sub o.y o.y S.t4,
   .mul o.z p.z q.z, .mul o.z o.z S.t3]

/-- Mixed-addition header, after copying `p.x` and `p.y` to `t2` and `t4`.
The second point is affine, so its Jacobian z coordinate is one. -/
def jacMixedHead (S : RcbSlots) (p q : Pt) : List FOp :=
  [.mul S.t0 p.z p.z, .mul S.t3 q.x S.t0,
   .mul S.t5 q.y p.z, .mul S.t5 S.t5 S.t0,
   .sub S.t3 S.t3 S.t2, .sub S.t5 S.t5 S.t4]

/-- Mixed-addition tail, omitting multiplication by the affine point's z coordinate. -/
def jacMixedTail (S : RcbSlots) (p q o : Pt) : List FOp :=
  (jacTail S p q o).take 11 ++ [.mul o.z p.z S.t3]

end VG.Impl.Weierstrass
