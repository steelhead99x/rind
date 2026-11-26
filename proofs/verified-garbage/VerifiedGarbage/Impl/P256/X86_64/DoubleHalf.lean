module

public import VerifiedGarbage.Impl.P256.X86_64.Half
public import VerifiedGarbage.Impl.Weierstrass.X86_64

/-! In-place Jacobian doubling with a modular half instead of repeated additions. -/

@[expose] public section

namespace VG.Impl.P256.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64

namespace DoubleHalf

def before (S : RcbSlots) (p : Pt) : List FOp :=
  [.add S.t1 p.y p.y, .mul S.t0 p.z p.z, .mul p.z S.t1 p.z, .mul S.t1 S.t1 S.t1,
   .sub S.t3 p.x S.t0, .add S.t4 p.x S.t0, .mul S.t3 S.t3 S.t4,
   .add S.t4 S.t3 S.t3, .add S.t3 S.t4 S.t3,
   .mul S.t2 p.x S.t1, .mul S.t1 S.t1 S.t1]

def after (S : RcbSlots) (p : Pt) : List FOp :=
  [.add S.t4 S.t2 S.t2, .mul p.x S.t3 S.t3, .sub p.x p.x S.t4,
   .sub p.y S.t2 p.x, .mul p.y S.t3 p.y, .sub p.y p.y S.t1]

end DoubleHalf
end VG.Impl.P256.X86_64
