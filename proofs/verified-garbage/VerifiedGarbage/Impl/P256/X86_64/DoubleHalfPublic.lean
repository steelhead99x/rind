module

public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfForward

/-! The measured verifier forwards registers on ADX and uses separate field blocks on baseline. -/

@[expose] public section

namespace VG.Impl.P256.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64

def doubleHalfPublic (M : Mod) (S : RcbSlots) (p : Pt) : Prog isa :=
  if M.adx then doubleHalfForward M S p else
    .seq (ForwardField.programB M (DoubleHalf.before S p))
      (.seq (.block (half S.t1 S.t1)) (ForwardField.programB M (DoubleHalf.after S p)))

end VG.Impl.P256.X86_64
