module

public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalf
public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField

/-! In-place point doubling, retaining field outputs in registers for the next operation. -/

@[expose] public section

namespace VG.Impl.P256.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64

def doubleHalfForward (M : Mod) (S : RcbSlots) (p : Pt) : Prog isa :=
  let cs := ForwardField.lastCache M [] (DoubleHalf.before S p)
  let hs := Forward.ofStores [.r8,.r9,.r10,.r11] S.t1
  .seq (ForwardField.program M [] (DoubleHalf.before S p))
    (.seq (.block (Forward.block cs (half S.t1 S.t1)))
      (ForwardField.program M hs (DoubleHalf.after S p)))

end VG.Impl.P256.X86_64
