module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField

/-! Public mixed Jacobian addition with register forwarding between field operations. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Jacobian
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- `o = p + q` for an affine `q`, the double of `p` by `dbl` if they are
equal (`dblJMul` for `a = -3`). -/
def jacMixedForward (K : WinCfg) (p q o : Pt) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prog isa :=
  let head := jacMixedHead K.S p q
  let tail := jacMixedTail K.S p q o
  .seq (.block (zeroTest K.M.n p.z)) <|
  .ite .e (.block (copyPt K.M.n o q)) <|
  .seq (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y)) <|
  .seq (ForwardField.programB K.M head) <|
  .seq (.block (zeroTest K.M.n K.S.t3)) <|
  .ite .e
    (.seq (.block (zeroTest K.M.n K.S.t5)) <|
      .ite .e (ForwardField.programB K.M (dbl K.S p o)) (.block (infinity K o)))
    (ForwardField.programB K.M tail)


end VG.Impl.Weierstrass.X86_64.Jacobian
