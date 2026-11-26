module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField

/-! Jacobian addition using the selected point's cached powers of Z. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.CachedJac
open VG VG.X86_64 VG.Impl.Weierstrass

def head (n : Nat) (S : RcbSlots) (p q : Pt) (dst : Nat) : List FOp :=
  [.mul S.t0 p.z p.z,.mul S.t2 p.x dst,.mul S.t3 q.x S.t0,
   .mul S.t4 p.y (dst+8*n),.mul S.t5 q.y p.z,.mul S.t5 S.t5 S.t0,
   .sub S.t3 S.t3 S.t2,.sub S.t5 S.t5 S.t4]

/-- `o = p + q`, `q`'s `Z²` and `Z³` at `dst`, the double of `p` by `dbl` if
they are equal (`dblJMul` for `a = -3`). -/
def add (K : WinCfg) (p q o : Pt) (dst : Nat) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prog isa :=
  .seq (.block (Jacobian.zeroTest K.M.n p.z)) <|
  .ite .e (.block (copyPt K.M.n o q)) <|
  .seq (.block (Jacobian.zeroTest K.M.n q.z)) <|
  .ite .e (.block (copyPt K.M.n o p)) <|
  .seq (ForwardField.programB K.M (head K.M.n K.S p q dst)) <|
  .seq (.block (Jacobian.zeroTest K.M.n K.S.t3)) <|
  .ite .e
    (.seq (.block (Jacobian.zeroTest K.M.n K.S.t5)) <|
      .ite .e (ForwardField.programB K.M (dbl K.S p o)) (.block (Jacobian.infinity K o)))
    (ForwardField.programB K.M (jacTail K.S p q o))

end VG.Impl.Weierstrass.X86_64.CachedJac
