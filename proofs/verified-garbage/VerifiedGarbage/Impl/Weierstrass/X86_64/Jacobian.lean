module

public import VerifiedGarbage.Impl.Weierstrass.JacAdd
public import VerifiedGarbage.Impl.Weierstrass.JacMul
public import VerifiedGarbage.Impl.Weierstrass.X86_64.TComb

/-! Jacobian point operations for public verification data. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Jacobian
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

def zeroTest (n a : Nat) : List Instr :=
  [.mov .rdx (.mem (sc a))] ++
    ((List.range (n-1)).map fun i => .alu .or .rdx (.mem (sc (a+8*(i+1))))) ++
    [.alu .test .rdx (.reg .rdx)]

def infinity (K : WinCfg) (o : Pt) : List Instr :=
  setConst K.M.n o.x 0 ++ setConst K.M.n o.y K.one ++ setConst K.M.n o.z 0

/-- `o = p + q`, the double of `p` by `dbl` if they are equal (`dblJMul` for
`a = -3`). -/
def jacAdd (K : WinCfg) (p q o : Pt) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prog isa :=
  .seq (.block (zeroTest K.M.n p.z)) <|
  .ite .e (.block (copyPt K.M.n o q)) <|
  .seq (.block (zeroTest K.M.n q.z)) <|
  .ite .e (.block (copyPt K.M.n o p)) <|
  .seq (fprogB K.M (jacHead K.S p q)) <|
  .seq (.block (zeroTest K.M.n K.S.t3)) <|
  .ite .e
    (.seq (.block (zeroTest K.M.n K.S.t5)) <|
      .ite .e (fprogB K.M (dbl K.S p o)) (.block (infinity K o)))
    (fprogB K.M (jacTail K.S p q o))
end VG.Impl.Weierstrass.X86_64.Jacobian
