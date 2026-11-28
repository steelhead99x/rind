module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac
public import VerifiedGarbage.Impl.Weierstrass.X86_64.JacMixedForward
public import VerifiedGarbage.Impl.Weierstrass.Layout.PointOps

/-!
# Short Weierstrass curves on x86-64: point operations as functions

`vg_<curve>_jac_double`, `vg_<curve>_jac_add_cached` and
`vg_<curve>_jac_add_affine` (`Proof/Weierstrass/PointOpsContract.lean`), and their
`_adx` forms for products with BMI2 and ADX: `ws` in `rdi`, where the
curve's code keeps it. Each keeps the callee-saved registers the field
arithmetic writes (`rbp`, `r12`–`r15`) in `xmm0`–`xmm4`, which are
caller-saved, runs the code the joint verifier inlined, into `D` and copied
back to `R` (`R = P`, `E = Q`, `D = O` of the specification), and restores
them. It uses no stack and never writes `rdi`, and every address is `rdi`
plus a constant.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.PointOps

open VG.X86_64 VG.Impl.Weierstrass

/-- The callee-saved registers the field arithmetic writes, and the `xmm`
register each is kept in. -/
def kept : List (Reg × XReg) :=
  [(.rbp, .xmm0), (.r12, .xmm1), (.r13, .xmm2), (.r14, .xmm3), (.r15, .xmm4)]

def saves : List Instr := kept.map fun (r, x) => .xop (.movq x r)

def restores : List Instr := kept.map fun (r, x) => .movqR r x

/-- A function running `body`. -/
def wrap (body : Prog isa) : Prog isa := .seq (.block saves) (.seq body (.block restores))

/-- `R = 2R` by `dbl` (`dblJMul` for `a = -3`), into `D` and copied back
(`Joint.jacDouble`). -/
def doubleBody (K : WinCfg) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prog isa :=
  .seq (fprogB K.M (dbl K.S K.R K.D)) (.block (copyPt K.M.n K.R K.D))

/-- `R = R + E` by the cached Jacobian addition, `E`'s `Z²` and `Z³` at `sel`,
into `D` and copied back; equal points doubled by `dbl`. -/
def addCachedBody (K : WinCfg) (sel : Nat) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prog isa :=
  .seq (CachedJac.add K K.R K.E K.D sel dbl) (.block (copyPt K.M.n K.R K.D))

/-- `R = R + E` by the mixed Jacobian addition, into `D` and copied back;
equal points doubled by `dbl`. -/
def addAffineBody (K : WinCfg) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prog isa :=
  .seq (Jacobian.jacMixedForward K K.R K.E K.D dbl) (.block (copyPt K.M.n K.R K.D))

/-- The suffix of the functions with the products `K.M`. -/
def suffix (K : WinCfg) : String := if K.M.adx then "_adx" else ""

/-- A call of `vg_<curve>_jac_double`. -/
def doubleCall (C : Impl.Weierstrass.PointOps.Curve) (K : WinCfg) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prog isa :=
  .call (s!"vg_{C.curve}_jac_double" ++ suffix K) (wrap (doubleBody K dbl))

/-- A call of `vg_<curve>_jac_add_cached`. -/
def addCachedCall (C : Impl.Weierstrass.PointOps.Curve) (K : WinCfg) (sel : Nat)
    (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prog isa :=
  .call (s!"vg_{C.curve}_jac_add_cached" ++ suffix K) (wrap (addCachedBody K sel dbl))

/-- A call of `vg_<curve>_jac_add_affine`. -/
def addAffineCall (C : Impl.Weierstrass.PointOps.Curve) (K : WinCfg)
    (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prog isa :=
  .call (s!"vg_{C.curve}_jac_add_affine" ++ suffix K) (wrap (addAffineBody K dbl))

end VG.Impl.Weierstrass.X86_64.PointOps
