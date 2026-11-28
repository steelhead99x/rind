module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Forward
public import VerifiedGarbage.Impl.Weierstrass.X86_64
public import VerifiedGarbage.Impl.Mont.X86_64.Double4

/-! Four-limb field programs with register doubling and forwarding between operations. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.ForwardField
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64

def code (M : Mod) (op : FOp) : List Instr :=
  match op with
  | .add o a b => if a=b ∧ M.n=4 then double4 M o a else opCode M op
  | _ => opCode M op

def outputRegs (M : Mod) : FOp → List Reg
  | .mul _ _ _ => match prodK? M with
    | some _ => sqLow
    | none => (List.range M.n).map (win M.n M.n)
  | _ => [.r8,.r9,.r10,.r11]

def outputCache (M : Mod) (op : FOp) : Forward.Cache :=
  let o := match op with | .mul o _ _ | .add o _ _ | .sub o _ _ => o
  Forward.ofStores (outputRegs M op) o

def codes (M : Mod) : Forward.Cache → List FOp → List (List Instr)
  | _,[] => []
  | cs,op::ops => Forward.block cs (code M op) :: codes M (outputCache M op) ops

def lastCache (M : Mod) : Forward.Cache → List FOp → Forward.Cache
  | cs,[] => cs
  | _,op::ops => lastCache M (outputCache M op) ops

def program (M : Mod) (cs : Forward.Cache) (ops : List FOp) : Prog isa :=
  blocks (codes M cs ops)

/-- Keep the same field operations on baseline; forward between them on ADX. -/
def programB (M : Mod) (ops : List FOp) : Prog isa :=
  if M.adx ∧ M.n=4 then program M [] ops else progs (ops.map fun op => (opCall? M op).getD (.block (code M op)))

end VG.Impl.Weierstrass.X86_64.ForwardField
