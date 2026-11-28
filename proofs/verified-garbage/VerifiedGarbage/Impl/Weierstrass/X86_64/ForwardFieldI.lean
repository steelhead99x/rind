module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField

/-!
# Four-limb field programs with code between their operations

`ForwardField.programB` with the block `side i` after operation `i` (from
`0`): code that the operations' wait on each other's results leaves time for,
as `fprogBI` for `fprogB`. On ADX the operations forward their results
through registers as in `programB`, the cache passing over the side code,
which must keep the registers it names and the memory.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.ForwardField
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64

/-- `codes`, with `side i` after operation `i`. -/
def codesI (M : Mod) (side : Nat → List Instr) : Forward.Cache → List FOp → Nat → List (List Instr)
  | _, [], _ => []
  | cs, op :: ops, i => Forward.block cs (code M op) :: side i :: codesI M side (outputCache M op) ops (i + 1)

/-- `programB`'s plain form, with `side i` after operation `i`. -/
def plainI (M : Mod) : List FOp → (Nat → List Instr) → Nat → Prog isa
  | [], _, _ => .block []
  | op :: ops, side, i => .seq ((opCall? M op).getD (.block (code M op)))
      (.seq (.block (side i)) (plainI M ops side (i + 1)))

/-- `programB` with the block `side i` after operation `i`. -/
def programBI (M : Mod) (ops : List FOp) (side : Nat → List Instr) : Prog isa :=
  if M.adx ∧ M.n = 4 then blocks (codesI M side [] ops 0) else plainI M ops side 0

end VG.Impl.Weierstrass.X86_64.ForwardField
