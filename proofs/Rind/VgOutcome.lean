import Aeneas
import VerifiedGarbage.Spec.MlKem
open Aeneas Aeneas.Std

/-!
# pyca/verified-garbage's contracts, as rind's wrappers return them

What `Rind/<Arch>/VgMlKem.lean`'s axioms share: the bytes of an array of
`U8` as VG's specs read them, and VG's `Outcome`, the result of a routine
whose `SampleNTT` is bounded, for a wrapper that returns `some` where the
routine returned 1 and `none` where it returned 0.
-/

namespace rind

/-- The bytes of `a`, as VG's specs take them. -/
def vgBytes {n : Usize} (a : Std.Array U8 n) : List VG.Byte := a.val.map (·.bv)

/-- `VG.Spec.MlKem.Outcome` (`Spec/MlKem/Contract.lean`), for a wrapper's
`r`, read as `conv`: `some` with the output of the unbounded algorithm `f`,
for some bound on `SampleNTT`'s loop, or `none` only if some `SampleNTT`
does not finish within `minIterations` iterations. -/
def vgOutcome {α β : Type} (f : Nat → Option α) (conv : β → α) : Option β → Prop
  | some x => ∃ iters, f iters = some (conv x)
  | none => f VG.Spec.MlKem.minIterations = none

end rind
