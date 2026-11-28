module

public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# A cheaper test for `Artifact.spSafe`

`Artifact.spSafe` says that no instruction of the code writes the stack
pointer but as a frame's push or pop: `code.all (fun i => !M.writesSp i)`.
On the ISAs where an instruction may write it (x86, x86-64), the kernel
evaluates the test at every instruction of every function, and
`M.writesSp`, which the trusted base states for a reader, costs it more than
the test needs: on x86-64 a match on the instruction around `Instr.dst`'s
own, then a comparison of `Option Reg`, each match on a type of three
hundred constructors.

An ISA's proofs may give a test `keeps` that implies it and is written for
the kernel, one match and a comparison of constructor indices (`SpTest`).
`Code.all_of_spTest` then proves `spSafe` from `c.allInstrs keeps`, which is
what `sp_safe` (`Registration.lean`) and the proofs evaluate.
-/

@[expose] public section

namespace VG

/-- `keeps i` implies that `i` does not write the stack pointer. The test is
an `outParam`, so that the statement the kernel evaluates names the ISA's
function itself. -/
class SpTest (M : ISA) (keeps : outParam (M.Instr → Bool)) : Prop where
  sound : ∀ i, keeps i = true → M.writesSp i = false

/-- `c.allInstrs (fun i => !M.writesSp i)`, from the ISA's cheaper test. -/
theorem Code.allInstrs_of_spTest {M : ISA} {keeps : M.Instr → Bool} [SpTest M keeps] {c : Prog M}
    (h : c.allInstrs keeps = true) : c.allInstrs (fun i => !M.writesSp i) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h ⊢
  intro i hi
  rw [SpTest.sound i (h i hi)]
  rfl

/-- `Artifact.spSafe`, from the ISA's cheaper test of every instruction. -/
theorem Code.all_of_spTest {M : ISA} {keeps : M.Instr → Bool} [SpTest M keeps] {c : Prog M}
    (h : c.allInstrs keeps = true) : c.all (fun i => !M.writesSp i) = true :=
  Code.all_of_allInstrs (Code.allInstrs_of_spTest h)

end VG
