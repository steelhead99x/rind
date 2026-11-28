import Rind.X86_64.Sqrx8xSquare
import Rind.X86_64.Sqrx8xRed
import Rind.X86_64.Sqrx8xMontProof

/-!
# rind's `bn_sqrx8x_internal` and `bn_sqrx8x_mont`, proven

`bn_sqrx8x_internal_correct`: the routine `RindIsa/X86_64/Sqrx8x.lean` gives as `prog`, which `admin/prove lean`
checks is the machine code of rind's naked function `low::x86_64::mont::bn_sqrx8x_internal` as rind's Linux release
build emits it, run in rind's extension of VG's x86_64 model from a state `InPre` holds of, terminates in one that
`InPost` relates it to, on the trace `internalTrace` of its width, pointers, and frame alone: the squaring
(`Sqrx8xSquare`) leaves `a²` in the frame, and the reduction (`Sqrx8xRed`) its Montgomery reduction.

`bn_sqrx8x_mont_correct`: so `bn_sqrx8x_mont`, which calls it, meets `Sqrx8xMontProof`'s contract, with no
hypothesis. Every theorem rests only on Lean's three axioms.
-/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

namespace rind.x86_64.sqrx8x

/-- `bn_sqrx8x_internal`'s trace: the squaring's, then the reduction's. -/
def internalTrace (k : Nat) (ap np fp : Addr) : List Leak :=
  squareTrace ap fp k ++ redTrace k np fp

/-- `bn_sqrx8x_internal` meets its contract. -/
theorem bn_sqrx8x_internal_correct : sqrx8xmont.Internal internalTrace := by
  intro s k ap np fp a n n0 hI
  obtain ⟨s', x, hP⟩ := square_ok s k ap np fp a n n0 hI (.loop Rind.X86_64.Sqrx8x.redPass (.vg .b))
    (redTrace k np fp) (fun s' => InPost s s' k np fp a n) fun s₄ hR hF hK => by
      obtain ⟨s₅, x₅, hp⟩ := red_ok s₄ k ap np fp a n n0 _ hR
      exact ⟨s₅, x₅, hp.mont, hp.rax, hp.rcx, hp.r8, hp.rbp, Keeps.trans hK hp.keeps, hF.trans hp.frame⟩
  exact ⟨s', x, hP⟩

end rind.x86_64.sqrx8x

/-- info: 'rind.x86_64.sqrx8x.bn_sqrx8x_internal_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.x86_64.sqrx8x.bn_sqrx8x_internal_correct

namespace rind.x86_64.sqrx8xmont

/-- The routine computes the Montgomery square of its argument, keeping what the System V ABI and its contract
require; its trace depends only on its arguments and the stack pointer; and some state meets its precondition. -/
theorem bn_sqrx8x_mont_correct :
    (∀ s, Pre s → ∃ t s', Exec I Rind.X86_64.Sqrx8xMont.prog s t s' ∧ Post s s') ∧
      ConstantTime I Pre Pub Rind.X86_64.Sqrx8xMont.prog ∧ ∃ s, Pre s :=
  bn_sqrx8x_mont_correct_of _ sqrx8x.bn_sqrx8x_internal_correct

end rind.x86_64.sqrx8xmont

/-- info: 'rind.x86_64.sqrx8xmont.bn_sqrx8x_mont_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.x86_64.sqrx8xmont.bn_sqrx8x_mont_correct
