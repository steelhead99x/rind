import Rind.X86_64.Sqrx8xSetup
import Rind.X86_64.Sqrx8xShift

/-! # bn_sqrx8x_internal's squaring

From the routine's entry to the reduction's: the setup, the first row block's triangle, the passes, and the shift
and add leave `t` `a²` and `RedPre`, on a trace of `a`'s and the frame's addresses and `k` alone. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

namespace rind.x86_64.sqrx8x

/-- Runs `c₄` after `c₁`, `c₂` and `c₃`, re-nesting their sequence. -/
theorem exec_seq3 {c₁ c₂ c₃ c₄ : Prog I} {s s₁ s₂ : S} {t t' : List Leak}
    (h : Exec I (.seq c₁ (.seq c₂ c₃)) s t s₁) (h₄ : Exec I c₄ s₁ t' s₂) :
    Exec I (.seq c₁ (.seq c₂ (.seq c₃ c₄))) s (t ++ t') s₂ := by
  cases h with
  | seq h₁ h₂₃ =>
    cases h₂₃ with
    | seq h₂ h₃ => rw [List.append_assoc, List.append_assoc]; exact Exec.seq h₁ (Exec.seq h₂ (Exec.seq h₃ h₄))

/-- The squaring's trace. -/
def squareTrace (ap fp : Addr) (k : Nat) : List Leak :=
  setupTrace ap fp k ++ (triTrace ap fp 0 ++ (outerTrace ap fp k ++ shiftPhaseTrace ap fp k))

/-- The squaring, then `c`, which runs from the reduction's entry with `t` `a²`. -/
theorem square_ok (s₀ : S) (k : Nat) (ap np fp : Addr) (a n : Nat → BitVec 64) (n0 : BitVec 64)
    (hI : InPre s₀ k ap np fp a n n0) (c : Prog I) (T : List Leak) (P : S → Prop)
    (hc : ∀ s, RedPre s k ap np fp a n n0 (val a k * val a k) → Frame s₀ s allRegs →
      Keeps s₀.vg.mem s.vg.mem fp k → ∃ s', Exec I c s T s' ∧ P s') :
    ∃ s', Exec I (.seq (.block Rind.X86_64.Sqrx8x.entry) <|
        .seq (.loop zeroBody (Rind.X86_64.Cond.vg .ne)) <|
        .seq (.block Rind.X86_64.Sqrx8x.init) <|
        .seq (.block Rind.X86_64.Sqrx8x.tri) <|
        .seq (.ite (Rind.X86_64.Cond.vg .e) (.block []) (.loop Rind.X86_64.Sqrx8x.outerPass (Rind.X86_64.Cond.vg .ne))) <|
        .seq (.block Rind.X86_64.Sqrx8x.outerBreak) <|
        .seq (.loop shiftBody .rcxnz) <|
        .seq (.block Rind.X86_64.Sqrx8x.shiftEnd) c) s₀ (squareTrace ap fp k ++ T) s' ∧ P s' := by
  have hC := hI.ctx
  obtain ⟨s1, x1, hP⟩ := setup_ok s₀ k ap np fp a n n0 hI
  obtain ⟨s2, x2, hO⟩ := tri_step s₀ k ap np fp a hC.ar hI.rsp 0 s1 hP
  obtain ⟨s3, x3, hO'⟩ := outer_ok s₀ k ap np fp a hC.k0 hC.ar hI.rsp hI.h63 s2 hO
  obtain ⟨s4, x4, hR, hF, hK⟩ := shiftPhase_ok s₀ k ap np fp a n n0 hC hI.rsp s3 hO'
  obtain ⟨s5, x5, hp⟩ := hc s4 hR hF hK
  refine ⟨s5, ?_, hp⟩
  have x := exec_seq3 x1 (Exec.seq (Exec.block x2) (Exec.seq x3 (exec_seq3 x4 x5)))
  simp only [squareTrace, List.append_assoc]
  exact x

end rind.x86_64.sqrx8x
