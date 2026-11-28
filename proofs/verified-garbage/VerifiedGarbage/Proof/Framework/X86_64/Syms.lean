module

import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# x86-64: the addresses of statics never change

No instruction, call, return or frame changes `State.syms`, the addresses of
the statics the code names (`leaSym`), so neither does a run (`Exec.syms`):
`WP.mono_syms` lets a proof use that the state after some code names the
same addresses as before it.
-/

@[expose] public section

namespace VG.X86_64

theorem setReg_syms (s : State) (r : Reg) (v : BitVec 64) : (s.setReg r v).syms = s.syms := rfl

theorem exec_syms {i : Instr} {s s' : State} (h : exec i s = some s') : s'.syms = s.syms := by
  cases i with
  | store m r | store32 m r | store8 m r | store16 m r | movdquStore m r | stmxcsr m =>
    simp only [reduceExec, State.store64, State.store32, State.store8, State.store16, State.store128] at h
    split at h <;> cases h; rfl
  | vmovdquStore len m r =>
    cases len <;> simp only [reduceExec, State.store128, State.store256] at h <;> split at h <;> cases h <;> rfl
  | vmovdqu32Store m r =>
    simp only [reduceExec, State.store512] at h; split at h <;> cases h; rfl
  | mov _ _ | mov32 _ _ | movzx8 _ _ | movzx16 _ _ | movdquLoad _ _ | vbroadcasti128 _ _ | vmovdqu32Load _ _
  | vbroadcasti32x4 _ _ | vbroadcasti32x4H _ _ | zbcst _ _ _ _ | vpbroadcastdZ _ _ | zbcstd _ _ _ _ | vpmadd52Load _ _ _ _ =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | vmovdquLoad len d m | vbinLoad _ len d _ m =>
    cases len <;> simp only [reduceExec, Option.map_eq_some_iff] at h <;> obtain ⟨_, _, rfl⟩ := h <;> rfl
  | alu op d src =>
    simp only [reduceExec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | alu32 op d src =>
    simp only [reduceExec, Taint.execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | shift32 op _ n =>
    simp only [reduceExec, execShift32] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl
    · cases h
  | shift op _ n =>
    simp only [reduceExec, execShift] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl
    · cases h
  | rorx32 _ _ _ | rorx _ _ _ =>
    simp only [reduceExec, execRorx32, execRorx] at h
    split at h <;> [(simp only [Option.some.injEq] at h; subst h; rfl); cases h]
  | shld _ _ _ | btr _ _ =>
    simp only [reduceExec, execShld, execBtr] at h
    split at h <;> [(simp only [Option.some.injEq] at h; subst h; rfl); cases h]
  | ldmxcsr m =>
    simp only [reduceExec, Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h
    split at h <;> cases h; rfl
  | xop op => simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.XOp.exec_eq op s]
  | vop op => simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.VOp.exec_eq op s]
  | zop op => simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.ZOp.exec_eq op s]
  | eop op => simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.EOp.exec_eq op s]
  | e5op op => simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.E5Op.exec_eq op s]
  | evLoad d m | evMadd52Load _ d _ m | evBroadcastLoad d m | e5InsertLoad d _ m _ =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; cases d <;> rfl
  | evStore m r | e5ExtractStore m r _ =>
    simp only [reduceExec, State.store256] at h; split at h <;> cases h; rfl
  | kLoad k d m | kLoad8 k d m => simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | kStore m k r => obtain ⟨_, rfl⟩ := State.storeMasked512_eq h; rfl
  | kStore8 m k r => obtain ⟨_, rfl⟩ := State.storeMasked512B_eq h; rfl
  | mulx hi lo src =>
    simp only [reduceExec, execMulx] at h; split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | adcx d src | adox d src =>
    simp only [reduceExec, execAdcx, execAdox] at h; split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h; obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | cmov =>
    obtain ⟨_, c, -, -, rfl⟩ := Taint.execCmov_some h; cases c <;> rfl
  | aluTbl op d m n ws =>
    simp only [reduceExec] at h
    split at h <;> [skip; cases h]
    simp only [Taint.execAluW_eq, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; split <;> rfl
  | vmovdquTbl d m n ws | movdquTbl d m n ws => simp only [reduceExec] at h; split at h <;> cases h; rfl
  | push | pop | alloc | free | callr => simp only [reduceExec, reduceCtorEq] at h
  | _ => simp only [reduceExec, Option.some.injEq] at h; subst h; rfl

theorem pushRegs_syms (t : State) (rs : List Reg) : (pushRegs t rs).syms = t.syms := by
  induction rs generalizing t with
  | nil => rfl
  | cons r rs ih => exact (ih _).trans rfl

theorem push_syms {i : Instr} {s s' : State} (h : push i s = some s') : s'.syms = s.syms := by
  cases i <;> simp only [push, reduceCtorEq] at h <;> split at h <;> cases h <;>
    first | rfl | exact pushRegs_syms _ _

theorem pop_syms {j : Instr} {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') : s'.syms = s₂.syms := by
  have hp : ∀ (k : Nat) (r : Reg) (t : State), (popReg t r k).syms = t.syms := by
    intro k; induction k with
    | zero => intro r t; rfl
    | succ k ih => intro r t; exact (ih _ _).trans rfl
  cases j <;> simp only [pop, reduceCtorEq] at h <;> split at h <;> cases h <;>
    first | rfl | exact hp _ _ _

theorem execBlock_syms : ∀ {is : List Instr} {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → s'.syms = s.syms
  | [], _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | i :: is, s, s', t, h => by
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      obtain ⟨⟨s₂, t₂⟩, h₂, e₂⟩ := Option.map_eq_some_iff.mp h
      cases e₂
      exact (execBlock_syms h₂).trans (exec_syms e)

theorem Exec.syms {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.syms = s.syms := by
  induction h with
  | block e => exact execBlock_syms e
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | iteT _ _ ih | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | call e₁ _ e₂ ih =>
    simp only [isa, call, Option.some.injEq] at e₁
    simp only [isa, ret] at e₂
    split at e₂ <;> [cases e₂; cases e₂]
    subst e₁; exact ih
  | frame e₁ _ e₂ ih => exact (pop_syms e₂).trans (ih.trans (push_syms e₁))
  | icall _ e₁ _ e₂ ih =>
    simp only [isa, call, Option.some.injEq] at e₁
    simp only [isa, ret] at e₂
    split at e₂ <;> [cases e₂; cases e₂]
    subst e₁; exact ih
  | icallNext _ _ _ ih => exact ih

/-- The state after `c` names the same addresses of statics as before it. -/
theorem WP.mono_syms {c : Prog isa} {s : State} {Q R : State → Prop} (h : WP isa c s Q)
    (k : ∀ s', Q s' → s'.syms = s.syms → R s') : WP isa c s R := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, k s' hq (Exec.syms he)⟩

/-- `Q` of the state after `c`, which may assume it names the same addresses
of statics as before. -/
theorem WP.of_syms {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => s'.syms = s.syms → Q s') : WP isa c s Q :=
  WP.mono_syms h fun _ hq sy => hq sy

end VG.X86_64
