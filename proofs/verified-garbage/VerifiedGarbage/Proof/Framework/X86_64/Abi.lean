module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# x86-64: the calling-convention obligations

`abiPreserved` asks that MXCSR's control bits be restored. Code that never
loads MXCSR keeps it, so its proofs show only the other obligations
(`gprPreserved`), and `abiPreserved_of_exec` adds MXCSR's.
-/

@[expose] public section

namespace VG.X86_64

theorem exec_mxcsr {i : Instr} (hi : loadsMxcsr i = false) {s s' : State} (h : exec i s = some s') :
    s'.mxcsr = s.mxcsr := by
  cases i with
  | ldmxcsr => cases hi
  | alu op d src =>
    simp only [reduceExec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | alu32 op d src =>
    simp only [reduceExec, Taint.execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | aluTbl op d m n ws =>
    simp only [reduceExec] at h
    split at h <;> [skip; cases h]
    simp only [Taint.execAluW_eq, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; split <;> rfl
  | shift32 op d n =>
    simp only [reduceExec, execShift32] at h
    split at h <;> [skip; cases h]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; rfl)
  | shift op d n =>
    simp only [reduceExec, execShift] at h
    split at h <;> [skip; cases h]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; rfl)
  | xop op => simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.XOp.exec_eq op s]
  | vop op => simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.VOp.exec_eq op s]
  | vmovdquLoad len d m | vbinLoad _ len d _ m =>
    cases len <;> simp only [reduceExec, Option.map_eq_some_iff] at h <;> obtain ⟨_, _, rfl⟩ := h <;> rfl
  | vmovdquTbl d m n ws | movdquTbl d m n ws => simp only [reduceExec] at h; split at h <;> cases h; rfl
  | vmovdquStore len m r =>
    cases len
    · simp only [reduceExec, State.store128] at h; split at h <;> cases h; rfl
    · simp only [reduceExec, State.store256] at h; split at h <;> cases h; rfl
  | store m r => simp only [reduceExec, State.store64] at h; split at h <;> cases h; rfl
  | store32 m r => simp only [reduceExec, State.store32] at h; split at h <;> cases h; rfl
  | store8 m r => simp only [reduceExec, State.store8] at h; split at h <;> cases h; rfl
  | store16 m r => simp only [reduceExec, State.store16] at h; split at h <;> cases h; rfl
  | movdquStore m r => simp only [reduceExec, State.store128] at h; split at h <;> cases h; rfl
  | stmxcsr m => simp only [reduceExec, State.store32] at h; split at h <;> cases h; rfl
  | vmovdqu32Store m r => simp only [reduceExec, State.store512] at h; split at h <;> cases h; rfl
  | evStore m r | e5ExtractStore m r _ =>
    simp only [reduceExec, State.store256] at h; split at h <;> cases h; rfl
  | kStore m k r => obtain ⟨_, rfl⟩ := State.storeMasked512_eq h; rfl
  | kStore8 m k r => obtain ⟨_, rfl⟩ := State.storeMasked512B_eq h; rfl
  | zop op => simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.ZOp.exec_eq op s]
  | eop op => simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.EOp.exec_eq op s]
  | e5op op => simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.E5Op.exec_eq op s]
  | evLoad d | evMadd52Load _ d | evBroadcastLoad d | e5InsertLoad d =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; cases d <;> rfl
  | mov | mov32 | movzx8 | movzx16 | movdquLoad | vbroadcasti128 | vmovdqu32Load | vbroadcasti32x4 | vbroadcasti32x4H | zbcst | vpbroadcastdZ | zbcstd
  | vpmadd52Load | kLoad | kLoad8 =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | bswap32 | bswap | movImm64 | leaSym | lfence | mul | imul | imul3 | andn32 | andn | vpmovmskb | vpcmpltuw
  | movqR | shiftCl | shiftx =>
    simp only [reduceExec, Option.some.injEq] at h; subst h; rfl
  | rorx32 => simp only [reduceExec, execRorx32] at h; split at h <;> cases h; rfl
  | rorx => simp only [reduceExec, execRorx] at h; split at h <;> cases h; rfl
  | shld => simp only [reduceExec, execShld] at h; split at h <;> cases h; rfl
  | btr => simp only [reduceExec, execBtr] at h; split at h <;> cases h; rfl
  | mulx =>
    simp only [reduceExec, execMulx] at h; split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | adcx =>
    simp only [reduceExec, execAdcx] at h; split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | adox =>
    simp only [reduceExec, execAdox] at h; split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | cmov =>
    obtain ⟨_, c, -, -, rfl⟩ := Taint.execCmov_some h; cases c <;> rfl
  | push | pop | alloc | free | callr => simp only [reduceExec, reduceCtorEq] at h

theorem pushRegs_mxcsr (s : State) (rs : List Reg) : (pushRegs s rs).mxcsr = s.mxcsr := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem popReg_mxcsr (s : State) (r : Reg) (k : Nat) : (popReg s r k).mxcsr = s.mxcsr := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

/-- A frame's push and pop keep MXCSR. -/
theorem push_mxcsr {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) : s₁.mxcsr = s.mxcsr := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  case push => split at h <;> cases h; exact pushRegs_mxcsr _ _
  case alloc => split at h <;> cases h; rfl

theorem pop_mxcsr {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') : s'.mxcsr = s₂.mxcsr := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  case pop => split at h <;> cases h; exact popReg_mxcsr _ _ _
  case free => split at h <;> cases h; rfl

theorem execBlock_mxcsr {is : List Instr} (hc : ∀ i ∈ is, loadsMxcsr i = false)
    {s s' : State} {t : List Leak} (h : execBlock isa is s = some (s', t)) : s'.mxcsr = s.mxcsr := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) h2,
      exec_mxcsr (hc i (List.mem_cons_self ..)) he]

/-- Code that never loads MXCSR keeps it. -/
theorem Exec.mxcsr {c : Prog isa} (hc : ∀ i ∈ instrs c, loadsMxcsr i = false)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : s'.mxcsr = s.mxcsr := by
  induction h with
  | block h => exact execBlock_mxcsr hc h
  | seq _ _ ih₁ ih₂ =>
    rw [ih₂ fun i hi => hc i (List.mem_append_right _ hi), ih₁ fun i hi => hc i (List.mem_append_left _ hi)]
  | iteT _ _ ih => exact ih fun i hi => hc i (List.mem_append_left _ hi)
  | iteF _ _ ih => exact ih fun i hi => hc i (List.mem_append_right _ hi)
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc, ih₁ hc]
  | frame hp _ hq ih =>
    rw [pop_mxcsr hq, ih fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi)),
      push_mxcsr hp]
  | call hc₁ _ hr ih =>
    simp only [isa, call, Option.some.injEq] at hc₁
    simp only [isa, ret] at hr
    split at hr <;> cases hr
    subst hc₁
    exact ih hc
  | icall _ hc₁ _ hr ih =>
    simp only [isa, call, Option.some.injEq] at hc₁
    simp only [isa, ret] at hr
    split at hr <;> cases hr
    subst hc₁
    exact ih fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
  | icallNext _ _ _ ih => exact ih fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_right _ hi))

/-- Two runs of `c` along the same trace from the same MXCSR leave the same
MXCSR: what a caller needs of a callee to relate the MXCSR of its two runs
after the call, now that MXCSR is public (`abi.pub`). -/
def MxDet (c : Prog isa) : Prop :=
  ∀ s₁ s₂ t s₁' s₂', Exec isa c s₁ t s₁' → Exec isa c s₂ t s₂' → s₁.mxcsr = s₂.mxcsr →
    s₁'.mxcsr = s₂'.mxcsr

/-- Code that never loads MXCSR keeps it, so leaves the same in two runs from
the same (the kernel checks `hc` by evaluating the code). -/
theorem MxDet.of_noLoad {c : Prog isa} (hc : c.allInstrs (fun i => !loadsMxcsr i) = true) : MxDet c := by
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  intro _ _ _ _ _ e₁ e₂ hm
  rw [Exec.mxcsr (fun i hi => by simpa using hc i hi) e₁, Exec.mxcsr (fun i hi => by simpa using hc i hi) e₂,
    hm]

/-- `Q`, from `Q` given the entry's MXCSR, for code that never loads MXCSR. -/
theorem WP.of_mx {c : Prog isa} (hc : c.allInstrs (fun i => !loadsMxcsr i) = true) {s : State}
    {Q : State → Prop} (h : WP isa c s fun t => t.mxcsr = s.mxcsr → Q t) : WP isa c s Q := by
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  obtain ⟨t, s', e, q⟩ := h
  exact ⟨t, s', e, q (Exec.mxcsr (fun i hi => by simpa using hc i hi) e)⟩

/-- Code that never loads MXCSR ends with its entry's. -/
theorem WP.mxcsr {c : Prog isa} (hc : c.allInstrs (fun i => !loadsMxcsr i) = true) {s : State}
    {Q : State → Prop} (h : WP isa c s Q) : WP isa c s fun t => Q t ∧ t.mxcsr = s.mxcsr := by
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  obtain ⟨t, s', e, q⟩ := h
  exact ⟨t, s', e, q, Exec.mxcsr (fun i hi => by simpa using hc i hi) e⟩

/-- The calling-convention obligations other than MXCSR's: the callee-saved
registers and the return address. -/
def gprPreserved (s s' : State) : Prop :=
  (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
  s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64

/-- The calling-convention obligations of code that never loads MXCSR (the
kernel checks `hc` by evaluating the code), from the others. -/
theorem abiPreserved_of_exec {c : Prog isa} (hc : c.allInstrs (fun i => !loadsMxcsr i) = true)
    {s s' : State} {t : List Leak} (he : Exec isa c s t s') (h : gprPreserved s s') :
    abiPreserved s s' := by
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  exact ⟨h.1, h.2, by rw [Exec.mxcsr (fun i hi => by simpa using hc i hi) he]⟩

/-- `WP.mono`, knowing that code that never loads MXCSR keeps it (the kernel
checks `hc` by evaluating the code). -/
theorem WP.mono_mx {c : Prog isa} (hc : c.allInstrs (fun i => !loadsMxcsr i) = true) {s : State}
    {Q R : State → Prop} (h : WP isa c s Q) (hq : ∀ s', Q s' → s'.mxcsr = s.mxcsr → R s') :
    WP isa c s R := by
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  obtain ⟨t, s', he, hQ⟩ := h
  exact ⟨t, s', he, hq s' hQ (Exec.mxcsr (fun i hi => by simpa using hc i hi) he)⟩

end VG.X86_64
