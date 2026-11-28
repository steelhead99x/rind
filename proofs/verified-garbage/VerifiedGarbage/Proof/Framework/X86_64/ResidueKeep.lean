module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
public import VerifiedGarbage.Impl.Scrub.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# What code without AVX or AVX-512 instructions keeps (x86-64)

`Instr.vecLevel` classifies the instructions of the model by the vector
state and MXCSR they may write: 0 for those that write none of bits 511:128
of `zmm0`–`zmm15`, nor `zmm16`–`zmm31`, nor MXCSR (the scalar and legacy SSE
instructions, and every store); 1 for those that may also write bits 511:128
of `zmm0`–`zmm15` (the VEX-encoded ones, and the EVEX ones of those
registers); 2 for the rest (`ldmxcsr`, and the EVEX instructions that may
write `zmm16`–`zmm31`). Code whose instructions are all at a level `l` of at
most 1 keeps what that level does not write (`Exec.vecKeep`), through its
frames and calls.

`Instr.vecLevelR` is the level of the vector registers alone: `vecLevel`, but
`ldmxcsr`, which writes only MXCSR, at level 0. Code whose instructions are
all at a `vecLevelR` of at most 1 keeps the vector state that level does not
write (`Exec.vecKeep0R`, `Exec.vecKeep1R`), whatever it does to MXCSR.
-/

@[expose] public section

namespace VG.X86_64.Residue

open VG.X86_64

/-- What an instruction of level `l` keeps. -/
def VKeep (l : Nat) (s s' : State) : Prop :=
  s'.ymmH = s.ymmH ∧ s'.zmmHiH = s.zmmHiH ∧ s'.mxcsr = s.mxcsr ∧
    (l = 0 → s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi)

/-- Every result in `o` satisfies `P`. -/
def Pres (P : State → Prop) (o : Option State) : Prop := ∀ x, o = some x → P x

theorem Pres.none' {P : State → Prop} : Pres P none := fun _ h => by cases h
theorem Pres.some' {P : State → Prop} {x : State} (h : P x) : Pres P (some x) :=
  fun _ e => by cases e; exact h
theorem Pres.map' {α : Type} {P : State → Prop} {o : Option α} {f : α → State} (h : ∀ a, P (f a)) :
    Pres P (o.map f) := fun x e => by
  obtain ⟨a, _, rfl⟩ := Option.map_eq_some_iff.mp e; exact h a
theorem Pres.bind' {α : Type} {P : State → Prop} {o : Option α} {f : α → Option State}
    (h : ∀ a, Pres P (f a)) : Pres P (o.bind f) := fun x e => by
  obtain ⟨a, _, e⟩ := Option.bind_eq_some_iff.mp e; exact h a x e

local macro "k0" : term => `(⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩)
local macro "k1" : term => `(⟨rfl, rfl, rfl, fun h => absurd h (by decide)⟩)
local macro "kk" : tactic => `(tactic| first | exact k0 | exact k1)
local macro "pres_leaf" : tactic => `(tactic| first
  | exact Pres.none'
  | (apply Pres.some'; kk)
  | (apply Pres.map'; intro _; kk)
  | (apply Pres.map'; intro _; split <;> kk))
local syntax "pres_go" : tactic
macro_rules
  | `(tactic| pres_go) => `(tactic| first
    | pres_leaf
    | (apply Pres.bind'; intro _; pres_go)
    | (split <;> pres_go))

theorem exec_pres (i : Instr) (s : State) (hi : i.vecLevel ≤ 1) :
    Pres (VKeep i.vecLevel s) (exec i s) := by
  cases i <;> simp only [Instr.vecLevel, Nat.reduceLeDiff] at hi ⊢
  case vop op => simp only [reduceExec]; rw [Taint.VOp.exec_eq]; exact Pres.some' k1
  case zop op => simp only [reduceExec]; rw [Taint.ZOp.exec_eq]; exact Pres.some' k1
  case xop op => simp only [reduceExec]; rw [Taint.XOp.exec_eq]; exact Pres.some' k0
  case vmovdquLoad len _ _ | vmovdquStore len _ _ | vbinLoad _ len _ _ _ =>
    cases len <;> simp only [reduceExec, State.store128, State.store256] <;> pres_go
  all_goals simp only [reduceExec, execAlu, execAluW, execAlu32, execShift32, execShift, execRorx32,
      execRorx, execShld, execBtr, execMulx, execAdcx, execAdox, execCmov, State.store64,
      State.store32, State.store8, State.store16, State.store128, State.store256, State.store512,
      State.storeMasked512, State.storeMasked512B]
  all_goals pres_go

theorem exec_vkeep {i : Instr} {s s' : State} (hi : i.vecLevel ≤ 1) (h : exec i s = some s') :
    VKeep i.vecLevel s s' :=
  exec_pres i s hi s' h

/-- The parts of the state that code of level 0 keeps. -/
def vk0 (s : State) := (s.ymmH, s.zmmHiH, s.mxcsr, s.ymmHi, s.zmmHi)
/-- The parts of the state that code of level 1 keeps. -/
def vk1 (s : State) := (s.ymmH, s.zmmHiH, s.mxcsr)

theorem pushRegs_vk0 (s : State) (rs : List Reg) : vk0 (pushRegs s rs) = vk0 s := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem popReg_vk0 (s : State) (r : Reg) (k : Nat) : vk0 (popReg s r k) = vk0 s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

theorem push_vk0 {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) : vk0 s₁ = vk0 s := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  case push rs => split at h <;> cases h; exact pushRegs_vk0 s rs
  case alloc => split at h <;> cases h; rfl

theorem pop_vk0 {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') : vk0 s' = vk0 s₂ := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  case pop r k => split at h <;> cases h; exact popReg_vk0 s₂ r k
  case free => split at h <;> cases h; rfl

theorem callret_vk0 {s s₁ s₂ s' : State} (hc : isa.call s = some s₁) (hr : isa.ret s₁ s₂ = some s')
    (hb : vk0 s₂ = vk0 s₁) : vk0 s' = vk0 s := by
  simp only [isa, call, Option.some.injEq] at hc; subst hc
  simp only [isa, ret] at hr; split at hr <;> cases hr
  exact hb

theorem vk1_of_vk0 {a b : State} (h : vk0 a = vk0 b) : vk1 a = vk1 b := by
  simp only [vk0, vk1, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Code of level 0 keeps bits 511:128 of every vector register and MXCSR. -/
theorem Exec.vecKeep0 {c : Prog isa} (hc : ∀ i ∈ instrs c, i.vecLevel = 0) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : vk0 s' = vk0 s :=
  Exec.keep (fun s : State => vk0 s) (ok := fun i : Instr => i.vecLevel = 0)
    (fun {i s s'} hi he => by
      have k := exec_vkeep (by omega_using [hi]) he
      rw [hi] at k
      simp only [vk0, k.1, k.2.1, k.2.2.1, (k.2.2.2 rfl).1, (k.2.2.2 rfl).2])
    (fun _ hp hq hb => by rw [pop_vk0 hq, hb, push_vk0 hp]) hc
    (.inr fun _ _ _ _ hc hr hb => callret_vk0 hc hr hb) h

/-- Code of level at most 1 keeps `zmm16`–`zmm31` and MXCSR. -/
theorem Exec.vecKeep1 {c : Prog isa} (hc : ∀ i ∈ instrs c, i.vecLevel ≤ 1) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : vk1 s' = vk1 s :=
  Exec.keep (fun s : State => vk1 s) (ok := fun i : Instr => i.vecLevel ≤ 1)
    (fun {i s s'} hi he => by
      have k := exec_vkeep hi he
      simp only [vk1, k.1, k.2.1, k.2.2.1])
    (fun _ hp hq hb => by rw [vk1_of_vk0 (pop_vk0 hq), hb, vk1_of_vk0 (push_vk0 hp)]) hc
    (.inr fun _ _ _ _ hc hr hb => by
      simp only [isa, call, Option.some.injEq] at hc; subst hc
      simp only [isa, ret] at hr; split at hr <;> cases hr
      exact hb) h

theorem pushRegs_xmm (s : State) (rs : List Reg) : (pushRegs s rs).xmm = s.xmm := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem popReg_xmm (s : State) (r : Reg) (k : Nat) : (popReg s r k).xmm = s.xmm := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

private theorem writesVec_eq (i : Instr) : Impl.Scrub.X86_64.writesVec i = KeepReg.writesVec i := by
  cases i <;> rfl

/-- Code that writes no vector register keeps the SSE registers. -/
theorem Exec.xmmKeep {c : Prog isa} (hc : ∀ i ∈ instrs c, Impl.Scrub.X86_64.writesVec i = false)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : s'.xmm = s.xmm :=
  Exec.keep (fun s : State => s.xmm) (ok := fun i : Instr => Impl.Scrub.X86_64.writesVec i = false)
    (fun {i s s'} hi he => KeepReg.exec_xmm (by rw [← writesVec_eq]; exact hi) he)
    (fun {i j s s₁ s₂ s'} _ hp hq hb => by
      have e₁ : s₁.xmm = s.xmm := by
        cases i <;> simp only [isa, push, reduceCtorEq] at hp
        case push rs => split at hp <;> cases hp; exact pushRegs_xmm s rs
        case alloc => split at hp <;> cases hp; rfl
      have e₂ : s'.xmm = s₂.xmm := by
        cases j <;> simp only [isa, pop, reduceCtorEq] at hq
        case pop r k => split at hq <;> cases hq; exact popReg_xmm s₂ _ _
        case free => split at hq <;> cases hq; rfl
      show s'.xmm = s.xmm
      rw [e₂, show s₂.xmm = s₁.xmm from hb, e₁]) hc
    (.inr fun _ _ _ _ hc hr hb => by
      simp only [isa, call, Option.some.injEq] at hc; subst hc
      simp only [isa, ret] at hr; split at hr <;> cases hr
      exact hb) h

/-- An instruction that writes no vector register and is at level at most
1 is at level 0. -/
theorem vecLevel_of_writesVec {i : Instr} (hw : Impl.Scrub.X86_64.writesVec i = false) (hl : i.vecLevel ≤ 1) :
    i.vecLevel = 0 := by
  cases i <;> simp_all [Impl.Scrub.X86_64.writesVec, Instr.vecLevel]

/-! ## The vector registers alone -/

theorem loadsMxcsr_eq {i : Instr} (h : loadsMxcsr i = true) : ∃ m, i = .ldmxcsr m := by
  cases i <;> simp_all [loadsMxcsr]

theorem vecLevel_of_loads {i : Instr} (h : loadsMxcsr i = true) : i.vecLevel = 2 := by
  obtain ⟨m, rfl⟩ := loadsMxcsr_eq h; rfl

theorem vecLevelR_le (i : Instr) : i.vecLevelR ≤ i.vecLevel := by
  unfold Instr.vecLevelR; split <;> omega_using []

/-- An instruction of level at most 1 does not load MXCSR. -/
theorem noLoad_of_vecLevel {i : Instr} (h : i.vecLevel ≤ 1) : loadsMxcsr i = false := by
  cases hl : loadsMxcsr i
  · rfl
  · rw [vecLevel_of_loads hl] at h; omega

/-- What an instruction of `vecLevelR` at most 1 keeps. -/
theorem exec_vkeepR {i : Instr} {s s' : State} (hi : i.vecLevelR ≤ 1) (h : exec i s = some s') :
    s'.ymmH = s.ymmH ∧ s'.zmmHiH = s.zmmHiH ∧ (i.vecLevelR = 0 → s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi) := by
  cases hl : loadsMxcsr i
  · have e : i.vecLevelR = i.vecLevel := by simp only [Instr.vecLevelR, hl, Bool.false_eq_true, ↓reduceIte]
    rw [e] at hi ⊢
    have k := exec_vkeep hi h
    exact ⟨k.1, k.2.1, k.2.2.2⟩
  · obtain ⟨m, rfl⟩ := loadsMxcsr_eq hl
    simp only [reduceExec, Option.bind_eq_some_iff] at h
    obtain ⟨v, -, h⟩ := h
    split at h
    · cases h; exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
    · cases h

/-- The vector state that code of `vecLevelR` 0 keeps. -/
def vk0R (s : State) := (s.ymmH, s.zmmHiH, s.ymmHi, s.zmmHi)
/-- The vector state that code of `vecLevelR` at most 1 keeps. -/
def vk1R (s : State) := (s.ymmH, s.zmmHiH)

theorem vk0R_of_vk0 {a b : State} (h : vk0 a = vk0 b) : vk0R a = vk0R b := by
  simp only [vk0, vk0R, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem vk1R_of_vk0 {a b : State} (h : vk0 a = vk0 b) : vk1R a = vk1R b := by
  simp only [vk0, vk1R, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, h.2.1⟩

/-- Code of `vecLevelR` 0 keeps bits 511:128 of every vector register. -/
theorem Exec.vecKeep0R {c : Prog isa} (hc : ∀ i ∈ instrs c, i.vecLevelR = 0) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : vk0R s' = vk0R s :=
  Exec.keep (fun s : State => vk0R s) (ok := fun i : Instr => i.vecLevelR = 0)
    (fun {i s s'} hi he => by
      have k := exec_vkeepR (by omega_using [hi]) he
      simp only [vk0R, k.1, k.2.1, (k.2.2 hi).1, (k.2.2 hi).2])
    (fun _ hp hq hb => by rw [vk0R_of_vk0 (pop_vk0 hq), hb, vk0R_of_vk0 (push_vk0 hp)]) hc
    (.inr fun _ _ _ _ hc hr hb => by
      simp only [isa, call, Option.some.injEq] at hc; subst hc
      simp only [isa, ret] at hr; split at hr <;> cases hr
      exact hb) h

/-- Code of `vecLevelR` at most 1 keeps `zmm16`–`zmm31`. -/
theorem Exec.vecKeep1R {c : Prog isa} (hc : ∀ i ∈ instrs c, i.vecLevelR ≤ 1) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : vk1R s' = vk1R s :=
  Exec.keep (fun s : State => vk1R s) (ok := fun i : Instr => i.vecLevelR ≤ 1)
    (fun {i s s'} hi he => by
      have k := exec_vkeepR hi he
      simp only [vk1R, k.1, k.2.1])
    (fun _ hp hq hb => by rw [vk1R_of_vk0 (pop_vk0 hq), hb, vk1R_of_vk0 (push_vk0 hp)]) hc
    (.inr fun _ _ _ _ hc hr hb => by
      simp only [isa, call, Option.some.injEq] at hc; subst hc
      simp only [isa, ret] at hr; split at hr <;> cases hr
      exact hb) h

/-- `vecLevel_of_writesVec`, for `vecLevelR`. -/
theorem vecLevelR_of_writesVec {i : Instr} (hw : Impl.Scrub.X86_64.writesVec i = false) (hl : i.vecLevelR ≤ 1) :
    i.vecLevelR = 0 := by
  unfold Instr.vecLevelR at hl ⊢
  split
  · rfl
  · rename_i h
    simp only [h, Bool.false_eq_true, ↓reduceIte] at hl
    exact vecLevel_of_writesVec hw hl

end VG.X86_64.Residue
