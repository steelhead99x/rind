module

public import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Calls (x86-64)

A call (`Code.call`) stores its return address at `rsp - 8` and runs the
called function from there (`State.callEntry`). Code that never writes `rsp`
itself changes memory only within the regions it may write and the return
addresses of its calls, within `8 * depth` bytes below `rsp`
(`Exec.frameSp`). `WP.call` runs a call of verified code from the callee's
`Verified` proof, as `WP.inline` does for inlined code.
-/

@[expose] public section

namespace VG

/-- How deeply calls nest in `c`. -/
def Code.depth {I C : Type} : Code I C → Nat
  | .block _ => 0
  | .seq a b => max a.depth b.depth
  | .ite _ t e => max t.depth e.depth
  | .loop b _ => b.depth
  | .call _ b => b.depth + 1
  | .frame _ b _ => b.depth
  | .icall _ _ b n => max (b.depth + 1) n.depth

end VG

namespace VG.X86_64

/-- The state a called function starts in: `rsp` moved down by 8 and the
return address (the next of the state's unknowns) stored there. -/
def State.callEntry (s : State) : State :=
  { s.setReg .rsp (s.gpr .rsp - 8) with
    mem := s.mem.writeW (s.gpr .rsp - 8) (s.unknowns 0)
    unknowns := fun n => s.unknowns (n + 1) }

theorem call_callEntry (s : State) : isa.call s = some s.callEntry := rfl

@[simp] theorem State.callEntry_rd (s : State) : s.callEntry.rd = s.rd := rfl
@[simp] theorem State.callEntry_wr (s : State) : s.callEntry.wr = s.wr := rfl
@[simp] theorem State.callEntry_mxcsr (s : State) : s.callEntry.mxcsr = s.mxcsr := rfl
@[simp] theorem State.callEntry_rsp (s : State) : s.callEntry.gpr .rsp = s.gpr .rsp - 8 := by
  simp [State.callEntry, State.setReg]
theorem State.callEntry_gpr (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r := by
  simp [State.callEntry, State.setReg, h]
theorem State.callEntry_mem (s : State) :
    s.callEntry.mem = s.mem.writeW (s.gpr .rsp - 8) (s.unknowns 0) := rfl

/-- The `n` bytes below `sp`. -/
abbrev below (sp : Addr) (n : Nat) : Region := ⟨sp - BitVec.ofNat 64 n, n⟩

theorem ofNat_split {a b : Nat} (hab : a ≤ b) :
    BitVec.ofNat 64 b = BitVec.ofNat 64 a + BitVec.ofNat 64 (b - a) := by
  rw [← BitVec.ofNat_add]; congr 1; omega_arith

theorem below_sub {sp : Addr} {a b : Nat} (hab : a ≤ b) (hb : b < 2 ^ 64) :
    Region.Sub (below sp a) (below sp b) := by
  exact Offset.below_mono sp hab hb

/-- The return address of a call from `sp` is in the `n ≥ 8` bytes below it. -/
theorem below_call (sp : Addr) {n : Nat} (h₁ : 8 ≤ n) (h₂ : n < 2 ^ 64) :
    (below sp n).Contains (sp - 8) 8 := by
  simp only [Region.Contains]
  rw [show sp - 8 - (sp - BitVec.ofNat 64 n) = BitVec.ofNat 64 (n - 8) from
    Offset.sub_ofNat_sub_sub_ofNat sp (a := 8) h₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- The stack a function called from `sp` uses is below the return address. -/
theorem below_callee (sp : Addr) (n : Nat) : Region.Sub (below (sp - 8) n) (below sp (n + 8)) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (sp - BitVec.ofNat 64 (n + 8)) = x - (sp - 8 - BitVec.ofNat 64 n) by
    rw [BitVec.sub_sub (sp : Addr) 8, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 n)]; rfl]
  omega_arith

/-- No instruction writes `rsp`. -/
abbrev NoSp (c : Prog isa) : Prop := ∀ i ∈ instrs c, Taint.clobbers i .rsp = false

theorem Frame.below_mono {wr : List Region} {sp : Addr} {a b : Nat} {m m' : Mem}
    (h : Frame (wr ++ [below sp a]) m m') (hab : a ≤ b) (hb : b < 2 ^ 64) :
    Frame (wr ++ [below sp b]) m m' :=
  Frame.sub h fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub hab hb⟩

/-- Code that never writes `rsp` changes memory only within the regions it
may write, and within `8 * depth` bytes below `rsp` (its calls' return
addresses). -/
theorem Exec.frameSp {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hc : NoSp c) (hd : 8 * c.depth + 8 < 2 ^ 64) :
    Frame (s.wr ++ [below (s.gpr .rsp) (8 * c.depth)]) s.mem s'.mem := by
  induction h with
  | block h => exact Frame.mono (execBlock_regions h).2.2 fun r hr => List.mem_append_left _ hr
  | @seq c₁ c₂ _ s₂ _ _ _ h₁ _ ih₁ ih₂ =>
    have hc₁ : NoSp c₁ := fun i hi => hc i (List.mem_append_left _ hi)
    have hc₂ : NoSp c₂ := fun i hi => hc i (List.mem_append_right _ hi)
    simp only [Code.depth] at hd ⊢
    have f₁ := Frame.below_mono (ih₁ hc₁ (by omega_arith)) (b := 8 * max c₁.depth c₂.depth) (by omega_arith)
      (by omega_arith)
    have f₂ := Frame.below_mono (ih₂ hc₂ (by omega_arith)) (b := 8 * max c₁.depth c₂.depth) (by omega_arith)
      (by omega_arith)
    rw [(Exec.rdwr h₁).2, Exec.gpr hc₁ h₁] at f₂
    exact Frame.trans f₁ f₂
  | iteT _ _ ih =>
    simp only [Code.depth] at hd ⊢
    exact Frame.below_mono (ih (fun i hi => hc i (List.mem_append_left _ hi)) (by omega_arith)) (by omega_arith)
      (by omega_arith)
  | iteF _ _ ih =>
    simp only [Code.depth] at hd ⊢
    exact Frame.below_mono (ih (fun i hi => hc i (List.mem_append_right _ hi)) (by omega_arith)) (by omega_arith)
      (by omega_arith)
  | loopExit _ _ ih => exact ih hc hd
  | @loopNext body _ _ _ _ _ _ h₁ _ _ ih₁ ih₂ =>
    have f₂ := ih₂ hc hd
    have hcb : NoSp body := hc
    rw [(Exec.rdwr h₁).2, Exec.gpr hcb h₁] at f₂
    exact Frame.trans (ih₁ hc hd) f₂
  | @frame i _ _ _ _ _ _ _ hp =>
    -- A frame's push writes `rsp`.
    have hi := hc i (List.mem_cons_self ..)
    cases i <;> simp only [isa, push, reduceCtorEq] at hp
    all_goals simp [Taint.clobbers] at hi
  | @call _ b s₀ s₁ s₂ s₃ _ hc₁ hb hr ih =>
    simp only [Code.depth] at hd ⊢
    have e₁ : s₁ = s₀.callEntry := (Option.some.inj ((call_callEntry s₀).symm.trans hc₁)).symm
    subst e₁
    have hm : s₃.mem = s₂.mem := by
      simp only [isa, ret] at hr; split at hr <;> cases hr; rfl
    have f₀ : Frame (s₀.wr ++ [below (s₀.gpr .rsp) (8 * (b.depth + 1))]) s₀.mem s₀.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_call _ (by omega_arith) (by omega_arith))
    have f₁ := ih hc (by omega_arith)
    simp only [State.callEntry_wr, State.callEntry_rsp] at f₁
    have f₁' : Frame (s₀.wr ++ [below (s₀.gpr .rsp) (8 * (b.depth + 1))]) s₀.callEntry.mem s₂.mem :=
      Frame.sub f₁ fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr
          refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          rw [show 8 * (b.depth + 1) = 8 * b.depth + 8 by omega_arith]
          exact below_callee _ _
    rw [hm]; exact Frame.trans f₀ f₁'
  | @icall _ _ b nx s₀ s₁ s₂ s₃ _ _ hc₁ hb hr ih =>
    have hcb : NoSp b := fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
    have hd' : 8 * b.depth + 8 + 8 < 2 ^ 64 := by simp only [Code.depth] at hd; omega_arith
    have e₁ : s₁ = s₀.callEntry := (Option.some.inj ((call_callEntry s₀).symm.trans hc₁)).symm
    subst e₁
    have hm : s₃.mem = s₂.mem := by
      simp only [isa, ret] at hr; split at hr <;> cases hr; rfl
    have f₀ : Frame (s₀.wr ++ [below (s₀.gpr .rsp) (8 * (b.depth + 1))]) s₀.mem s₀.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_call _ (by omega_arith) (by omega_arith))
    have f₁ := ih hcb (by omega_arith)
    simp only [State.callEntry_wr, State.callEntry_rsp] at f₁
    have f₁' : Frame (s₀.wr ++ [below (s₀.gpr .rsp) (8 * (b.depth + 1))]) s₀.callEntry.mem s₂.mem :=
      Frame.sub f₁ fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr
          refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          rw [show 8 * (b.depth + 1) = 8 * b.depth + 8 by omega_arith]
          exact below_callee _ _
    rw [hm]
    exact Frame.below_mono (Frame.trans f₀ f₁') (by simp only [Code.depth]; omega_arith) (by omega_arith)
  | @icallNext i nm bd n' b' nn _ _ _ _ _ _ _ ih =>
    have hcn : NoSp (.icall i n' b' nn) :=
      fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_right _ hi))
    have hle : (Code.icall i n' b' nn).depth ≤ (Code.icall i nm bd (.icall i n' b' nn)).depth :=
      Nat.le_max_right _ _
    exact Frame.below_mono (ih hcn (by omega_arith)) (by omega_arith) (by omega_arith)

/-- Calling verified code: from a state `s` such that, once the call has
stored its return address (`State.callEntry`), the callee's precondition
holds with its permissions narrowed to `rd` and `wr`, the call returns in a
state that has the permissions of `s`, its callee-saved registers and `rsp`,
and every register the callee's instructions never write; that differs from
`s` in memory only within `wr` and the stack below `rsp` that the call
uses; and whose memory and registers (`rsp` aside) are those of a state
satisfying the callee's postcondition; and with the bits of MXCSR that
`abiPreserved` keeps (a callee may load MXCSR, and restore it). -/
theorem WP.call_mx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : 8 * c.depth + 16 < 2 ^ 64)
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = s.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (s.callEntry.withRegions rd wr) s₂) →
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 → Q s') :
    WP isa (.call n c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr] at hr hwr
  have hf := Exec.frameSp he hsp (by omega_arith)
  simp only [State.withRegions_wr, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_rsp] at hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions] at he'
  rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at he'
  let s₂ := s₁.withRegions s.rd s.wr
  have hs₂ : s₂ = s₁.withRegions s.rd s.wr := rfl
  have hsp₂ : s₂.gpr .rsp = s.gpr .rsp - 8 := by
    rw [hs₂, State.withRegions_gpr, habi.1 .rsp (by simp [calleeSaved])]; simp
  have hret : isa.ret s.callEntry s₂ = some (s₂.setReg .rsp (s₂.gpr .rsp + 8)) := by
    simp only [isa, ret]
    refine ite_eq_left ⟨by rw [hsp₂, State.callEntry_rsp], ?_⟩
    have := habi.2.1
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp] at this
    rw [hsp₂, State.callEntry_rsp]; exact this
  have hrsp : (s₂.setReg .rsp (s₂.gpr .rsp + 8)).gpr .rsp = s.gpr .rsp := by
    simp only [State.setReg, ite_true, hsp₂]; exact BitVec.sub_add_cancel _ _
  have hkeep : ∀ r, r ≠ .rsp → (s₂.setReg .rsp (s₂.gpr .rsp + 8)).gpr r = s₂.gpr r :=
    fun r h => by simp [State.setReg, h]
  refine ⟨_, _, .call (call_callEntry s) he' hret, hQ _ rfl rfl (fun r hr' => ?_) ?_ (fun r h => ?_)
    ⟨s₁, rfl, fun r h => (hkeep r h).symm, hpost⟩ habi.2.2⟩
  · by_cases h : r = .rsp
    · subst h; exact hrsp
    · rw [hkeep r h, hs₂, State.withRegions_gpr, habi.1 r hr', State.withRegions_gpr,
        State.callEntry_gpr _ h]
  · -- The return address, then the callee.
    have f₀ : Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.mem s.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_call _ (by omega_arith) (by omega_arith))
    have f₁ : Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.callEntry.mem s₁.mem :=
      Frame.sub hf fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr
          refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          rw [show 8 * (c.depth + 1) = 8 * c.depth + 8 by omega_arith]
          exact below_callee _ _
    exact Frame.trans f₀ f₁
  · by_cases hrs : r = .rsp
    · subst hrs; exact hrsp
    · rw [hkeep r hrs, Exec.gpr h he', State.callEntry_gpr _ hrs]

/-- `WP.call`, without what it says of MXCSR. -/
theorem WP.call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : 8 * c.depth + 16 < 2 ^ 64)
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = s.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (s.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) s Q :=
  WP.call_mx hv hsp hd hpre hc hw fun s' h₁ h₂ h₃ h₄ h₅ h₆ _ => hQ s' h₁ h₂ h₃ h₄ h₅ h₆

end VG.X86_64
