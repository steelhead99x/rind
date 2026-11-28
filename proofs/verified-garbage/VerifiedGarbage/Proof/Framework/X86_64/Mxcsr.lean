module
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.Taint

import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Depth

/-!
# x86-64: code that restores MXCSR

Code that loads MXCSR (for Intel's MCDT prologue: see "MCDT" in
`TCB/X86_64/Isa.lean`) keeps its control bits if it first saves MXCSR in a
register (`mxcsrSave`, `r11` unless code needs it), never writes that
register, and loads it back from it last (`mxcsrRestore`). `ctlOk` checks that every load of MXCSR by some code, and
by the functions it calls, is between such a pair, and `abiPreserved_of_ctl`
extends `abiPreserved_of_exec` to such code, whatever MXCSR held on entry.

`mxClass` checks more of such code: that MXCSR on return is a function of
MXCSR on entry alone (`MxC.app`), the same on every path (`Exec.mxClass`):
MXCSR itself if the code never loads it, and otherwise MXCSR but for its
reserved bits, if every path through it ends with such a pair. Two runs
from the same MXCSR then return with the same MXCSR, whatever else differs.
-/

@[expose] public section

namespace VG.X86_64

/-- Whether `.seq a b` is `mxcsrSave m r`, then code that never writes `r`,
then `mxcsrRestore m' r`. -/
noncomputable def restores (a b : Prog isa) : Bool :=
  match a, b with
  | .block is, .seq mid (.block js) =>
    match saveOp is, restoreOp js with
    | some (m, r), some m' =>
      is == mxcsrSave m r && js == mxcsrRestore m' r && mid.allInstrs fun i => !Taint.clobbers i r
    | _, _ => false
  | _, _ => false

/-- Whether every load of MXCSR by `c`, and by the functions it calls, is
between `mxcsrSave` and `mxcsrRestore` (`restores`). -/
noncomputable def ctlOk : Prog isa → Bool
  | .block is => KList.all is fun i => !loadsMxcsr i
  | .seq a b => restores a b || (ctlOk a && ctlOk b)
  | .ite _ t e => ctlOk t && ctlOk e
  | .loop b _ => ctlOk b
  | .call _ b => ctlOk b
  | .frame i b j => !loadsMxcsr i && ctlOk b && !loadsMxcsr j
  | .icall i _ b n => !loadsMxcsr i && ctlOk b && ctlOk n

/-- A check that implies `ctlOk` and composes like `Code.allInstrs`: `c`
itself never loads MXCSR, and the functions it calls satisfy `ctlOk`. -/
noncomputable def ctlC : Prog isa → Bool
  | .block is => KList.all is fun i => !loadsMxcsr i
  | .seq a b => ctlC a && ctlC b
  | .ite _ t e => ctlC t && ctlC e
  | .loop b _ => ctlC b
  | .call _ b => ctlOk b
  | .frame i b j => !loadsMxcsr i && ctlC b && !loadsMxcsr j
  | .icall i _ b n => !loadsMxcsr i && ctlOk b && ctlC n

theorem ctlOk_of_ctlC {c : Prog isa} (h : ctlC c = true) : ctlOk c = true := by
  induction c with
  | block _ => exact h
  | seq _ _ iha ihb =>
    simp only [ctlC, Bool.and_eq_true] at h
    simp only [ctlOk, iha h.1, ihb h.2, Bool.and_self, Bool.or_true]
  | ite _ _ _ iht ihe =>
    simp only [ctlC, Bool.and_eq_true] at h
    simp only [ctlOk, iht h.1, ihe h.2, Bool.and_self]
  | loop _ _ ih => exact ih h
  | call _ _ _ => exact h
  | frame _ _ _ ih =>
    simp only [ctlC, Bool.and_eq_true] at h
    simp only [ctlOk, h.1.1, h.2, ih h.1.2, Bool.and_self]
  | icall _ _ _ _ _ ihn =>
    simp only [ctlC, Bool.and_eq_true] at h
    simp only [ctlOk, h.1.1, h.1.2, ihn h.2, Bool.and_self]

/-- Code that never loads MXCSR satisfies `ctlOk`. -/
theorem ctlOk_of_noLoad {c : Prog isa} (h : c.allInstrs (fun i => !loadsMxcsr i) = true) : ctlOk c = true := by
  induction c with
  | block is =>
    rw [Code.allInstrs_eq] at h
    exact (KList.all_eq _ _).trans h
  | seq _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlOk, iha h.1, ihb h.2, Bool.and_self, Bool.or_true]
  | ite _ _ _ iht ihe =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlOk, iht h.1, ihe h.2, Bool.and_self]
  | loop _ _ ih => exact ih h
  | call _ _ ih => exact ih h
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlOk, h.1.1, h.2, ih h.1.2, Bool.and_self]
  | icall _ _ _ _ ihb ihn =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlOk, h.1.1, ihb h.1.2, ihn h.2, Bool.and_self]

theorem ctlOk_seq_of {a b : Prog isa} (ha : ctlOk a = true) (hb : ctlOk b = true) : ctlOk (.seq a b) = true := by
  simp only [ctlOk, ha, hb, Bool.and_self, Bool.or_true]

theorem ctlOk_ite_of {c : Cond} {a b : Prog isa} (ha : ctlOk a = true) (hb : ctlOk b = true) :
    ctlOk (.ite c a b) = true := by
  simp only [ctlOk, ha, hb, Bool.and_self]

theorem ctlOk_loop_of {c : Cond} {a : Prog isa} (ha : ctlOk a = true) : ctlOk (.loop a c) = true := ha

/-- MXCSR's control bits, which the calling convention preserves. -/
abbrev ctl (v : BitVec 32) : BitVec 10 := v.extractLsb' 6 10

theorem restores_eq {a b : Prog isa} (h : restores a b = true) :
    ∃ m m' r mid, a = .block (mxcsrSave m r) ∧ b = .seq mid (.block (mxcsrRestore m' r)) ∧
      ∀ i ∈ instrs mid, Taint.clobbers i r = false := by
  unfold restores at h
  split at h
  · split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, hm⟩ := h
      refine ⟨_, _, _, _, rfl, rfl, fun i hi => ?_⟩
      rw [Code.allInstrs_eq, List.all_eq_true] at hm
      simpa using hm i hi
    · cases h
  · cases h

theorem ea_writeMem (s : State) (x : Mem) (m : MemOp) : ({ s with mem := x } : State).ea m = s.ea m := rfl

theorem save_exec {m : MemOp} {r : Reg} {s s' : State} {t : List Leak}
    (h : execBlock isa (mxcsrSave m r) s = some (s', t)) :
    s'.gpr r = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧ s'.mxcsr = s.mxcsr := by
  simp only [mxcsrSave, execBlock, isa, exec, State.store32] at h
  by_cases hw : InRegions s.wr (s.ea m) 4
  · have hl : InRegions (s.rd ++ s.wr) (s.ea m) 4 :=
      let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩
    simp only [hw, ite_true, readSrc32, State.load32, ea_writeMem, hl, Option.map_some,
      Mem.readW_writeW_self32, execAlu32, Option.bind_some, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨?_, rfl⟩
    simp only [State.setReg32, State.setReg, ↓reduceIte,
      BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
  · simp only [hw, ite_false, reduceCtorEq] at h

theorem restore_exec {m : MemOp} {r : Reg} {s s' : State} {t : List Leak}
    (h : execBlock isa (mxcsrRestore m r) s = some (s', t)) : s'.mxcsr = (s.gpr r).setWidth 32 := by
  simp only [mxcsrRestore, execBlock, isa, exec, State.store32] at h
  by_cases hw : InRegions s.wr (s.ea m) 4
  · have hl : InRegions (s.rd ++ s.wr) (s.ea m) 4 :=
      let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩
    simp only [hw, ite_true, State.load32, ea_writeMem, hl, Mem.readW_writeW_self32,
      Option.bind_some] at h
    by_cases hz : BitVec.extractLsb' 16 16 (BitVec.setWidth 32 (s.gpr r)) = 0
    · simp only [hz, ite_true, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl
    · simp only [hz, ite_false, Option.map_none, reduceCtorEq] at h
  · simp only [hw, ite_false, reduceCtorEq] at h

theorem ctl_and (v : BitVec 32) : ctl (BitVec.setWidth 32 (BitVec.setWidth 64 (v &&& 0xFFFF))) = ctl v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hi, decide_true,
    Bool.true_and]
  rw [decide_eq_true (by omega_using [hi]), decide_eq_true (by omega_using [hi]), Bool.true_and,
    show (0xFFFF : BitVec 32).getLsbD (6 + i) = true by revert i; decide, Bool.and_true, Bool.true_and]

theorem execBlock_ctl {is : List Instr} (hc : (is.all fun i => !loadsMxcsr i) = true)
    {s s' : State} {t : List Leak} (h : execBlock isa is s = some (s', t)) : s'.mxcsr = s.mxcsr :=
  execBlock_mxcsr (fun i hi => by simpa using List.all_eq_true.mp hc i hi) h

/-- Code that `ctlOk` accepts keeps MXCSR's control bits. -/
theorem Exec.ctl {c : Prog isa} (hc : ctlOk c = true) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : ctl s'.mxcsr = ctl s.mxcsr := by
  induction h with
  | block h => rw [execBlock_ctl ((KList.all_eq _ _).symm.trans hc) h]
  | seq h₁ h₂ ih₁ ih₂ =>
    simp only [ctlOk, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hr | ⟨ha, hb⟩
    · obtain ⟨m, m', r, mid, rfl, rfl, hk⟩ := restores_eq hr
      rw [Exec.block_iff] at h₁
      cases h₂ with
      | seq hm hr' =>
        rw [Exec.block_iff] at hr'
        rw [restore_exec hr', Exec.gpr hk hm, (save_exec h₁).1, ctl_and]
    · rw [ih₂ hb, ih₁ ha]
  | iteT _ _ ih =>
    simp only [ctlOk, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih =>
    simp only [ctlOk, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc, ih₁ hc]
  | frame hp _ hq ih =>
    simp only [ctlOk, Bool.and_eq_true] at hc
    rw [pop_mxcsr hq, ih hc.1.2, push_mxcsr hp]
  | call hc₁ _ hr ih =>
    simp only [isa, call, Option.some.injEq] at hc₁
    simp only [isa, ret] at hr
    split at hr <;> cases hr
    subst hc₁
    exact ih hc
  | icall _ hc₁ _ hr ih =>
    simp only [ctlOk, Bool.and_eq_true] at hc
    simp only [isa, call, Option.some.injEq] at hc₁
    simp only [isa, ret] at hr
    split at hr <;> cases hr
    subst hc₁
    exact ih hc.1.2
  | icallNext _ _ _ ih =>
    exact ih (by simp only [ctlOk, Bool.and_eq_true] at hc ⊢; exact hc.2)

/-- The calling-convention obligations of code that `ctlOk` accepts, from
the others. -/
theorem abiPreserved_of_ctl {c : Prog isa} (hc : ctlOk c = true) {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') (h : gprPreserved s s') : abiPreserved s s' :=
  ⟨h.1, h.2, Exec.ctl hc he⟩

/-! ## MXCSR on return as a function of MXCSR on entry -/

theorem MxC.app_comp (a b : MxC) (x : BitVec 32) : (a.comp b).app x = b.app (a.app x) := by
  cases a <;> cases b <;> simp [MxC.comp, MxC.app, BitVec.and_assoc]

theorem MxC.app_idem (a : MxC) (x : BitVec 32) : a.app (a.app x) = a.app x := by
  cases a <;> simp [MxC.app, BitVec.and_assoc]

theorem restoresC_eq {a b : Prog isa} (h : restoresC a b = true) :
    ∃ m m' r mid, a = .block (mxcsrSave m r) ∧ b = .seq mid (.block (mxcsrRestore m' r)) ∧
      ∀ i ∈ instrs mid, Taint.clobbers i r = false := by
  unfold restoresC at h
  split at h
  · split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, hm⟩ := h
      exact ⟨_, _, _, _, rfl, rfl, fun i hi => by simpa using Code.all_instrs hm i hi⟩
    · cases h
  · cases h

theorem mxClass_icall (i : Instr) (n : String) (b nx : Prog isa) : mxClass (.icall i n b nx) =
    if loadsMxcsr i then none else
    match mxClass b, mxClass nx with
    | some x, some y => if x = y then some x else none
    | _, _ => none := rfl

theorem mask_restore {m m' : MemOp} {r : Reg} {mid : Prog isa} {s s₁ s' : State} {t₁ t : List Leak}
    (hk : ∀ i ∈ instrs mid, Taint.clobbers i r = false)
    (h₁ : execBlock isa (mxcsrSave m r) s = some (s₁, t₁))
    (h₂ : Exec isa (.seq mid (.block (mxcsrRestore m' r))) s₁ t s') : s'.mxcsr = MxC.mask.app s.mxcsr := by
  cases h₂ with
  | seq hm hr' =>
    rw [Exec.block_iff] at hr'
    rw [restore_exec hr', Exec.gpr hk hm, (save_exec h₁).1,
      BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
    rfl

/-- Code of class `k` leaves `k.app` of MXCSR on entry. -/
theorem Exec.mxClass {c : Prog isa} {k : MxC} (hc : mxClass c = some k) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : s'.mxcsr = k.app s.mxcsr := by
  induction h generalizing k with
  | block h =>
    simp only [VG.X86_64.mxClass] at hc
    split at hc
    · cases hc; rename_i hb; exact execBlock_ctl hb h
    · cases hc
  | @seq a b _ _ _ _ _ h₁ h₂ ih₁ ih₂ =>
    simp only [VG.X86_64.mxClass] at hc
    split at hc
    · rename_i hr; cases hc
      obtain ⟨m, m', r, mid, rfl, rfl, hk⟩ := restoresC_eq hr
      rw [Exec.block_iff] at h₁
      exact mask_restore hk h₁ h₂
    · split at hc
      · rename_i x y hx hy; cases hc
        rw [ih₂ hy, ih₁ hx, MxC.app_comp]
      · cases hc
  | iteT _ _ ih =>
    simp only [VG.X86_64.mxClass] at hc
    split at hc
    · rename_i x y hx hy; split at hc
      · cases hc; exact ih hx
      · cases hc
    · cases hc
  | iteF _ _ ih =>
    simp only [VG.X86_64.mxClass] at hc
    split at hc
    · rename_i x y hx hy; split at hc
      · rename_i e; cases hc; subst e; exact ih hy
      · cases hc
    · cases hc
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc, ih₁ hc, MxC.app_idem]
  | frame hp _ hq ih =>
    simp only [VG.X86_64.mxClass] at hc
    split at hc
    · rw [pop_mxcsr hq, ih hc, push_mxcsr hp]
    · cases hc
  | call hc₁ _ hr ih =>
    simp only [isa, call, Option.some.injEq] at hc₁
    simp only [isa, ret] at hr
    split at hr <;> cases hr
    subst hc₁
    exact ih hc
  | icall _ hc₁ _ hr ih =>
    simp only [VG.X86_64.mxClass] at hc
    split at hc
    · cases hc
    · split at hc
      · rename_i x y hx hy; split at hc
        · cases hc
          simp only [isa, call, Option.some.injEq] at hc₁
          simp only [isa, ret] at hr
          split at hr <;> cases hr
          subst hc₁
          exact ih hx
        · cases hc
      · cases hc
  | icallNext _ _ _ ih =>
    rw [mxClass_icall] at hc
    split at hc
    · cases hc
    · split at hc
      · rename_i x y hx hy; split at hc
        · rename_i e; cases hc; subst e; exact ih hy
        · cases hc
      · cases hc

/-- Code of some class leaves in MXCSR a function of MXCSR on entry. -/
theorem mxFun_of {c : Prog isa} (h : (mxClass c).isSome = true) :
    ∃ f : BitVec 32 → BitVec 32, ∀ s t s', Exec isa c s t s' → s'.mxcsr = f s.mxcsr := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
  exact ⟨k.app, fun _ _ _ he => Exec.mxClass hk he⟩

/-- Code that never loads MXCSR is of class `keep`. -/
theorem mxClass_of_noLoad {c : Prog isa} (h : c.all (fun i => !loadsMxcsr i) = true) : mxClass c = some .keep := by
  induction c with
  | block is => simp only [Code.all] at h; simp only [VG.X86_64.mxClass, h, ↓reduceIte]
  | seq a b iha ihb =>
    simp only [Code.all, Bool.and_eq_true] at h
    simp only [VG.X86_64.mxClass, iha h.1, ihb h.2]
    split
    · rename_i hr
      obtain ⟨m, m', r, mid, rfl, rfl, -⟩ := restoresC_eq hr
      simp [Code.all, mxcsrRestore, loadsMxcsr] at h
    · rfl
  | ite _ _ _ iht ihe =>
    simp only [Code.all, Bool.and_eq_true] at h
    simp only [VG.X86_64.mxClass, iht h.1, ihe h.2, ↓reduceIte]
  | loop _ _ ih => exact ih h
  | call _ _ ih => exact ih h
  | frame _ _ _ ih =>
    simp only [Code.all, Bool.and_eq_true] at h
    simp only [VG.X86_64.mxClass, h.1.1, h.2, Bool.and_self, ↓reduceIte, ih h.1.2]
  | icall i _ _ _ ihb ihn =>
    simp only [Code.all, Bool.and_eq_true] at h
    have h1 : loadsMxcsr i = false := by simpa using h.1.1
    simp only [VG.X86_64.mxClass, h1, Bool.false_eq_true, ↓reduceIte, ihb h.1.2, ihn h.2]

end VG.X86_64
