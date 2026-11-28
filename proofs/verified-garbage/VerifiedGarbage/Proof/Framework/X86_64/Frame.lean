module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.X86_64.Isa

import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Frames (x86-64)

A frame's push stores its registers below `rsp` (`pushed`) and makes those
bytes a writable region; its pop reloads one register and removes the
region (`popped`). `WP.frame` runs a frame whose body leaves `rsp` and the
writable regions as the push left them, and `RelCT.frame` relates two runs of
one.
-/

@[expose] public section

namespace VG.X86_64

/-- The state after a frame's push of `rs`. -/
def pushed (rs : List Reg) (s : State) : State :=
  { pushRegs s rs with wr := ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length), 8 * rs.length⟩ :: s.wr }

/-- The state after a frame's `pop r` (`k` times), from the state `s` its
body ends in. -/
def popped (r : Reg) (k : Nat) (s : State) : State := { popReg s r k with wr := s.wr.tail }

theorem push_pushed {rs : List Reg} {s : State} (hne : rs ≠ []) (hrs : .rsp ∉ rs)
    (hn : 8 * rs.length ≤ (s.gpr .rsp).toNat) : isa.push (.push rs) s = some (pushed rs s) := by
  simp only [isa, push, ne_eq, hne, not_false_eq_true, hrs, hn, and_self, ite_true]
  rfl

theorem push_some {rs : List Reg} {s s₁ : State} (h : isa.push (.push rs) s = some s₁) :
    s₁ = pushed rs s := by
  simp only [isa, push] at h
  split at h <;> [skip; cases h]
  cases h
  rfl

@[simp] theorem pushed_rd (rs : List Reg) (s : State) : (pushed rs s).rd = s.rd :=
  (pushRegs_eq s rs).1
@[simp] theorem pushed_wr (rs : List Reg) (s : State) :
    (pushed rs s).wr = ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length), 8 * rs.length⟩ :: s.wr := rfl
theorem pushed_rsp (rs : List Reg) (s : State) :
    (pushed rs s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length) := (pushRegs_eq s rs).2.2.1
theorem pushed_gpr (rs : List Reg) (s : State) {r : Reg} (h : r ≠ .rsp) :
    (pushed rs s).gpr r = s.gpr r := (pushRegs_eq s rs).2.2.2 r h

@[simp] theorem pushed_mxcsr (rs : List Reg) (s : State) : (pushed rs s).mxcsr = s.mxcsr :=
  pushRegs_mxcsr s rs

theorem popReg_mem (s : State) (d : Reg) (k : Nat) : (popReg s d k).mem = s.mem := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

@[simp] theorem popped_rd (r : Reg) (k : Nat) (s : State) : (popped r k s).rd = s.rd :=
  (popReg_eq s r k).1
@[simp] theorem popped_wr (r : Reg) (k : Nat) (s : State) : (popped r k s).wr = s.wr.tail := rfl
@[simp] theorem popped_mem (r : Reg) (k : Nat) (s : State) : (popped r k s).mem = s.mem :=
  popReg_mem s r k
@[simp] theorem popped_mxcsr (r : Reg) (k : Nat) (s : State) : (popped r k s).mxcsr = s.mxcsr :=
  popReg_mxcsr s r k
theorem popped_rsp (r : Reg) (k : Nat) (s : State) :
    (popped r k s).gpr .rsp = s.gpr .rsp + BitVec.ofNat 64 (8 * k) := (popReg_eq s r k).2.2.1
theorem popped_gpr (r : Reg) (k : Nat) (s : State) {r' : Reg} (h : r' ≠ .rsp) (h' : r' ≠ r) :
    (popped r k s).gpr r' = s.gpr r' := (popReg_eq s r k).2.2.2 r' h h'

theorem toNat_sub_ofNat {a : Addr} {k : Nat} (h : k ≤ a.toNat) :
    (a - BitVec.ofNat 64 k).toNat = a.toNat - k := by
  have := a.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_using [h]),
    show 2 ^ 64 - k + a.toNat = (a.toNat - k) + 2 ^ 64 by omega_using [h], Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_using [])]

/-- `push r` for each of `rs` stores `rs[j]` at `rsp - 8 (j + 1)`, and nothing
outside the `8 * rs.length` bytes below `rsp`. -/
theorem pushRegs_mem (s : State) (rs : List Reg) (hrs : .rsp ∉ rs)
    (hn : 8 * rs.length ≤ (s.gpr .rsp).toNat) :
    Frame [⟨s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length), 8 * rs.length⟩] s.mem (pushRegs s rs).mem ∧
      ∀ j (hj : j < rs.length),
        (pushRegs s rs).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr rs[j] := by
  induction rs generalizing s with
  | nil => exact ⟨Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at hrs
    simp only [List.length_cons] at hn ⊢
    let s₁ : State := { s.setReg .rsp (s.gpr .rsp - 8) with
      mem := s.mem.writeW (s.gpr .rsp - 8) (s.gpr x) }
    have hs₁ : s₁ = { s.setReg .rsp (s.gpr .rsp - 8) with
      mem := s.mem.writeW (s.gpr .rsp - 8) (s.gpr x) } := rfl
    have hsp₁ : s₁.gpr .rsp = s.gpr .rsp - 8 := by simp [hs₁, State.setReg]
    have hg₁ : ∀ r, r ≠ .rsp → s₁.gpr r = s.gpr r := fun r h => by simp [hs₁, State.setReg, h]
    have hm₁ : s₁.mem = s.mem.writeW (s.gpr .rsp - 8) (s.gpr x) := rfl
    have e₁ : (s₁.gpr .rsp).toNat = (s.gpr .rsp).toNat - 8 := by
      rw [hsp₁]; have := (s.gpr .rsp).isLt; bv_omega_arith
    obtain ⟨ih₁, ih₂⟩ := ih s₁ hrs.2 (by omega_using [hn, e₁])
    have hp : pushRegs s (x :: xs) = pushRegs s₁ xs := rfl
    generalize hS : s.gpr .rsp = S at *
    generalize hT : s₁.gpr .rsp = T at *
    subst hsp₁
    clear ih
    refine ⟨fun y hy => ?_, fun j hj => ?_⟩
    · have hy' := hy _ (List.mem_singleton_self _)
      simp only [Region.Contains] at hy'
      rw [hp, ih₁ y (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains]; bv_omega_arith), hm₁]
      apply Mem.write_apply
      bv_omega_arith
    · rw [hp]
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [show S - BitVec.ofNat 64 (8 * (0 + 1)) = S - 8 from rfl,
          ← Mem.readW_writeW_self64 s.mem (S - 8) (s.gpr x), ← hm₁]
        refine Mem.readW_congr fun t ht => ih₁ _ fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains]
        simp only [Nat.reduceDiv] at ht
        bv_omega_arith
      | succ j =>
        simp only [List.getElem_cons_succ]
        have := ih₂ j (by omega_using [hj])
        rw [hg₁ _ (fun h => hrs.2 (h ▸ List.getElem_mem _))] at this
        rw [← this]
        congr 1
        bv_omega_arith

/-- The memory a release leaves, `lose`, differs from the frame's only in the
frame. -/
theorem lose_frame (m : Mem) (a : Addr) (n : Nat) (u : Nat → BitVec 64) :
    Frame [⟨a, n⟩] m (lose m a n u) := by
  intro x hx
  have h := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h
  simp only [lose]
  split
  · omega
  · rfl

/-- Two memories that agree at a byte agree there once the same release, with
the same unknowns, loses it: the residue of two runs that share their
unknowns. -/
theorem lose_congr {m₁ m₂ : Mem} (a : Addr) (n : Nat) (u : Nat → BitVec 64) {x : Addr}
    (h : m₁ x = m₂ x) : lose m₁ a n u x = lose m₂ a n u x := by
  simp only [lose]
  split
  · split
    · exact h
    · rfl
  · exact h

/-- A byte outside the released frame keeps its value. -/
theorem lose_out {m : Mem} {a : Addr} {n : Nat} {u : Nat → BitVec 64} {x : Addr}
    (h : n ≤ (x - a).toNat) : lose m a n u x = m x := by
  simp only [lose]
  split
  · omega
  · rfl

/-- The state a frame's pop leaves: `popped`, with the released frame's
bytes `lose`'s and the unknowns it used gone. -/
def released (r : Reg) (k : Nat) (s : State) : State :=
  { popped r k s with
    mem := lose s.mem (s.gpr .rsp) (8 * k) s.unknowns
    unknowns := fun n => s.unknowns (n + 2 * k) }

theorem pop_released {rs : List Reg} {r : Reg} {s s₂ : State} (hne : rs ≠ []) (hr : r ≠ .rsp)
    (hsp : s₂.gpr .rsp = (pushed rs s).gpr .rsp) (hw : s₂.wr = (pushed rs s).wr) :
    isa.pop (.pop r rs.length) (pushed rs s) s₂ = some (released r rs.length s₂) := by
  simp only [isa, pop]
  refine ite_eq_left ⟨by simpa using hne, hr, hsp, hw, ?_⟩
  rw [pushed_wr, pushed_rsp]; rfl

/-- A frame: its body runs from `pushed rs s`, ends with `rsp` and the
writable regions as the push left them, and the pop of the `rs.length`
words leads to `popped r rs.length s₂`, of which the postcondition may rely
on nothing the frame's bytes hold, nor on the unknowns: it holds whatever
memory `m` that differs from the body's only in the frame, and whatever
unknowns `u`, the state then has. (A frame's bytes are below `rsp` once it
is released, where a signal handler may overwrite them.) -/
theorem WP.frame {rs : List Reg} {r : Reg} {body : Prog isa} {s : State} {Q : State → Prop}
    (hne : rs ≠ []) (hrs : .rsp ∉ rs) (hr : r ≠ .rsp) (hn : 8 * rs.length ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (pushed rs s) fun s₂ => s₂.gpr .rsp = (pushed rs s).gpr .rsp ∧
      s₂.wr = (pushed rs s).wr ∧ ∀ m u,
        Frame [⟨s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length), 8 * rs.length⟩] s₂.mem m →
        Q { popped r rs.length s₂ with mem := m, unknowns := u }) :
    WP isa (.frame (.push rs) body (.pop r rs.length)) s Q := by
  obtain ⟨t, s₂, he, hsp, hw, hq⟩ := hb
  refine ⟨_, _, Exec.frame (push_pushed hne hrs hn) he (pop_released hne hr hsp hw), hq _ _ ?_⟩
  rw [hsp, pushed_rsp]
  exact lose_frame _ _ _ _

/-- `WP.frame` with the state the pop leaves, `released r rs.length s₂`. Only the residue lemmas use it, which state
per run what a released frame holds (ChaCha20's gathered seal, MCDT's
entry); every other proof uses `WP.frame`, whose postcondition holds
whatever the frame's bytes. -/
theorem WP.frameMem {rs : List Reg} {r : Reg} {body : Prog isa} {s : State} {Q : State → Prop}
    (hne : rs ≠ []) (hrs : .rsp ∉ rs) (hr : r ≠ .rsp) (hn : 8 * rs.length ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (pushed rs s) fun s₂ => s₂.gpr .rsp = (pushed rs s).gpr .rsp ∧
      s₂.wr = (pushed rs s).wr ∧ Q (released r rs.length s₂)) :
    WP isa (.frame (.push rs) body (.pop r rs.length)) s Q := by
  obtain ⟨t, s₂, he, hsp, hw, hq⟩ := hb
  exact ⟨_, _, Exec.frame (push_pushed hne hrs hn) he (pop_released hne hr hsp hw), hq⟩

/-- A frame's pop from memory `m` that agrees with `s`'s on the `k` words it
reads loads what it loads from `s`: with that memory (and any unknowns) it
leads to `popReg s r k` with them. (An outer frame's pop, after an inner
frame lost its bytes, reads only its own.) -/
theorem popReg_withMem (r : Reg) : ∀ (k : Nat) (s : State) (m : Mem) (u : Nat → BitVec 64),
    (∀ i < k, m.readW (s.gpr .rsp + BitVec.ofNat 64 (8 * i)) 64 =
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (8 * i)) 64) →
    popReg { s with mem := m, unknowns := u } r k = { popReg s r k with mem := m, unknowns := u }
  | 0, _, _, _, _ => rfl
  | k + 1, s, m, u, h => by
    have h0 : m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
      have := h 0 (Nat.zero_lt_succ _)
      rwa [show s.gpr .rsp + BitVec.ofNat 64 (8 * 0) = s.gpr .rsp from BitVec.add_zero _] at this
    let s' : State := (s.setReg r (s.mem.readW (s.gpr .rsp) 64)).setReg .rsp (s.gpr .rsp + 8)
    have hs' : s'.gpr .rsp = s.gpr .rsp + 8 := by simp [s', State.setReg]
    have e : ({ s with mem := m, unknowns := u }.setReg r ({ s with mem := m, unknowns := u }.mem.readW
        ({ s with mem := m, unknowns := u }.gpr .rsp) 64)).setReg .rsp
          ({ s with mem := m, unknowns := u }.gpr .rsp + 8) = { s' with mem := m, unknowns := u } := by
      show (({ s with mem := m, unknowns := u }.setReg r (m.readW (s.gpr .rsp) 64)).setReg .rsp
        (s.gpr .rsp + 8)) = _
      rw [h0]; rfl
    show popReg (({ s with mem := m, unknowns := u }.setReg r ({ s with mem := m, unknowns := u }.mem.readW
        ({ s with mem := m, unknowns := u }.gpr .rsp) 64)).setReg .rsp
          ({ s with mem := m, unknowns := u }.gpr .rsp + 8)) r k = { popReg s' r k with mem := m, unknowns := u }
    rw [e]
    refine popReg_withMem r k s' m u fun i hi => ?_
    have := h (i + 1) (by omega_using [hi])
    rw [hs', show s.gpr .rsp + 8 + BitVec.ofNat 64 (8 * i) = s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1)) by
      rw [BitVec.add_assoc]; congr 1; bv_omega_arith]
    exact this

/-- `popReg_withMem`, for the pop of a frame. -/
theorem popped_withMem {r : Reg} {k : Nat} {s : State} {m : Mem} {u : Nat → BitVec 64}
    (h : ∀ i < k, m.readW (s.gpr .rsp + BitVec.ofNat 64 (8 * i)) 64 =
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (8 * i)) 64) :
    popped r k { s with mem := m, unknowns := u } = { popped r k s with mem := m, unknowns := u } := by
  unfold popped
  rw [popReg_withMem r k s m u h]

/-- A byte of a region apart from a frame is what it was once the frame's
bytes are lost. -/
theorem lost_byte {F R : Region} {m m' : Mem} (f : Frame [F] m m') (hd : R.Disjoint F) {i : Nat}
    (hi : i < R.len) : m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine f _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine hd _ ?_ hc
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [hi, this]

/-- Two runs of a frame leak the same trace when `rsp` agrees and the runs of
its body, from the states after the push, do. -/
theorem RelCT.frame {rs : List Reg} {r : Reg} {k : Nat} {body : Prog isa}
    {P R : State → State → Prop} (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed rs s₁ ∧ b = pushed rs s₂) body R) :
    RelCT isa P (.frame (.push rs) body (.pop r k)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := push_some p₁
      obtain rfl := push_some p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      have g₁ := (pop_eq q₁).2.2.2.2.1
      have g₂ := (pop_eq q₂).2.2.2.2.1
      rw [pushed_rsp] at g₁ g₂
      have e := hsp _ _ hp
      refine ⟨?_, trivial⟩
      simp only [addrs, g₁, g₂, e]

end VG.X86_64
