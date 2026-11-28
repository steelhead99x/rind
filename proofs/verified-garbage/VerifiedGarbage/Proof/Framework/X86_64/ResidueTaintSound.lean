module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaint
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Frame

/-!
# The residue analysis is sound (x86-64)

`rtaint`, the analysis of `ResidueTaint.lean` as a `VG.Taint`: each transfer
function is sound (`step_sound`, `call_sound`, `ret_sound`, `push_sound`,
`pop_sound`, and the order and joins). `Taint.check_sound` then gives, for
two runs of code from states the starting taint describes, states that the
final taint describes: equal outside the writable regions but within the
window's bytes that `sec` lists.
-/

@[expose] public section

namespace VG.X86_64.RTaint

open VG.X86_64 VG.X86_64.Taint
open VG.X86_64.Residue (Pres Pres.none' Pres.some' Pres.map' Pres.bind')

/-! ## What instructions change -/

local macro "uk_leaf" : tactic => `(tactic| first
  | exact Pres.none'
  | (apply Pres.some'; rfl)
  | (apply Pres.map'; intro _; rfl)
  | (apply Pres.map'; intro _; split <;> rfl))

local syntax "uk_go" : tactic
macro_rules
  | `(tactic| uk_go) => `(tactic| first
    | uk_leaf
    | (apply Pres.bind'; intro _; uk_go)
    | (split <;> uk_go))

theorem exec_unknowns_pres (i : Instr) (s : State) :
    Pres (fun x => x.unknowns = s.unknowns) (exec i s) := by
  cases i
  case vop op => simp only [reduceExec]; rw [Taint.VOp.exec_eq]; exact Pres.some' rfl
  case zop op => simp only [reduceExec]; rw [Taint.ZOp.exec_eq]; exact Pres.some' rfl
  case xop op => simp only [reduceExec]; rw [Taint.XOp.exec_eq]; exact Pres.some' rfl
  case eop op => simp only [reduceExec]; rw [Taint.EOp.exec_eq]; exact Pres.some' rfl
  case e5op op => simp only [reduceExec]; rw [Taint.E5Op.exec_eq]; exact Pres.some' rfl
  case vmovdquLoad len _ _ | vmovdquStore len _ _ | vbinLoad _ len _ _ _ =>
    cases len <;> simp only [reduceExec, State.store128, State.store256] <;> uk_go
  case evLoad d _ | evMadd52Load _ d _ _ | evBroadcastLoad d _ =>
    simp only [reduceExec]; apply Pres.map'; intro _; rw [Taint.setVy_eq]
  case e5InsertLoad d _ _ _ =>
    simp only [reduceExec]; apply Pres.map'; intro _; rw [Taint.setVz_eq]
  all_goals simp only [reduceExec, execAlu, execAluW, execAlu32, execShift32, execShift, execRorx32,
      execRorx, execShld, execBtr, execMulx, execAdcx, execAdox, execCmov, State.store64,
      State.store32, State.store8, State.store16, State.store128, State.store256, State.store512,
      State.storeMasked512, State.storeMasked512B]
  all_goals uk_go

theorem exec_unknowns {i : Instr} {s s' : State} (h : exec i s = some s') : s'.unknowns = s.unknowns :=
  exec_unknowns_pres i s s' h

theorem exec_frame {i : Instr} {s s' : State} (h : exec i s = some s') :
    s'.wr = s.wr ∧ Frame s.wr s.mem s'.mem := by
  have e : execBlock isa [i] s = some (s', (addrs i s).map Leak.addr) := by
    simp only [execBlock, isa, h, Option.map_some, List.append_nil]
  obtain ⟨-, hw, hf⟩ := execBlock_regions e
  exact ⟨hw, hf⟩



theorem exec_mem_pres (i : Instr) (s : State) (h : writesMem i = false) :
    Pres (fun x => x.mem = s.mem) (exec i s) := by
  cases i <;> simp only [writesMem, storeW, Option.isSome_some, Option.isSome_none, Bool.true_or,
    Bool.false_or, reduceCtorEq] at h
  case vop op => simp only [reduceExec]; rw [Taint.VOp.exec_eq]; exact Pres.some' rfl
  case zop op => simp only [reduceExec]; rw [Taint.ZOp.exec_eq]; exact Pres.some' rfl
  case xop op => simp only [reduceExec]; rw [Taint.XOp.exec_eq]; exact Pres.some' rfl
  case eop op => simp only [reduceExec]; rw [Taint.EOp.exec_eq]; exact Pres.some' rfl
  case e5op op => simp only [reduceExec]; rw [Taint.E5Op.exec_eq]; exact Pres.some' rfl
  case vmovdquLoad len _ _ | vbinLoad _ len _ _ _ => cases len <;> simp only [reduceExec] <;> uk_go
  case vmovdquStore len _ _ => cases len <;> simp at h
  case evLoad d _ | evMadd52Load _ d _ _ | evBroadcastLoad d _ =>
    simp only [reduceExec]; apply Pres.map'; intro _; rw [Taint.setVy_eq]
  case e5InsertLoad d _ _ _ =>
    simp only [reduceExec]; apply Pres.map'; intro _; rw [Taint.setVz_eq]
  all_goals simp only [reduceExec, execAlu, execAluW, execAlu32, execShift32, execShift, execRorx32,
      execRorx, execShld, execBtr, execMulx, execAdcx, execAdox, execCmov]
  all_goals uk_go

theorem exec_mem {i : Instr} {s s' : State} (h : writesMem i = false) (e : exec i s = some s') :
    s'.mem = s.mem :=
  exec_mem_pres i s h s' e

theorem writeW_out {m : Mem} {a y : Addr} {w : Nat} {v : BitVec w} (h : ¬ (y - a).toNat < w / 8) :
    m.writeW a v y = m y :=
  Mem.write_apply h

/-- A store changes memory only within the `w` bytes at its address. -/
theorem exec_store {i : Instr} {m : MemOp} {w : Nat} (hi : storeW i = some (m, w)) {s s' : State}
    (e : exec i s = some s') : ∀ y, ¬ (y - s.ea m).toNat < w → s'.mem y = s.mem y := by
  intro y hy
  cases i <;> simp only [storeW, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hi
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := hi
       simp only [reduceExec, State.store64, State.store32, State.store8, State.store16, State.store128,
         State.store256, State.store512] at e
       split at e <;> [skip; cases e]
       cases e
       exact writeW_out (by omega_using [hy]))
    | skip
  case vmovdquStore len _ _ =>
    cases len <;> simp only [Option.some.injEq, Prod.mk.injEq] at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
      simp only [reduceExec, State.store128, State.store256] at e <;> split at e <;> cases e <;>
      exact writeW_out (by omega_using [hy])

/-- A byte at offset `k` of region `j` is not among the `n` bytes at offset `d`
of region `i`, if they are other regions or other offsets. -/
theorem byte_not_in {τ : Taint.T} {s : State} (hw : Wf τ s) {i d n j k : Nat} (hn : 0 < n)
    (hd : d + n ≤ τ.lens.getD i 0) (hk : k < τ.lens.getD j 0) (hsep : j ≠ i ∨ k < d ∨ d + n ≤ k) :
    ¬ (byteAddr s j k - byteAddr s i d).toNat < n := by
  intro hlt
  have hne := lens_ne (n := d + n) (by omega_using [hn]) hd
  obtain ⟨-, hdisj, hbound⟩ := hw.1 hne
  obtain ⟨hi, hri⟩ := region_mem hw hne (i := i) (by omega_using [hn, hd])
  obtain ⟨hj, hrj⟩ := region_mem hw hne (i := j) (by omega_using [hk])
  have hli := region_len hw hne i
  have hlj := region_len hw hne j
  have hbi : (region s i).len ≤ 2 ^ 64 := by rw [hri]; exact hbound _ (List.getElem_mem _)
  have hbj : (region s j).len ≤ 2 ^ 64 := by rw [hrj]; exact hbound _ (List.getElem_mem _)
  by_cases hji : j = i
  · -- The same region, at other offsets.
    subst hji
    have hsep := hsep.resolve_left (· rfl)
    have h : byteAddr s j k - byteAddr s j d = BitVec.ofNat 64 k - BitVec.ofNat 64 d :=
      Offset.add_sub_add_left _ _ _
    exact Offset.not_lt_sub_ofNat hsep (by omega_using [hk, hlj, hbj]) hn (by omega_using [hlj, hbj, hd]) (h ▸ hlt)
  · -- Another region: the regions are disjoint.
    have hA : (region s i).Contains (byteAddr s i d) n := by
      simp only [Region.Contains, byteAddr]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn, hd, hli, hbi])]
      omega_using [hd, hli]
    have hX : (region s j).Contains (byteAddr s j k) 1 := by
      simp only [Region.Contains, byteAddr]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk, hlj, hbj])]
      omega_using [hk, hlj]
    have hXi := hA.byte hlt
    rw [List.pairwise_iff_getElem] at hdisj
    rcases Nat.lt_or_gt_of_ne hji with h | h
    · exact hdisj j i hj hi h _ (hrj ▸ hX) (hri ▸ hXi)
    · exact hdisj i j hi hj h _ (hri ▸ hXi) (hrj ▸ hX)

/-! ## The public bytes of the regions -/

theorem byteAddr_wr {s s' : State} (h : s'.wr = s.wr) (i k : Nat) : byteAddr s' i k = byteAddr s i k := by
  simp only [byteAddr, region, h]

/-- The base analysis's agreement, without its slots. -/
theorem _root_.VG.X86_64.Taint.Agree.noSlots {t : Taint.T} {s₁ s₂ : State} (ha : Taint.Agree t s₁ s₂) :
    Taint.Agree { t with slots := [] } s₁ s₂ :=
  ⟨ha.rf, ha.wr, ha.wf₁, ha.wf₂, fun _ h => (by cases h), fun _ h => (by cases h), ha.lo, ha.xr⟩

/-- Two memories after a store of the same value at the same address are the
same at a byte the store writes, or one where they were. -/
theorem writeW_same {m₁ m₂ : Mem} {A X : Addr} {w : Nat} (v : BitVec w)
    (h : (X - A).toNat < w / 8 ∨ m₁ X = m₂ X) : m₁.writeW A v X = m₂.writeW A v X := by
  simp only [Mem.writeW, Mem.write]
  split
  · rfl
  · rename_i hn; exact h.resolve_left hn

/-! ## Stores within a known range of a region -/

theorem idxSlots_ok {t : Taint.T} (hok : SlotsOk t) (ri lo hi : Nat) (p : Bool) :
    SlotsOk (idxStore t ri lo hi p) := by
  intro sl hsl
  simp only [idxStore] at hsl
  split at hsl
  · exact hok sl hsl
  · exact hok sl (List.mem_filter.mp hsl).1

/-- A store of `n` bytes at offset `d` of region `ri`, within `[lo, hi)`, of
the same value in both runs if `p`. -/
theorem Agree.storeAt {t : Taint.T} {s₁ s₂ : State} (ha : Taint.Agree t s₁ s₂) {ri lo hi d n : Nat}
    (hn : 0 < n) (hlo : lo ≤ d) (hhi : d + n ≤ hi) (hfit : hi ≤ t.lens.getD ri 0)
    {V₁ V₂ : BitVec (8 * n)} {p : Bool} (hv : p = true → V₁ = V₂) :
    Taint.Agree (idxStore t ri lo hi p)
      { s₁ with mem := s₁.mem.write (byteAddr s₁ ri d) n V₁ }
      { s₂ with mem := s₂.mem.write (byteAddr s₂ ri d) n V₂ } where
  rf := ha.rf
  wr := ha.wr
  wf₁ := ha.wf₁
  wf₂ := ha.wf₂
  ok := idxSlots_ok ha.ok ri lo hi p
  lo := ha.lo
  xr := ha.xr
  slots := by
    intro sl hsl k hk₁ hk₂
    simp only [byteAddr_withMem]
    have hne : t.lens ≠ [] := lens_ne (i := ri) (n := d + n) (by omega_using [hn]) (Nat.le_trans hhi hfit)
    have hA : byteAddr s₁ ri d = byteAddr s₂ ri d := by simp only [byteAddr, region, ha.wr hne]
    simp only [idxStore] at hsl
    split at hsl
    · rename_i hp
      rw [hA, hv hp, ha.byteAddr_eq hsl hk₂]
      exact write_same _ (ha.byteAddr_eq hsl hk₂ ▸ ha.slots sl hsl k hk₁ hk₂)
    · rw [List.mem_filter] at hsl
      obtain ⟨h, hsep⟩ := hsl
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hsep
      have hsep : sl.1 ≠ ri ∨ k < d ∨ d + n ≤ k := by
        rcases hsep with (h' | h') | h'
        · exact .inl h'
        · exact .inr (.inr (by omega_using [hhi, hk₁, h']))
        · exact .inr (.inl (by omega_using [hlo, hk₂, h']))
      have hk : sl.2.1 + sl.2.2 ≤ t.lens.getD sl.1 0 := ha.ok sl h
      have hd' : d + n ≤ t.lens.getD ri 0 := Nat.le_trans hhi hfit
      have hk' : k < t.lens.getD sl.1 0 := Nat.lt_of_lt_of_le hk₂ hk
      rw [write_other ha.wf₁ hn hd' hk' hsep, write_other ha.wf₂ hn hd' hk' hsep]
      exact ha.slots sl h k hk₁ hk₂

/-! ## The stores `special` handles -/

theorem exec_store_eq {m : MemOp} {r : Reg} {s s' : State} (h : exec (.store m r) s = some s') :
    s' = { s with mem := s.mem.write (s.ea m) 8 ((s.gpr r).setWidth 64) } := by
  simp only [reduceExec, State.store64] at h; split at h <;> cases h; rfl

theorem exec_store8_eq {m : MemOp} {r : Reg} {s s' : State} (h : exec (.store8 m r) s = some s') :
    s' = { s with mem := s.mem.write (s.ea m) 1 (((s.gpr r).setWidth 8).setWidth 8) } := by
  simp only [reduceExec, State.store8] at h; split at h <;> cases h; rfl

theorem exec_movdquStore_eq {m : MemOp} {x : XReg} {s s' : State} (h : exec (.movdquStore m x) s = some s') :
    s' = { s with mem := s.mem.write (s.ea m) 16 ((s.xmm x).setWidth 128) } := by
  simp only [reduceExec, State.store128] at h; split at h <;> cases h; rfl

theorem ubOf_some {l : List (Reg × Nat)} {r : Reg} {n : Nat} (h : ubOf l r = some n) : (r, n) ∈ l := by
  simp only [ubOf, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have := List.find?_some hp
  simp only [beq_iff_eq] at this
  rw [← this]; exact List.mem_of_find?_eq_some hp

theorem find_base {l : List (Reg × Nat × Nat)} {b : Reg} {q : Reg × Nat × Nat}
    (h : l.find? (·.1 == b) = some q) : q ∈ l ∧ q.1 = b := by
  have := List.find?_some h
  simp only [beq_iff_eq] at this
  exact ⟨List.mem_of_find?_eq_some h, this⟩

/-- Where a store `idxRange` bounds writes: at offset `lo` plus the index of region `ri`. -/
theorem idxRange_ea {τ : FT} {s : State} (hw : Wf τ.t s) (o : One τ s) {m : MemOp} {w ri lo hi : Nat}
    (h : idxRange τ m w = some (ri, lo, hi)) :
    ∃ x, m.index = some x ∧ s.ea m = byteAddr s ri (lo + (s.gpr x).toNat) ∧
      lo + (s.gpr x).toNat + w ≤ hi ∧ hi ≤ τ.t.lens.getD ri 0 := by
  unfold idxRange at h
  split at h <;> [rename_i x hx; cases h]
  split at h <;> [rename_i b ri' k B hb hB; cases h]
  split at h <;> [rename_i hc; cases h]
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨hbm, hbe⟩ := find_base hb
  simp only at hbe
  subst hbe
  have hxB := o.ub _ (ubOf_some hB)
  obtain ⟨hs, hd, hfit⟩ := hc
  refine ⟨x, hx, ?_, by simp only at hxB; omega_using [hxB], by omega_using [hfit]⟩
  have hbase := hw.2 _ hbm
  simp only [State.ea, hx, hs, hbase, byteAddr]
  rw [show m.disp = ((m.disp.toNat : Nat) : Int) from (Int.toNat_of_nonneg hd).symm, BitVec.ofInt_natCast]
  rw [show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, BitVec.ofNat_add, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  ac_rfl

theorem memPub_idx {t : Taint.T} {m : MemOp} {x : Reg} (h : memPub t m = true) (hx : m.index = some x) :
    pub t x = true := by
  simp only [memPub, hx, Bool.and_eq_true] at h; exact h.2

/-- An indexed store whose range `idxRange` bounds. -/
theorem idx_sound {τ : FT} {s₁ s₂ : State} (ha : Taint.Agree τ.t s₁ s₂) (o₁ : One τ s₁) (o₂ : One τ s₂)
    {m : MemOp} {w ri lo hi : Nat} (hr : idxRange τ m w = some (ri, lo, hi)) (hm : memPub τ.t m = true)
    (hw : 0 < w) {V₁ V₂ : BitVec (8 * w)} {p : Bool} (hv : p = true → V₁ = V₂) :
    Taint.Agree (idxStore τ.t ri lo hi p)
      { s₁ with mem := s₁.mem.write (s₁.ea m) w V₁ } { s₂ with mem := s₂.mem.write (s₂.ea m) w V₂ } := by
  obtain ⟨x, hx, ea₁, hle, hfit⟩ := idxRange_ea ha.wf₁ o₁ hr
  obtain ⟨x', hx', ea₂, -, -⟩ := idxRange_ea ha.wf₂ o₂ hr
  rw [hx] at hx'; cases hx'
  have hxe : s₁.gpr x = s₂.gpr x := ha.reg (memPub_idx hm hx)
  rw [ea₁, ea₂, ← hxe]
  exact Agree.storeAt ha hw (Nat.le_add_right _ _) hle hfit hv

theorem special_sound {τ : FT} {i : Instr} {t' : Taint.T} {s₁ s₂ s₁' s₂' : State}
    (ha : Taint.Agree τ.t s₁ s₂) (o₁ : One τ s₁) (o₂ : One τ s₂) (h : special τ i = some t')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Taint.Agree t' s₁' s₂' := by
  cases i
  case store m r =>
    rw [exec_store_eq e₁, exec_store_eq e₂]
    cases hx : m.index with
    | none => simp only [special, hx] at h; cases h
    | some x =>
      simp only [special, hx, storeW, storePub] at h
      cases hr : idxRange τ m 8 with
      | none => simp only [hr] at h; cases h
      | some q =>
        obtain ⟨ri, lo, hi⟩ := q
        simp only [hr] at h
        split at h <;> [rename_i hm; cases h]
        cases h
        exact ⟨by simp only [addrs, ha.ea hm], idx_sound ha o₁ o₂ hr hm (by decide) fun hp => by rw [ha.reg hp]⟩
  case store8 m r =>
    rw [exec_store8_eq e₁, exec_store8_eq e₂]
    cases hx : m.index with
    | none => simp only [special, hx] at h; cases h
    | some x =>
      simp only [special, hx, storeW, storePub] at h
      cases hr : idxRange τ m 1 with
      | none => simp only [hr] at h; cases h
      | some q =>
        obtain ⟨ri, lo, hi⟩ := q
        simp only [hr] at h
        split at h <;> [rename_i hm; cases h]
        cases h
        exact ⟨by simp only [addrs, ha.ea hm], idx_sound ha o₁ o₂ hr hm (by decide) fun hp => by rw [ha.reg hp]⟩
  case movdquStore m x =>
    rw [exec_movdquStore_eq e₁, exec_movdquStore_eq e₂]
    cases hx : m.index with
    | none =>
      simp only [special, hx] at h
      split at h <;> [rename_i hxp; cases h]
      simp only [storeStep] at h
      split at h <;> [rename_i hm; cases h]
      cases h
      exact ⟨by simp only [addrs, ha.ea hm], ha.store hm (by decide) fun _ => by rw [ha.xr x hxp]⟩
    | some y =>
      simp only [special, hx, storeW, storePub] at h
      cases hr : idxRange τ m 16 with
      | none => simp only [hr] at h; cases h
      | some q =>
        obtain ⟨ri, lo, hi⟩ := q
        simp only [hr] at h
        split at h <;> [rename_i hm; cases h]
        cases h
        exact ⟨by simp only [addrs, ha.ea hm], idx_sound ha o₁ o₂ hr hm (by decide) fun hp => by rw [ha.xr x hp]⟩
  all_goals simp only [special, reduceCtorEq] at h

/-! ## Zeroing idioms and pointers reloaded from slots -/

theorem _root_.VG.X86_64.Taint.Agree.addReg {t : Taint.T} {s₁ s₂ : State} (ha : Taint.Agree t s₁ s₂) {d : Reg}
    (h : s₁.gpr d = s₂.gpr d) : Taint.Agree { t with regs := t.regs.insert d } s₁ s₂ :=
  ⟨⟨fun r hr => by
      rcases RegSet.mem_insert.mp hr with rfl | hr
      · exact h
      · exact ha.rf.1 r hr, ha.rf.2⟩, ha.wr, ha.wf₁, ha.wf₂, ha.ok, ha.slots, ha.lo, ha.xr⟩

theorem _root_.VG.X86_64.Taint.Agree.addXreg {t : Taint.T} {s₁ s₂ : State} (ha : Taint.Agree t s₁ s₂) {x : XReg}
    (h : s₁.xmm x = s₂.xmm x) : Taint.Agree { t with xregs := t.xregs.insert x } s₁ s₂ :=
  ⟨ha.rf, ha.wr, ha.wf₁, ha.wf₂, ha.ok, ha.slots, ha.lo, fun r hr => by
      rcases RegSet.mem_insert.mp hr with rfl | hr
      · exact h
      · exact ha.xr r hr⟩

theorem _root_.VG.X86_64.Taint.Agree.addBase {t : Taint.T} {s₁ s₂ : State} (ha : Taint.Agree t s₁ s₂) {p : Reg × Nat × Nat}
    (h₁ : s₁.gpr p.1 = (region s₁ p.2.1).base + BitVec.ofNat 64 p.2.2)
    (h₂ : s₂.gpr p.1 = (region s₂ p.2.1).base + BitVec.ofNat 64 p.2.2) :
    Taint.Agree { t with bases := p :: t.bases } s₁ s₂ :=
  ⟨ha.rf, ha.wr,
    ⟨ha.wf₁.1, fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h₁
      · exact ha.wf₁.2 q hq⟩,
    ⟨ha.wf₂.1, fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h₂
      · exact ha.wf₂.2 q hq⟩, ha.ok, ha.slots, ha.lo, ha.xr⟩

theorem exec_xor_self {d : Reg} {s s' : State} (h : exec (.alu .xor d (.reg d)) s = some s') :
    s'.gpr d = 0 := by
  simp only [reduceExec, execAlu, readSrc, Option.bind_some, Option.some.injEq] at h
  subst h
  simp only [State.setReg, ↓reduceIte, BitVec.xor_self]; rfl

theorem exec_xor32_self {d : Reg} {s s' : State} (h : exec (.alu32 .xor d (.reg d)) s = some s') :
    s'.gpr d = 0 := by
  simp only [reduceExec, execAlu32, readSrc32, Option.bind_some, Option.some.injEq] at h
  subst h
  simp only [State.setReg32, State.setReg, ↓reduceIte, BitVec.xor_self, BitVec.setWidth_zero]; rfl

theorem exec_pxor_self {x : XReg} {s s' : State} (h : exec (.xop (.bin .pxor x x)) s = some s') :
    s'.xmm x = 0 := by
  simp only [reduceExec, Option.some.injEq] at h
  subst h
  simp only [XOp.exec, State.setXmm, ↓reduceIte, XBinOp.eval, BitVec.xor_self]; rfl

theorem exec_mov_mem {d : Reg} {m : MemOp} {s s' : State} (h : exec (.mov d (.mem m)) s = some s') :
    s'.gpr d = s.mem.readW (s.ea m) 64 ∧ s'.wr = s.wr := by
  simp only [reduceExec, readSrc, State.load64, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  split at hv <;> cases hv
  simp only [State.setReg, ↓reduceIte, and_self]

theorem find_mb {l : List (Nat × Nat × Nat × Nat)} {ri o : Nat} {q : Nat × Nat × Nat × Nat}
    (h : l.find? (fun e => e.1 == ri && e.2.1 == o) = some q) : q ∈ l ∧ q.1 = ri ∧ q.2.1 = o := by
  have := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨List.mem_of_find?_eq_some h, this⟩

/-- The pointer a load from a slot of `mb` reads. -/
theorem mb_load {τ : FT} {s s' : State} (hw : Wf τ.t s) (o : One τ s) {d : Reg} {m : MemOp}
    {ri off : Nat} {q : Nat × Nat × Nat × Nat} (hm : addrOf τ.t m = some (ri, off))
    (hf : τ.mb.find? (fun e => e.1 == ri && e.2.1 == off) = some q)
    (e : exec (.mov d (.mem m)) s = some s') :
    s'.gpr d = (region s' q.2.2.1).base + BitVec.ofNat 64 q.2.2.2 := by
  obtain ⟨hg, hwr⟩ := exec_mov_mem e
  obtain ⟨hq, h1, h2⟩ := find_mb hf
  have := o.mb _ hq
  rw [h1, h2] at this
  rw [hg, ea_of_addrOf hw hm, this]
  simp only [region, hwr]

theorem post_sound {τ : FT} {i : Instr} {t' : Taint.T} {s₁ s₂ s₁' s₂' : State}
    (hw₁ : Wf τ.t s₁) (hw₂ : Wf τ.t s₂) (o₁ : One τ s₁) (o₂ : One τ s₂)
    (ha : Taint.Agree t' s₁' s₂') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    Taint.Agree (post τ i t') s₁' s₂' := by
  unfold post
  split
  · rename_i d d'
    split
    · rename_i hd
      simp only [beq_iff_eq] at hd; subst hd
      exact ha.addReg (by rw [exec_xor_self e₁, exec_xor_self e₂])
    · exact ha
  · rename_i d d'
    split
    · rename_i hd
      simp only [beq_iff_eq] at hd; subst hd
      exact ha.addReg (by rw [exec_xor32_self e₁, exec_xor32_self e₂])
    · exact ha
  · rename_i x x'
    split
    · rename_i hx
      simp only [beq_iff_eq] at hx; subst hx
      exact ha.addXreg (by rw [exec_pxor_self e₁, exec_pxor_self e₂])
    · exact ha
  · rename_i d m
    split
    · rename_i ri off hm
      split
      · rename_i q hf
        exact ha.addBase (mb_load hw₁ o₁ hm hf e₁) (mb_load hw₂ o₂ hm hf e₂)
      · exact ha
    · exact ha
  · exact ha

/-! ## Loads from the argument area -/

theorem aa_add (s : State) (τ : FT) (o i : Nat) : aa s τ o + BitVec.ofNat 64 i = aa s τ (o + i) := by
  simp only [aa, wa]
  rw [show τ.room + τ.depth + 8 + (o + i) = τ.room + τ.depth + 8 + o + i by omega_using [], BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]

theorem aa_eq {s₁ s₂ : State} {τ : FT} (h : s₁.gpr .rsp = s₂.gpr .rsp) : aa s₁ τ = aa s₂ τ := by
  funext o; simp only [aa, wa, wb, h]

/-- Where a load `argOff` places reads. -/
theorem argOff_ea {τ : FT} {m : MemOp} {o : Nat} (h : argOff τ m = some o) (s : State) :
    s.ea m = aa s τ o := by
  unfold argOff at h
  split at h <;> [rename_i hc; cases h]
  obtain ⟨hb, hi, hd⟩ := hc
  simp only [Option.some.injEq] at h
  have hdisp : m.disp = ((τ.depth + 8 + o : Nat) : Int) := by omega_using [hd, h]
  simp only [State.ea, hi, hb]
  rw [hdisp, BitVec.ofInt_natCast]
  simp only [aa, wa, wb]
  rw [show τ.room + τ.depth + 8 + o = τ.room + (τ.depth + 8 + o) by omega_using [],
    BitVec.ofNat_add τ.room (τ.depth + 8 + o), ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem exec_mov32_mem {d : Reg} {m : MemOp} {s s' : State} (h : exec (.mov32 d (.mem m)) s = some s') :
    s'.gpr d = (s.mem.readW (s.ea m) 32).setWidth 64 ∧ s'.wr = s.wr := by
  simp only [reduceExec, readSrc32, State.load32, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  split at hv <;> cases hv
  simp only [State.setReg32, State.setReg, ↓reduceIte, and_self]

theorem argPost_sound {τ : FT} {i : Instr} {t' : Taint.T} {s₁ s₂ s₁' s₂' : State}
    (hsp : s₁.gpr .rsp = s₂.gpr .rsp) (o₁ : One τ s₁) (o₂ : One τ s₂) (hsa : SaEq τ s₁ s₂)
    (ha : Taint.Agree t' s₁' s₂') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    Taint.Agree (argPost τ i t') s₁' s₂' := by
  have hpub : ∀ {o w : Nat}, saPub τ o w = true → ∀ j < w,
      s₁.mem (aa s₁ τ o + BitVec.ofNat 64 j) = s₂.mem (aa s₁ τ o + BitVec.ofNat 64 j) := by
    intro o w h j hj
    simp only [saPub, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨e, he, h1, h2⟩ := h
    have := hsa e he (o + j) (by omega_using [h1]) (by omega_using [hj, h2])
    rw [← aa_eq hsp] at this
    rw [aa_add]; exact this
  unfold argPost
  split
  · rename_i d m
    split
    · rename_i o ho
      obtain ⟨g₁, w₁⟩ := exec_mov_mem e₁
      obtain ⟨g₂, w₂⟩ := exec_mov_mem e₂
      have ha' : Taint.Agree (if saPub τ o 8 = true then { t' with regs := t'.regs.insert d } else t') s₁' s₂' := by
        split
        · rename_i hp
          refine ha.addReg ?_
          rw [g₁, g₂, argOff_ea ho, argOff_ea ho, ← aa_eq hsp]
          exact Mem.readW_congr fun j hj => hpub hp j hj
        · exact ha
      dsimp only
      split
      · rename_i e hf
        have hq := List.mem_of_find?_eq_some hf
        have hq1 : e.1 = o := by simpa using List.find?_some hf
        refine ha'.addBase ?_ ?_
        · rw [g₁, argOff_ea ho, ← hq1, o₁.sp e hq]; simp only [region, w₁]
        · rw [g₂, argOff_ea ho, ← hq1, o₂.sp e hq]; simp only [region, w₂]
      · exact ha'
    · exact ha
  · rename_i d m
    split
    · rename_i o ho
      split
      · rename_i hp
        obtain ⟨g₁, -⟩ := exec_mov32_mem e₁
        obtain ⟨g₂, -⟩ := exec_mov32_mem e₂
        refine ha.addReg ?_
        rw [g₁, g₂, argOff_ea ho, argOff_ea ho, ← aa_eq hsp]
        exact congrArg (BitVec.setWidth 64) (Mem.readW_congr fun j hj => hpub hp j hj)
      · exact ha
    · exact ha
  · exact ha

/-! ## Loads of public bytes of the regions -/

/-- The bytes `pbPub` says are public: at the same address, and the same, in both runs. -/
theorem pbPub_eq {τ : FT} {s₁ s₂ : State} (ha : Taint.Agree τ.t s₁ s₂) (hwr : s₁.wr = s₂.wr)
    (hpb : PbEq τ s₁ s₂) {m : MemOp} {w : Nat} (h : pbPub τ m w = true) :
    s₂.ea m = s₁.ea m ∧ ∀ j < w, s₁.mem (s₁.ea m + BitVec.ofNat 64 j) = s₂.mem (s₁.ea m + BitVec.ofNat 64 j) := by
  unfold pbPub at h
  split at h <;> [rename_i i d hm; cases h]
  have hea : s₂.ea m = s₁.ea m := by
    rw [ea_of_addrOf ha.wf₁ hm, ea_of_addrOf ha.wf₂ hm]; exact byteAddr_wr hwr.symm i d
  refine ⟨hea, fun j hj => ?_⟩
  have := (hpb i (d + j) (btest_bit h (Nat.le_add_right _ _) (by omega_using [hj]))).2
  rw [← byteAddr_add, ← byteAddr_add, ← ea_of_addrOf ha.wf₁ hm, ← ea_of_addrOf ha.wf₂ hm, hea] at this
  exact this

theorem pbPost_sound {τ : FT} {i : Instr} {t' : Taint.T} {s₁ s₂ s₁' s₂' : State}
    (ha : Taint.Agree τ.t s₁ s₂) (hwr : s₁.wr = s₂.wr) (hpb : PbEq τ s₁ s₂)
    (hb : Taint.Agree t' s₁' s₂') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    Taint.Agree (pbPost τ i t') s₁' s₂' := by
  unfold pbPost
  split
  · rename_i d m
    split
    · rename_i hp
      obtain ⟨hea, hm⟩ := pbPub_eq ha hwr hpb hp
      refine hb.addReg ?_
      rw [(exec_mov_mem e₁).1, (exec_mov_mem e₂).1, hea]
      exact Mem.readW_congr fun j hj => hm j hj
    · exact hb
  · rename_i d m
    split
    · rename_i hp
      obtain ⟨hea, hm⟩ := pbPub_eq ha hwr hpb hp
      refine hb.addReg ?_
      rw [(exec_mov32_mem e₁).1, (exec_mov32_mem e₂).1, hea]
      exact congrArg (BitVec.setWidth 64) (Mem.readW_congr fun j hj => hm j hj)
    · exact hb
  · rename_i c d m
    split
    · rename_i hp
      simp only [Bool.and_eq_true] at hp
      obtain ⟨⟨hp, hd⟩, hf⟩ := hp
      obtain ⟨hea, hm⟩ := pbPub_eq ha hwr hpb hp
      obtain ⟨v₁, c₁, hv₁, hc₁, rfl⟩ := execCmov_some (by simpa only [reduceExec] using e₁)
      obtain ⟨v₂, c₂, hv₂, hc₂, rfl⟩ := execCmov_some (by simpa only [reduceExec] using e₂)
      have r₁ : v₁ = s₁.mem.readW (s₁.ea m) 64 := by
        simp only [readSrc, State.load64] at hv₁; split at hv₁ <;> cases hv₁; rfl
      have r₂ : v₂ = s₂.mem.readW (s₂.ea m) 64 := by
        simp only [readSrc, State.load64] at hv₂; split at hv₂ <;> cases hv₂; rfl
      have hc : c₁ = c₂ := by
        have := Taint.cond_sound (c := c) ha hf
        rw [hc₁, hc₂] at this
        exact Option.some.inj this
      refine hb.addReg ?_
      rw [cmov_gpr, cmov_gpr]
      simp only [↓reduceIte]
      rw [hc, r₁, r₂, hea, ha.reg hd, Mem.readW_congr fun j hj => hm j hj]
    · exact hb
  · exact hb

/-! ## The lengths of the regions, kept -/

theorem argPost_lens (τ : FT) (i : Instr) (t : Taint.T) : (argPost τ i t).lens = t.lens := by
  unfold argPost; split <;> (try split) <;> (try split) <;> (try split) <;> rfl

theorem post_lens (τ : FT) (i : Instr) (t : Taint.T) : (post τ i t).lens = t.lens := by
  unfold post; split <;> (try split) <;> (try split) <;> rfl

theorem pbPost_lens (τ : FT) (i : Instr) (t : Taint.T) : (pbPost τ i t).lens = t.lens := by
  unfold pbPost; split <;> (try split) <;> rfl

/-- No instruction's step changes what the base analysis knows of the regions' lengths. -/
theorem _root_.VG.X86_64.Taint.step_lens {τ τ' : Taint.T} {i : Instr} (h : Taint.step τ i = some τ') :
    τ'.lens = τ.lens := by
  cases i
  case vmovdquStore l _ _ =>
    cases l <;> simp only [Taint.step, storeStep, Option.ite_none_right_eq_some, Option.some.injEq] at h <;>
      obtain ⟨-, rfl⟩ := h <;> rfl
  case xop op =>
    cases op <;> simp only [Taint.step, noX, Option.some.injEq] at h <;> subst h <;> rfl
  all_goals
    simp only [Taint.step, storeStep, aluStep, adxStep, cmovStep, mulStep, mulxStep, noX,
      Option.ite_none_right_eq_some, Option.some.injEq, reduceCtorEq] at h
  all_goals first
    | (obtain ⟨-, -, rfl⟩ := h; rfl)
    | (obtain ⟨-, rfl⟩ := h; rfl)
    | (subst h; rfl)

theorem special_lens {τ : FT} {i : Instr} {t' : Taint.T} (h : special τ i = some t') : t'.lens = τ.t.lens := by
  unfold special at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | (simp only [storeStep, Option.ite_none_right_eq_some, Option.some.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl)
    | cases h

theorem baseStep_lens {τ : FT} {i : Instr} {t' : Taint.T} (h : baseStep τ i = some t') : t'.lens = τ.t.lens := by
  unfold baseStep at h
  split at h
  · rename_i t'' hs
    cases h
    exact special_lens hs
  · obtain ⟨t'', ht, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [pbPost_lens, argPost_lens, post_lens]
    rcases Taint.stepKD_spec τ.t i with ⟨h', -⟩ | ⟨a, b, h₁, h₂, hab⟩
    · rw [show X86_64.taint.step τ.t i = Taint.stepKD τ.t i from taint_step _ _, h'] at ht; cases ht
    · rw [show X86_64.taint.step τ.t i = Taint.stepKD τ.t i from taint_step _ _, h₁] at ht
      cases ht
      rw [hab.lens]
      exact Taint.step_lens h₂

theorem baseStep_sound {τ : FT} {i : Instr} {t' : Taint.T} {s₁ s₂ s₁' s₂' : State}
    (ha : Taint.Agree τ.t s₁ s₂) (hsp : s₁.gpr .rsp = s₂.gpr .rsp) (o₁ : One τ s₁) (o₂ : One τ s₂)
    (hsa : SaEq τ s₁ s₂) (hwr : s₁.wr = s₂.wr) (hpb : PbEq τ s₁ s₂)
    (h : baseStep τ i = some t') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Taint.Agree t' s₁' s₂' := by
  unfold baseStep at h
  split at h
  · rename_i t'' hs
    cases h
    exact special_sound ha o₁ o₂ hs e₁ e₂
  · obtain ⟨t'', ht, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨had, hb⟩ := X86_64.taint.step_sound ha ht e₁ e₂
    exact ⟨had, pbPost_sound ha hwr hpb
      (argPost_sound hsp o₁ o₂ hsa (post_sound ha.wf₁ ha.wf₂ o₁ o₂ hb e₁ e₂) e₁ e₂) e₁ e₂⟩

/-! ## The argument area, kept -/

/-- A byte of the argument area is not in the `n` bytes at window index `i`
if they end below it. -/
theorem aa_sep {τ : FT} {s : State} (hr : τ.room ≤ (s.gpr .rsp).toNat)
    (htop : (s.gpr .rsp).toNat + τ.depth + 8 + τ.an ≤ 2 ^ 64) {k : Nat} (hk : k < τ.an) {i n : Nat}
    (hi : i + n ≤ τ.room + τ.depth + 8) : ¬ (aa s τ k - wa s τ i).toNat < n := by
  simp only [aa, wa]
  rw [Offset.sub_toNat _ (by omega_using [hi]) (by omega_using [hr, htop, hk])]
  omega_using [hi]

theorem aa_shift {s s' : State} {τ τ' : FT}
    (h : s'.gpr .rsp - BitVec.ofNat 64 τ'.room = s.gpr .rsp - BitVec.ofNat 64 τ.room)
    (hd : τ'.room + τ'.depth = τ.room + τ.depth) : aa s' τ' = aa s τ := by
  have hw : wb s' τ' = wb s τ := h
  funext k; simp only [aa, wa]; rw [hw, hd]

/-- `aFree`, for a state of the same argument area. -/
theorem aFree_of {τ τ' : FT} {s s' : State} (haa : aa s' τ' = aa s τ) (han : τ'.an = τ.an)
    (h : ∀ k < τ.an, ∀ r ∈ s'.wr, ¬ r.Contains (aa s τ k) 1) :
    ∀ k < τ'.an, ∀ r ∈ s'.wr, ¬ r.Contains (aa s' τ' k) 1 := by
  rw [haa, han]; exact h

/-- `One.sp`, for a state of the same argument area. -/
theorem sp_of {τ τ' : FT} {s s' : State} (haa : aa s' τ' = aa s τ)
    (h : ∀ e ∈ τ'.sp, s'.mem.readW (aa s τ e.1) 64 = (region s' e.2.1).base + BitVec.ofNat 64 e.2.2) :
    ∀ e ∈ τ'.sp, s'.mem.readW (aa s' τ' e.1) 64 = (region s' e.2.1).base + BitVec.ofNat 64 e.2.2 := by
  rw [haa]; exact h

/-- The pointers of `sp` are kept by a change of memory that keeps the
argument area, the regions and its address. -/
theorem sp_keep {τ τ' : FT} {s s' : State} (o : One τ s) (hfit : ∀ e ∈ τ.sp, e.1 + 8 ≤ τ.an)
    (hm : ∀ k < τ.an, s'.mem (aa s τ k) = s.mem (aa s τ k)) (hwr : s'.wr = s.wr)
    (haa : aa s' τ' = aa s τ) (hsp : τ'.sp = τ.sp) :
    ∀ e ∈ τ'.sp, s'.mem.readW (aa s' τ' e.1) 64 = (region s' e.2.1).base + BitVec.ofNat 64 e.2.2 := by
  intro e he
  rw [hsp] at he
  rw [haa, show region s' e.2.1 = region s e.2.1 by simp only [region, hwr], ← o.sp e he]
  apply Mem.readW_congr
  intro j hj
  simp only [Nat.reduceDiv] at hj
  rw [aa_add]
  exact hm _ (by have := hfit e he; omega_using [hj, this])

/-- So are the public bytes of `sa`. -/
theorem sa_keep {τ τ' : FT} {s₁ s₂ s₁' s₂' : State} (inv : RInv τ s₁ s₂)
    (hm₁ : ∀ k < τ.an, s₁'.mem (aa s₁ τ k) = s₁.mem (aa s₁ τ k))
    (hm₂ : ∀ k < τ.an, s₂'.mem (aa s₁ τ k) = s₂.mem (aa s₁ τ k))
    (haa₁ : aa s₁' τ' = aa s₁ τ) (haa₂ : aa s₂' τ' = aa s₂ τ) (hsa : τ'.sa = τ.sa) : SaEq τ' s₁' s₂' := by
  intro e he k h1 h2
  rw [hsa] at he
  have hk := inv.saFit e he
  rw [haa₁, haa₂, ← aa_eq inv.rsp, hm₁ k (by omega_using [h2, hk]), hm₂ k (by omega_using [h2, hk])]
  have := inv.saEq e he k h1 h2
  rwa [← aa_eq inv.rsp] at this

/-! ## Bounds, flags and pointers in slots -/

theorem toNat_signExtend_of_msb {v : BitVec 32} (h : v.msb = false) : (v.signExtend 64).toNat = v.toNat := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false h, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le v.isLt (by decide))]

theorem ubNew_sound {τ : FT} {i : Instr} {p : Reg × Nat} {s s' : State} (o : One τ s)
    (h : ubNew τ i = some p) (e : exec i s = some s') : (s'.gpr p.1).toNat ≤ p.2 := by
  unfold ubNew at h
  split at h
  · rename_i d v
    split at h <;> [cases h; skip]
    rename_i hm
    cases h
    simp only [reduceExec, readSrc, Option.map_some, Option.some.injEq] at e
    subst e
    simp only [State.setReg, ↓reduceIte, toNat_signExtend_of_msb (Bool.of_not_eq_true hm), Nat.le_refl]
  · rename_i d v
    cases h
    simp only [reduceExec, readSrc32, Option.map_some, Option.some.injEq] at e
    subst e
    simp only [State.setReg32, State.setReg, ↓reduceIte, BitVec.toNat_setWidth]
    exact Nat.le_of_eq (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le v.isLt (by decide)))
  · rename_i d v
    split at h <;> [cases h; skip]
    rename_i hm
    cases h
    simp only [reduceExec, execAlu, readSrc, Option.bind_some, Option.some.injEq] at e
    subst e
    simp only [State.setReg, ↓reduceIte, BitVec.toNat_and]
    exact Nat.le_trans Nat.and_le_right (Nat.le_of_eq (toNat_signExtend_of_msb (Bool.of_not_eq_true hm)))
  · rename_i d v
    cases h
    simp only [reduceExec, execAlu32, readSrc32, Option.bind_some, Option.some.injEq] at e
    subst e
    simp only [State.setReg32, State.setReg, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_and]
    exact Nat.le_trans (Nat.mod_le _ _) Nat.and_le_right
  · rename_i d x
    split at h <;> [skip; cases h]
    rename_i hf
    simp only [beq_iff_eq] at hf
    obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp h
    have hd := o.ub _ (ubOf_some hB)
    have hcf := o.fl _ _ hf
    obtain ⟨v, c, hv, hc, rfl⟩ := execCmov_some (by simpa only [reduceExec] using e)
    simp only [readSrc, Option.some.injEq] at hv
    subst hv
    simp only [eval, hcf, Option.some.injEq] at hc
    subst hc
    simp only at hd ⊢
    rw [cmov_gpr]
    simp only [↓reduceIte]
    split
    · rename_i hlt; simp only [decide_eq_true_eq] at hlt; omega_using [hd, hlt]
    · exact hd
  · cases h

theorem ub_step {τ : FT} {i : Instr} {s s' : State} (o : One τ s) (e : exec i s = some s') :
    ∀ p ∈ (ubNew τ i).toList ++ ubKill τ.ub i, (s'.gpr p.1).toNat ≤ p.2 := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ubNew_sound o (Option.mem_toList.mp hp) e
  · simp only [ubKill, List.mem_filter, Bool.not_eq_true'] at hp
    rw [exec_gpr hp.2 e]
    exact o.ub p hp.1

theorem fl_step {i : Instr} {s s' : State} (e : exec i s = some s') :
    ∀ a b, flOf i = some (a, b) → s'.cf = some (decide ((s'.gpr a).toNat < (s'.gpr b).toNat)) := by
  intro a b h
  unfold flOf at h
  split at h
  · rename_i a' b'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [reduceExec, execAlu, readSrc, Option.bind_some, Option.some.injEq] at e
    subst e
    simp only [arithFlags, State.setFlags]
    rfl
  · cases h

theorem storeW_pos {i : Instr} {m : MemOp} {w : Nat} (h : storeW i = some (m, w)) : 0 < w := by
  cases i <;> simp only [storeW, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  all_goals first | (obtain ⟨-, rfl⟩ := h; decide) | skip
  rename_i len _ _
  cases len <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨-, rfl⟩ := h <;> decide

/-- Where a store `storeRange` bounds writes. -/
theorem storeRange_ea {τ : FT} {s : State} (hw : Wf τ.t s) (o : One τ s) {m : MemOp} {w ri lo hi : Nat}
    (h : storeRange τ m w = some (ri, lo, hi)) :
    ∃ d, s.ea m = byteAddr s ri d ∧ lo ≤ d ∧ d + w ≤ hi ∧ hi ≤ τ.t.lens.getD ri 0 := by
  unfold storeRange at h
  split at h
  · rename_i ri' d hm
    split at h <;> [rename_i hfit; cases h]
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨d, ea_of_addrOf hw hm, Nat.le_refl _, Nat.le_refl _, hfit⟩
  · obtain ⟨x, -, hea, hle, hfit⟩ := idxRange_ea hw o h
    exact ⟨lo + (s.gpr x).toNat, hea, Nat.le_add_right _ _, hle, hfit⟩

theorem mem_mbKill {mb : List (Nat × Nat × Nat × Nat)} {ri lo hi : Nat} {e : Nat × Nat × Nat × Nat}
    (h : e ∈ mbKill mb ri lo hi) : e ∈ mb ∧ (e.1 ≠ ri ∨ e.2.1 + 8 ≤ lo ∨ hi ≤ e.2.1) := by
  simp only [mbKill, List.mem_filter, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact ⟨h.1, by rcases h.2 with (h | h) | h <;> [exact .inl h; exact .inr (.inl h); exact .inr (.inr h)]⟩

theorem mbAfter_fit {τ : FT} {i : Instr} (hf : ∀ e ∈ τ.mb, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0) :
    ∀ e ∈ mbAfter τ i, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0 := by
  intro e he
  unfold mbAfter at he
  split at he
  · rename_i m w hsw
    split at he
    · rename_i ri lo hi hr
      have hk : ∀ e ∈ mbKill τ.mb ri lo hi, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0 :=
        fun e he => hf e (mem_mbKill he).1
      split at he
      · rename_i m' r
        split at he
        · rename_i _ pj pk _ ri' d' hb hm
          rcases List.mem_cons.mp he with rfl | he
          · simp only [storeW, Option.some.injEq, Prod.mk.injEq] at hsw
            obtain ⟨rfl, rfl⟩ := hsw
            simp only [storeRange, hm] at hr
            split at hr <;> [rename_i hfit; cases hr]
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact hfit
          · exact hk e he
        · exact hk e he
      · exact hk e he
    · cases he
  · split at he
    · cases he
    · exact hf e he

/-- The 8 bytes of a slot of `mb` are outside what a store bounded by
`[lo, hi)` of region `ri` writes. -/
theorem mb_keep {τ : FT} {i : Instr} {m : MemOp} {w ri lo hi : Nat} {s s' : State}
    (hw : Wf τ.t s) (o : One τ s) (hsw : storeW i = some (m, w)) (hr : storeRange τ m w = some (ri, lo, hi))
    (e : exec i s = some s') {q : Nat × Nat × Nat × Nat} (hq : q.2.1 + 8 ≤ τ.t.lens.getD q.1 0)
    (hsep : q.1 ≠ ri ∨ q.2.1 + 8 ≤ lo ∨ hi ≤ q.2.1) :
    s'.mem.readW (byteAddr s q.1 q.2.1) 64 = s.mem.readW (byteAddr s q.1 q.2.1) 64 := by
  obtain ⟨d, hea, hlo, hhi, hfit⟩ := storeRange_ea hw o hr
  have hw0 := storeW_pos hsw
  apply Mem.readW_congr
  intro k hk
  simp only [Nat.reduceDiv] at hk
  rw [byteAddr_add]
  apply exec_store hsw e
  rw [hea]
  exact byte_not_in hw hw0 (by omega_using [hhi, hfit]) (by omega_using [hq, hk]) (by omega_using [hsep, hlo, hhi, hk])

theorem mb_step {τ : FT} {i : Instr} {s s' : State} (hw : Wf τ.t s) (o : One τ s)
    (hf : ∀ e ∈ τ.mb, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0) (e : exec i s = some s') :
    ∀ q ∈ mbAfter τ i, s'.mem.readW (byteAddr s' q.1 q.2.1) 64 =
      (region s' q.2.2.1).base + BitVec.ofNat 64 q.2.2.2 := by
  have hwr := (exec_frame e).1
  have hba : ∀ j k, byteAddr s' j k = byteAddr s j k := fun j k => by simp only [byteAddr, region, hwr]
  have hrg : ∀ j, region s' j = region s j := fun j => by simp only [region, hwr]
  intro q hq
  rw [hba, hrg]
  unfold mbAfter at hq
  split at hq
  · rename_i m w hsw
    split at hq
    · rename_i ri lo hi hr
      have hk : ∀ q ∈ mbKill τ.mb ri lo hi, s'.mem.readW (byteAddr s q.1 q.2.1) 64 =
          (region s q.2.2.1).base + BitVec.ofNat 64 q.2.2.2 := fun q hq => by
        obtain ⟨hq, hsep⟩ := mem_mbKill hq
        rw [mb_keep hw o hsw hr e (hf q hq) hsep]
        exact o.mb q hq
      split at hq
      · rename_i m' r
        split at hq
        · rename_i _ _ b pj pk d' hb hm
          rcases List.mem_cons.mp hq with rfl | hq
          · simp only [storeW, Option.some.injEq, Prod.mk.injEq] at hsw
            obtain ⟨rfl, rfl⟩ := hsw
            simp only [storeRange, hm] at hr
            split at hr <;> [skip; cases hr]
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            obtain ⟨hbm, hbe⟩ := find_base hb
            simp only at hbe
            subst hbe
            rw [exec_store_eq e]
            simp only
            rw [← ea_of_addrOf hw hm]
            rw [BitVec.setWidth_eq]
            exact (Mem.readW_writeW_self64 s.mem _ (s.gpr b)).trans (hw.2 _ hbm)
          · exact hk q hq
        · exact hk q hq
      · exact hk q hq
    · cases hq
  · split at hq
    · cases hq
    · rename_i hwm
      rw [exec_mem (Bool.of_not_eq_true hwm) e]
      exact o.mb q hq

/-! ## The public bytes of the regions, after an instruction -/

/-- A masked store changes memory only within the 64 bytes at its address. -/
theorem exec_kStore {i : Instr} {m : MemOp} (hi : kStoreOp i = some m) {s s' : State}
    (e : exec i s = some s') : ∀ y, ¬ (y - s.ea m).toNat < 64 → s'.mem y = s.mem y := by
  intro y hy
  cases i <;> simp only [kStoreOp, reduceCtorEq, Option.some.injEq] at hi
  case kStore m' k x =>
    subst hi
    obtain ⟨V, rfl⟩ := State.storeMasked512_eq (by simpa only [reduceExec] using e)
    exact Mem.write_apply hy
  case kStore8 m' k x =>
    subst hi
    obtain ⟨V, rfl⟩ := State.storeMasked512B_eq (by simpa only [reduceExec] using e)
    exact Mem.write_apply hy

/-- The byte at offset `k` of region `j` is outside what a store bounded by
`[lo, hi)` of region `ri` writes. -/
theorem byte_keep {τ : FT} {m : MemOp} {w ri lo hi : Nat} {s s' : State}
    (hw : Wf τ.t s) (o : One τ s) (hw0 : 0 < w) (hr : storeRange τ m w = some (ri, lo, hi))
    (hst : ∀ y, ¬ (y - s.ea m).toNat < w → s'.mem y = s.mem y) {j k : Nat} (hk : k < τ.t.lens.getD j 0)
    (hsep : j ≠ ri ∨ k < lo ∨ hi ≤ k) : s'.mem (byteAddr s j k) = s.mem (byteAddr s j k) := by
  obtain ⟨d, hea, hlo, hhi, hfit⟩ := storeRange_ea hw o hr
  apply hst
  rw [hea]
  exact byte_not_in hw hw0 (by omega_using [hhi, hfit]) hk (by omega_using [hsep, hlo, hhi])

/-- After a store `stPub` says is of a public value, the two memories are
the same at the bytes it writes, and where they were. -/
theorem pub_store_mem {τ : FT} {i : Instr} {m : MemOp} {w : Nat} {s₁ s₂ s₁' s₂' : State}
    (hp : stPub τ i = true) (hsw : storeW i = some (m, w)) (ha : Taint.Agree τ.t s₁ s₂)
    (had : addrs i s₁ = addrs i s₂) (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    ∀ X, ((X - s₁.ea m).toNat < w ∨ s₁.mem X = s₂.mem X) → s₁'.mem X = s₂'.mem X := by
  intro X hX
  cases i <;> simp only [stPub, Bool.false_eq_true] at hp
  case store m' r =>
    simp only [storeW, Option.some.injEq, Prod.mk.injEq] at hsw; obtain ⟨rfl, rfl⟩ := hsw
    have hea : s₁.ea m' = s₂.ea m' := by simpa only [addrs, List.cons.injEq, and_true] using had
    simp only [reduceExec, State.store64] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]; split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    show (s₁.mem.writeW _ _) X = (s₂.mem.writeW _ _) X
    rw [← hea, ← ha.reg hp]; exact writeW_same _ hX
  case store32 m' r =>
    simp only [storeW, Option.some.injEq, Prod.mk.injEq] at hsw; obtain ⟨rfl, rfl⟩ := hsw
    have hea : s₁.ea m' = s₂.ea m' := by simpa only [addrs, List.cons.injEq, and_true] using had
    simp only [reduceExec, State.store32] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]; split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    show (s₁.mem.writeW _ _) X = (s₂.mem.writeW _ _) X
    rw [← hea, ← ha.reg hp]; exact writeW_same _ hX
  case store8 m' r =>
    simp only [storeW, Option.some.injEq, Prod.mk.injEq] at hsw; obtain ⟨rfl, rfl⟩ := hsw
    have hea : s₁.ea m' = s₂.ea m' := by simpa only [addrs, List.cons.injEq, and_true] using had
    simp only [reduceExec, State.store8] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]; split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    show (s₁.mem.writeW _ _) X = (s₂.mem.writeW _ _) X
    rw [← hea, ← ha.reg hp]; exact writeW_same _ hX
  case store16 m' r =>
    simp only [storeW, Option.some.injEq, Prod.mk.injEq] at hsw; obtain ⟨rfl, rfl⟩ := hsw
    have hea : s₁.ea m' = s₂.ea m' := by simpa only [addrs, List.cons.injEq, and_true] using had
    simp only [reduceExec, State.store16] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]; split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    show (s₁.mem.writeW _ _) X = (s₂.mem.writeW _ _) X
    rw [← hea, ← ha.reg hp]; exact writeW_same _ hX
  case movdquStore m' x =>
    simp only [storeW, Option.some.injEq, Prod.mk.injEq] at hsw; obtain ⟨rfl, rfl⟩ := hsw
    rw [Bool.and_eq_true] at hp
    have hea : s₁.ea m' = s₂.ea m' := by simpa only [addrs, List.cons.injEq, and_true] using had
    simp only [reduceExec, State.store128] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]; split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    show (s₁.mem.writeW _ _) X = (s₂.mem.writeW _ _) X
    rw [← hea, ← ha.xr x hp.1]; exact writeW_same _ hX

/-- The bytes `pbAfter` says are public after an instruction are. -/
theorem pb_step {τ : FT} {i : Instr} {s₁ s₂ s₁' s₂' : State} (inv : RInv τ s₁ s₂)
    (had : addrs i s₁ = addrs i s₂) (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    ∀ j k, (pbGet (pbAfter τ i) j).testBit k = true →
      k < τ.t.lens.getD j 0 ∧ s₁'.mem (byteAddr s₁' j k) = s₂'.mem (byteAddr s₂' j k) := by
  intro j k hk
  have hpb : ∀ j k, (pbGet τ.pb j).testBit k = true →
      k < τ.t.lens.getD j 0 ∧ s₁.mem (byteAddr s₁ j k) = s₂.mem (byteAddr s₁ j k) := fun j k h => by
    have := inv.pb j k h; rwa [byteAddr_wr inv.wr.symm] at this
  rw [byteAddr_wr (exec_frame e₁).1, byteAddr_wr (exec_frame e₂).1, byteAddr_wr inv.wr.symm]
  -- A store within `[lo, hi)` of region `ri`: the bytes outside it are as they were.
  have range : ∀ {m : MemOp} {w ri lo hi : Nat}, storeRange τ m w = some (ri, lo, hi) → 0 < w →
      (∀ y, ¬ (y - s₁.ea m).toNat < w → s₁'.mem y = s₁.mem y) →
      (∀ y, ¬ (y - s₂.ea m).toNat < w → s₂'.mem y = s₂.mem y) →
      (pbGet (pbMod (bclr · lo (hi - lo)) τ.pb ri) j).testBit k = true →
      k < τ.t.lens.getD j 0 ∧ s₁'.mem (byteAddr s₁ j k) = s₂'.mem (byteAddr s₁ j k) := by
    intro m w ri lo hi hr hw0 hst₁ hst₂ hk
    obtain ⟨d, -, hlo, hhi, -⟩ := storeRange_ea inv.base.wf₁ inv.one₁ hr
    have h : (pbGet τ.pb j).testBit k = true ∧ (j ≠ ri ∨ k < lo ∨ hi ≤ k) := by
      rw [pbGet_mod] at hk
      split at hk
      · rename_i hc
        rw [testBit_bclr] at hk
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
          Nat.not_le, Nat.not_lt] at hk
        exact ⟨hc.1 ▸ hk.1, by omega_using [hk, hlo, hhi, hw0]⟩
      · rename_i hc
        refine ⟨hk, .inl fun hj => ?_⟩
        rw [pbGet_ge (by omega_using [hc, hj])] at hk
        simp only [Nat.zero_testBit, Bool.false_eq_true] at hk
    have hlt := (hpb j k h.1).1
    have h₂ := byte_keep inv.base.wf₂ inv.one₂ hw0 hr hst₂ hlt h.2
    rw [byteAddr_wr inv.wr.symm] at h₂
    rw [byte_keep inv.base.wf₁ inv.one₁ hw0 hr hst₁ hlt h.2, h₂]
    exact ⟨hlt, (hpb j k h.1).2⟩
  unfold pbAfter at hk
  split at hk
  · rename_i m w hsw
    split at hk
    · -- A public value: the bytes written are the same, and the others as they were.
      rename_i hp
      have hmem := pub_store_mem hp hsw inv.base had e₁ e₂
      have hold : (pbGet τ.pb j).testBit k = true →
          k < τ.t.lens.getD j 0 ∧ s₁'.mem (byteAddr s₁ j k) = s₂'.mem (byteAddr s₁ j k) := fun h =>
        ⟨(hpb j k h).1, hmem _ (.inr (hpb j k h).2)⟩
      split at hk
      · rename_i r d hm
        split at hk
        · rename_i hfit
          rw [pbGet_mod] at hk
          split at hk
          · rename_i hc
            obtain ⟨rfl, -⟩ := hc
            rw [testBit_bset, Bool.or_eq_true] at hk
            rcases hk with hk | hk
            · exact hold hk
            · simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
              refine ⟨by omega_using [hk, hfit], hmem _ (.inl ?_)⟩
              rw [ea_of_addrOf inv.base.wf₁ hm, show k = d + (k - d) by omega_using [hk], ← byteAddr_add,
                Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
              exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega_using [hk])
          · exact hold hk
        · exact hold hk
      · exact hold hk
    · -- Any other store: the bytes it may write are no longer public.
      split at hk
      · rename_i ri lo hi hr
        exact range hr (storeW_pos hsw) (exec_store hsw e₁) (exec_store hsw e₂) hk
      · rw [pbGet_zero] at hk
        simp only [Nat.zero_testBit, Bool.false_eq_true] at hk
  · split at hk
    · split at hk
      · rename_i ri lo hi hr
        obtain ⟨m, hm, hr⟩ := Option.bind_eq_some_iff.mp hr
        exact range hr (by decide) (exec_kStore hm e₁) (exec_kStore hm e₂) hk
      · rw [pbGet_zero] at hk
        simp only [Nat.zero_testBit, Bool.false_eq_true] at hk
    · rename_i hwm
      rw [exec_mem (Bool.of_not_eq_true hwm) e₁, exec_mem (Bool.of_not_eq_true hwm) e₂]
      exact hpb j k hk

/-! ## Soundness: instructions -/

theorem step_sound {τ τ' : FT} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  unfold step at hs
  split at hs <;> [rename_i hok; cases hs]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨hok, hsp⟩ := hok
  split at hs <;> [rename_i t' ht; cases hs]
  cases hs
  have hl : t'.lens = τ.t.lens := baseStep_lens ht
  have inv := ha hok
  obtain ⟨had, hb⟩ := baseStep_sound inv.base inv.rsp inv.one₁ inv.one₂ inv.saEq inv.wr inv.pb ht e₁ e₂
  have hl' : (if writesMem i = true then { t' with slots := [] } else t').lens = τ.t.lens := by
    split <;> exact hl
  have hb' : Taint.Agree (if writesMem i = true then { t' with slots := [] } else t') s₁' s₂' := by
    split <;> [exact hb.noSlots; exact hb]
  have r₁ := exec_rsp hsp e₁
  have r₂ := exec_rsp hsp e₂
  obtain ⟨w₁, f₁⟩ := exec_frame e₁
  obtain ⟨w₂, f₂⟩ := exec_frame e₂
  have hfit := mbAfter_fit (i := i) inv.mbFit
  have hm₁ : ∀ k < τ.an, s₁'.mem (aa s₁ τ k) = s₁.mem (aa s₁ τ k) := fun k hk => f₁ _ (inv.aFree k hk)
  have hm₂ : ∀ k < τ.an, s₂'.mem (aa s₁ τ k) = s₂.mem (aa s₁ τ k) :=
    fun k hk => f₂ _ (by rw [← inv.wr]; exact inv.aFree k hk)
  have haa₁ : ∀ τ' : FT, τ'.room = τ.room → τ'.depth = τ.depth → aa s₁' τ' = aa s₁ τ :=
    fun τ' h1 h2 => aa_shift (by rw [r₁, h1]) (by rw [h1, h2])
  have haa₂ : ∀ τ' : FT, τ'.room = τ.room → τ'.depth = τ.depth → aa s₂' τ' = aa s₂ τ :=
    fun τ' h1 h2 => aa_shift (by rw [r₂, h1]) (by rw [h1, h2])
  refine ⟨had, fun _ => ⟨hb', by rw [r₁, r₂, inv.rsp], by rw [exec_unknowns e₁, exec_unknowns e₂, inv.unk],
    by rw [w₁, w₂, inv.wr], fun h => by rw [w₁]; exact inv.lens (hl' ▸ h), by rw [w₁]; exact inv.nfr,
    by rw [r₁]; exact inv.room, by rw [r₁]; exact inv.top, ?_, ?_, inv.rasIn, inv.rasSorted, ?_, ?_,
    fun e he => by rw [hl']; exact hfit e he,
    ⟨ub_step inv.one₁ e₁, fl_step e₁, mb_step inv.base.wf₁ inv.one₁ inv.mbFit e₁,
      sp_keep inv.one₁ inv.spFit hm₁ w₁ (haa₁ _ rfl rfl) rfl⟩,
    ⟨ub_step inv.one₂ e₂, fl_step e₂, mb_step inv.base.wf₂ inv.one₂ inv.mbFit e₂,
      sp_keep inv.one₂ inv.spFit (by rw [← aa_eq inv.rsp]; exact hm₂) w₂ (haa₂ _ rfl rfl) rfl⟩, ?_,
    by rw [r₁]; exact inv.aTop, aFree_of (haa₁ _ rfl rfl) rfl fun k hk r hr => inv.aFree k hk r (by rwa [w₁] at hr),
    inv.saFit, sa_keep inv hm₁ hm₂ (haa₁ _ rfl rfl) (haa₂ _ rfl rfl) rfl, inv.spFit,
    fun j k hk => by rw [hl']; exact pb_step inv had e₁ e₂ j k hk⟩⟩
  · intro i hi; simp only [region, w₁, r₁]; exact inv.frames i hi
  · intro i h₁ h₂; simp only [region, w₁, wb, r₁]; rw [w₁] at h₂; exact inv.others i h₁ h₂
  · intro j hj i hi; simp only [region, raSlot, wa, wb, w₁, r₁]; exact inv.rasFr j hj i hi
  · intro j hj hn hw
    have d := inv.dead j hj hn
    simp only [wa, wb] at hw d ⊢
    rw [w₁, r₁] at hw
    rw [r₁, r₂, f₁ _ hw, f₂ _ (by rw [← inv.wr, ← inv.rsp]; exact hw)]
    exact d hw
  · intro i hi; simp only [region, wa, wb, w₁, r₁]; exact inv.fw i hi

/-! ## Soundness: branches, joins and order -/

theorem cond_sound {τ : FT} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (h : (τ.ok && τ.t.flags) = true) : eval c s₁ = eval c s₂ := by
  simp only [Bool.and_eq_true] at h
  exact Taint.cond_sound (ha h.1).base h.2

/-- `RInv τ` gives `RInv σ` for a `σ` of the same frames that knows less. -/
theorem RInv.weaken {τ σ : FT} {s₁ s₂ : State} (inv : RInv τ s₁ s₂) (hn : σ.nfr = τ.nfr)
    (hd : σ.depth = τ.depth) (hr : σ.room = τ.room) (hra : σ.ras = τ.ras)
    (hb : Taint.Agree σ.t s₁ s₂) (hl : σ.t.lens = τ.t.lens)
    (hsec : ∀ j, ¬ InSec σ.sec j → ¬ InSec τ.sec j)
    (hub : ∀ p ∈ σ.ub, ∃ n, (p.1, n) ∈ τ.ub ∧ n ≤ p.2) (hfl : σ.fl = none ∨ σ.fl = τ.fl)
    (hmb : ∀ e ∈ σ.mb, e ∈ τ.mb) (hfw : σ.fw = τ.fw) (han : σ.an = τ.an)
    (hsa : ∀ e ∈ σ.sa, e ∈ τ.sa) (hsp : ∀ e ∈ σ.sp, e ∈ τ.sp)
    (hpb : ∀ i k, (pbGet σ.pb i).testBit k = true → (pbGet τ.pb i).testBit k = true) : RInv σ s₁ s₂ := by
  have e : ∀ s, wa s σ = wa s τ := fun s => by funext j; simp only [wa, wb, hr]
  have e' : ∀ s, raSlot s σ = raSlot s τ := fun s => by funext j; simp only [raSlot, e]
  have ea : ∀ s, aa s σ = aa s τ := fun s => by funext j; simp only [aa, e, hr, hd]
  have one : ∀ {s}, One τ s → One σ s := fun o =>
    ⟨fun p hp => by
      obtain ⟨n, hn, hle⟩ := hub p hp
      exact Nat.le_trans (o.ub (p.1, n) hn) hle,
     fun a b h => by
      rcases hfl with h' | h'
      · rw [h'] at h; cases h
      · exact o.fl a b (h' ▸ h),
     fun e he => o.mb e (hmb e he),
     fun e he => by rw [ea]; exact o.sp e (hsp e he)⟩
  refine ⟨hb, inv.rsp, inv.unk, inv.wr, fun x => inv.lens (hl ▸ x), hn ▸ inv.nfr, hr ▸ inv.room,
    hd ▸ inv.top, ?_, ?_, ?_, hra ▸ inv.rasSorted, ?_, ?_, ?_, one inv.one₁, one inv.one₂, ?_,
    by rw [hd, han]; exact inv.aTop, fun k hk r hr' => by rw [ea]; exact inv.aFree k (han ▸ hk) r hr',
    fun e he => han ▸ inv.saFit e (hsa e he),
    fun e he k h1 h2 => by rw [ea, ea]; exact inv.saEq e (hsa e he) k h1 h2,
    fun e he => han ▸ inv.spFit e (hsp e he),
    fun i k hk => by rw [hl]; exact inv.pb i k (hpb i k hk)⟩
  · rw [hn, hd]; exact inv.frames
  · intro i h₁ h₂; simp only [wb, hr, hd]; exact inv.others i (hn ▸ h₁) h₂
  · rw [hra, hr, hd]; exact inv.rasIn
  · rw [e', hra, hn]; exact inv.rasFr
  · intro j hj hnot hw
    rw [e] at hw ⊢; rw [e]
    exact inv.dead j (hr ▸ hd ▸ hj) (hsec j hnot) hw
  · intro e he; rw [hl]; exact inv.mbFit e (hmb e he)
  · intro i hi
    rw [e, List.getElem_of_eq hfw hi]
    exact inv.fw i (hfw ▸ hi)

theorem inSec_lor_left {a b j : Nat} (h : ¬ InSec (Nat.lor a b) j) : ¬ InSec a j := fun h' => h (by
  show (a ||| b).testBit j = true
  rw [Nat.testBit_or, show a.testBit j = true from h', Bool.true_or])

theorem inSec_lor_right {a b j : Nat} (h : ¬ InSec (Nat.lor a b) j) : ¬ InSec b j := fun h' => h (by
  show (a ||| b).testBit j = true
  rw [Nat.testBit_or, show b.testBit j = true from h', Bool.or_true])

theorem mem_ubMeet {l₁ l₂ : List (Reg × Nat)} {p : Reg × Nat}
    (h : p ∈ l₁.filterMap fun p => (ubOf l₂ p.1).map fun n => (p.1, max p.2 n)) :
    (∃ n, (p.1, n) ∈ l₁ ∧ n ≤ p.2) ∧ (∃ n, (p.1, n) ∈ l₂ ∧ n ≤ p.2) := by
  obtain ⟨q, hq, h⟩ := List.mem_filterMap.mp h
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨⟨q.2, hq, Nat.le_max_left _ _⟩, ⟨n, ubOf_some hn, Nat.le_max_right _ _⟩⟩

theorem meet_left {τ₁ τ₂ : FT} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  unfold meet
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩, hl⟩, -⟩, -⟩ := hc
    intro _
    refine (h h1).weaken rfl rfl rfl rfl (Taint.meet_left (h h1).base) (by simp [Taint.meet, hl])
      (fun j hn => inSec_lor_left hn) (fun p hp => (mem_ubMeet hp).1) ?_
      (fun e he => (List.mem_filter.mp he).1) rfl rfl (fun e he => (List.mem_filter.mp he).1)
      (fun e he => (List.mem_filter.mp he).1)
      (fun i k hk => by rw [pbGet_meet, Nat.testBit_and, Bool.and_eq_true] at hk; exact hk.1)
    simp only
    split <;> [exact .inr rfl; exact .inl rfl]
  · exact fun h => absurd h (by decide)

theorem meet_right {τ₁ τ₂ : FT} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  unfold meet
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, h2⟩, hn⟩, hd⟩, hr⟩, hra⟩, hl⟩, hfw⟩, han⟩ := hc
    intro _
    refine (h h2).weaken hn hd hr hra (Taint.meet_right (h h2).base) (by simp [Taint.meet, hl])
      (fun j hn => inSec_lor_right hn) (fun p hp => (mem_ubMeet hp).2) ?_
      (fun e he => by simpa using (List.mem_filter.mp he).2) hfw han
      (fun e he => by simpa using (List.mem_filter.mp he).2) (fun e he => by simpa using (List.mem_filter.mp he).2)
      (fun i k hk => by rw [pbGet_meet, Nat.testBit_and, Bool.and_eq_true] at hk; exact hk.2)
    simp only
    split
    · rename_i hf; simp only [beq_iff_eq] at hf; exact .inr hf
    · exact .inl rfl
  · exact fun h => absurd h (by decide)

theorem le_sound {τ σ : FT} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) : Agree τ s₁ s₂ := by
  intro hτ
  simp only [le, hτ, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem] at hle
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hn⟩, hd⟩, hr⟩, hra⟩, hb⟩, hsec⟩, hub⟩, hfl⟩, hmb⟩, hfw⟩, han⟩, hsa⟩, hsp⟩, hpb⟩ := hle
  have inv := h hs
  have hbase := Taint.le_sound (Taint.leK_eq ▸ hb) inv.base
  have hl : τ.t.lens = σ.t.lens := by
    have hb' := hb
    rw [Taint.leK_eq] at hb'; simp only [Taint.le, Bool.and_eq_true, beq_iff_eq] at hb'; exact hb'.1.1.1.1.2
  refine inv.weaken hn hd hr hra hbase hl (fun j hnot h' => hnot (bsub_bit hsec h')) ?_ ?_ hmb hfw
    han hsa hsp (fun i k hk => pbLe_bit hpb hk)
  · intro p hp
    have h := hub p hp
    cases hn : ubOf σ.ub p.1 with
    | none => rw [hn] at h; cases h
    | some n => rw [hn] at h; exact ⟨n, ubOf_some hn, by simpa using h⟩
  · rcases Bool.or_eq_true_iff.mp hfl with h | h
    · exact .inl (Option.isNone_iff_eq_none.mp h)
    · exact .inr (by simpa using h)

/-! ## The window -/

theorem addr_add_sub (p : Addr) (n r : Nat) : p + BitVec.ofNat 64 n - BitVec.ofNat 64 (r + n) = p - BitVec.ofNat 64 r := by
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 r), BitVec.sub_eq_add_neg, BitVec.neg_add,
    BitVec.sub_eq_add_neg, ← BitVec.add_assoc, BitVec.add_assoc p, BitVec.add_right_neg, BitVec.add_zero,
    BitVec.add_neg_eq_sub]

theorem addr_sub_sub (p : Addr) {n r : Nat} (h : n ≤ r) :
    p - BitVec.ofNat 64 n - BitVec.ofNat 64 (r - n) = p - BitVec.ofNat 64 r := by
  rw [Offset.sub_ofNat_eq p h, BitVec.add_sub_cancel]

theorem toNat_sub_ofNat (x : Addr) {n : Nat} (h : n ≤ x.toNat) : (x - BitVec.ofNat 64 n).toNat = x.toNat - n := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_using [h]),
    show 2 ^ 64 - n + x.toNat = x.toNat - n + 2 ^ 64 by omega_using [h], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [])]

theorem toNat_add_ofNat (x : Addr) {n : Nat} (h : x.toNat + n < 2 ^ 64) : (x + BitVec.ofNat 64 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_using [h]), Nat.mod_eq_of_lt h]

theorem wa_eq {s₁ s₂ : State} {τ : FT} (h : s₁.gpr .rsp = s₂.gpr .rsp) (j : Nat) : wa s₁ τ j = wa s₂ τ j := by
  simp only [wa, wb, h]

/-- An address within `n` bytes below the stack pointer is a window index below `room`. -/
theorem below_wa {τ : FT} {s : State} {n : Nat} (hn : n ≤ τ.room) (y : Addr) :
    y = wa s τ (τ.room - n + (y - (s.gpr .rsp - BitVec.ofNat 64 n)).toNat) := by
  simp only [wa, wb]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← Offset.sub_ofNat_eq _ hn, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.add_comm, BitVec.sub_add_cancel]

theorem wa_shift {s s' : State} {τ τ' : FT}
    (h : s'.gpr .rsp - BitVec.ofNat 64 τ'.room = s.gpr .rsp - BitVec.ofNat 64 τ.room) : wa s' τ' = wa s τ := by
  funext j; simp only [wa, wb, h]

theorem region_getElem {s : State} {i : Nat} (hi : i < s.wr.length) : region s i = s.wr[i] := by
  simp only [region, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem contains_self (a : Addr) {n : Nat} (h : 0 < n) : (⟨a, n⟩ : Region).Contains a 1 := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [h]

/-- The bytes of the window below the stack pointer are in no writable region. -/
theorem below_free {τ : FT} {s₁ s₂ : State} (inv : RInv τ s₁ s₂) {j : Nat} (hj : j < τ.room) :
    ∀ r ∈ s₁.wr, ¬ r.Contains (wa s₁ τ j) 1 := by
  intro r hr hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hroom := inv.room
  have htop := inv.top
  rw [← region_getElem hi] at hc
  by_cases hfr : i < τ.nfr
  · have h1 := inv.frames i hfr _ hc
    have hw : wa s₁ τ j = s₁.gpr .rsp - BitVec.ofNat 64 (τ.room - j) := by
      simp only [wa, wb]
      rw [Offset.sub_ofNat_eq _ (Nat.sub_le τ.room j), Nat.sub_sub_self (Nat.le_of_lt hj)]
    have hd := Offset.base_disjoint_below (s₁.gpr .rsp) (n := τ.room - j) (k := τ.depth) (by omega_using [hroom, htop])
    exact hd _ h1 (by rw [hw]; exact contains_self _ (by omega_using [hj]))
  · have hd := inv.others i (by omega_using [hfr]) hi
    exact hd _ hc (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hroom]))

theorem below_free' {τ : FT} {s₁ s₂ : State} (inv : RInv τ s₁ s₂) {n : Nat} (hn : n ≤ τ.room) :
    ∀ y, (y - (s₁.gpr .rsp - BitVec.ofNat 64 n)).toNat < n → ∀ r ∈ s₁.wr, ¬ r.Contains y 1 := by
  intro y hy
  rw [below_wa hn y]
  exact below_free inv (by omega_using [hn, hy])

/-- A byte of a region the base analysis knows is in the region. -/
theorem byte_in {t : Taint.T} {s : State} (hw : Wf t s) {i k : Nat} (hk : k < t.lens.getD i 0) :
    region s i ∈ s.wr ∧ (region s i).Contains (byteAddr s i k) 1 := by
  have hne := lens_ne (n := k + 1) (by omega_using []) hk
  obtain ⟨hi, hri⟩ := region_mem hw hne (i := i) (by omega_using [hk])
  have hli := region_len hw hne i
  have hb : (region s i).len ≤ 2 ^ 64 := by rw [hri]; exact (hw.1 hne).2.2 _ (List.getElem_mem _)
  refine ⟨hri ▸ List.getElem_mem _, ?_⟩
  simp only [Region.Contains, byteAddr]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk, hli, hb])]
  omega_using [hk, hli]

/-- The pointers of `mb` are kept by a change of memory outside the writable regions. -/
theorem mb_out {τ : FT} {s s' : State} (hw : Wf τ.t s) (o : One τ s)
    (hfit : ∀ e ∈ τ.mb, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0) (hwr : s'.wr = s.wr)
    (hm : ∀ y, (∃ r ∈ s.wr, r.Contains y 1) → s'.mem y = s.mem y) :
    ∀ e ∈ τ.mb, s'.mem.readW (byteAddr s' e.1 e.2.1) 64 = (region s' e.2.2.1).base + BitVec.ofNat 64 e.2.2.2 := by
  intro e he
  have hba : byteAddr s' e.1 e.2.1 = byteAddr s e.1 e.2.1 := by simp only [byteAddr, region, hwr]
  have hrg : region s' e.2.2.1 = region s e.2.2.1 := by simp only [region, hwr]
  rw [hba, hrg, ← o.mb e he]
  apply Mem.readW_congr
  intro k hk
  simp only [Nat.reduceDiv] at hk
  rw [byteAddr_add]
  have := hfit e he
  obtain ⟨h1, h2⟩ := byte_in hw (i := e.1) (k := e.2.1 + k) (by omega_using [hk, this])
  exact hm _ ⟨_, h1, h2⟩

/-- The public bytes of the regions are kept by a change of memory outside the writable regions. -/
theorem PbEq.out {τ τ' : FT} {s₁ s₂ s₁' s₂' : State} (h : PbEq τ s₁ s₂) (hw₁ : Wf τ.t s₁) (hw₂ : Wf τ.t s₂)
    (hwr₁ : s₁'.wr = s₁.wr) (hwr₂ : s₂'.wr = s₂.wr)
    (hm₁ : ∀ y, (∃ r ∈ s₁.wr, r.Contains y 1) → s₁'.mem y = s₁.mem y)
    (hm₂ : ∀ y, (∃ r ∈ s₂.wr, r.Contains y 1) → s₂'.mem y = s₂.mem y)
    (hpb : τ'.pb = τ.pb) (hl : τ'.t.lens = τ.t.lens) : PbEq τ' s₁' s₂' := by
  intro i k hk
  rw [hpb] at hk
  obtain ⟨h1, h2⟩ := h i k hk
  obtain ⟨a1, a2⟩ := byte_in hw₁ h1
  obtain ⟨b1, b2⟩ := byte_in hw₂ h1
  rw [hl, byteAddr_wr hwr₁, byteAddr_wr hwr₂, hm₁ _ ⟨_, a1, a2⟩, hm₂ _ ⟨_, b1, b2⟩]
  exact ⟨h1, h2⟩

/-- The base analysis's agreement after a call or a return: the stack pointer
moves the same way in both runs, and memory changes only to equal values. -/
theorem agree_killSp {t : Taint.T} {s₁ s₂ s₁' s₂' : State} (ha : Taint.Agree t s₁ s₂)
    (hsp : s₁'.gpr .rsp = s₂'.gpr .rsp)
    (hg₁ : ∀ r, r ≠ .rsp → s₁'.gpr r = s₁.gpr r) (hg₂ : ∀ r, r ≠ .rsp → s₂'.gpr r = s₂.gpr r)
    (hf₁ : s₁'.cf = s₁.cf ∧ s₁'.zf = s₁.zf ∧ s₁'.sf = s₁.sf ∧ s₁'.of = s₁.of)
    (hf₂ : s₂'.cf = s₂.cf ∧ s₂'.zf = s₂.zf ∧ s₂'.sf = s₂.sf ∧ s₂'.of = s₂.of)
    (hx₁ : s₁'.xmm = s₁.xmm) (hx₂ : s₂'.xmm = s₂.xmm) (hw₁ : s₁'.wr = s₁.wr) (hw₂ : s₂'.wr = s₂.wr)
    (hm : ∀ a, (s₁'.mem a = s₁.mem a ∧ s₂'.mem a = s₂.mem a) ∨ s₁'.mem a = s₂'.mem a) :
    Taint.Agree (killSp t) s₁' s₂' where
  rf := ⟨fun r hr => by
      by_cases h : r = .rsp
      · subst h; exact hsp
      · rw [hg₁ r h, hg₂ r h]; exact ha.rf.1 r hr,
    fun hf => by
      obtain ⟨a, b, c, d⟩ := ha.rf.2 hf
      rw [hf₁.1, hf₂.1, hf₁.2.1, hf₂.2.1, hf₁.2.2.1, hf₂.2.2.1, hf₁.2.2.2, hf₂.2.2.2]
      exact ⟨a, b, c, d⟩⟩
  wr h := by rw [hw₁, hw₂]; exact ha.wr h
  wf₁ := ⟨fun h => by rw [hw₁]; exact ha.wf₁.1 h, kill_bases ha.wf₁ hw₁ hg₁⟩
  wf₂ := ⟨fun h => by rw [hw₂]; exact ha.wf₂.1 h, kill_bases ha.wf₂ hw₂ hg₂⟩
  ok := ha.ok
  slots sl h k h₁ h₂ := by
    have hb : ∀ s s' : State, s'.wr = s.wr → byteAddr s' sl.1 k = byteAddr s sl.1 k := fun s s' h => by
      simp only [byteAddr, region, h]
    rw [hb _ _ hw₁, hb _ _ hw₂, ← ha.byteAddr_eq h h₂]
    rcases hm (byteAddr s₁ sl.1 k) with ⟨e₁, e₂⟩ | e
    · have := ha.slots sl h k h₁ h₂
      rw [← ha.byteAddr_eq h h₂] at this
      rw [e₁, e₂]; exact this
    · exact e
  lo := noLo
  xr r h := by rw [hx₁, hx₂]; exact ha.xr r h

/-- `[p, p + d)` without its first `b` bytes. -/
theorem sub_shrink {r : Region} {p : Addr} {d b : Nat} (hs : Region.Sub r ⟨p, d⟩)
    (hd : Region.Disjoint r ⟨p, b⟩) (hb : b ≤ d) (hd64 : d < 2 ^ 64) :
    Region.Sub r ⟨p + BitVec.ofNat 64 b, d - b⟩ := by
  intro a ha
  have h1 := hs a ha
  have h2 := hd a ha
  simp only [Region.Contains] at h1 h2 ⊢
  rw [Offset.toNat_sub_add _ _ (by omega), show 2 ^ 64 - b + (a - p).toNat = (a - p).toNat - b + 2 ^ 64 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

theorem sub_down (p : Addr) (n d : Nat) : Region.Sub ⟨p, d⟩ ⟨p - BitVec.ofNat 64 n, d + n⟩ := by
  have := Offset.sub_base (p - BitVec.ofNat 64 n) (d := n) (n := d) (k := d + n) (by omega_using [])
  rwa [BitVec.sub_add_cancel] at this

theorem Region.sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

/-! ## Soundness: calls and returns -/

/-- What a call does to the state, field by field. -/
structure CallFx (s s' : State) : Prop where
  sp : s'.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 8
  gpr : ∀ r, r ≠ .rsp → s'.gpr r = s.gpr r
  flags : s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of
  xmm : s'.xmm = s.xmm
  wr : s'.wr = s.wr
  unk : s'.unknowns = fun n => s.unknowns (n + 1)
  mem : s'.mem = s.mem.writeW (s.gpr .rsp - BitVec.ofNat 64 8) (s.unknowns 0)

theorem callFx {s s' : State} (h : isa.call s = some s') : CallFx s s' := by
  simp only [isa, call, Option.some.injEq] at h
  subst h
  exact ⟨by simp only [State.setReg, ↓reduceIte]; rfl, fun _ h => setReg_ne h, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

theorem call_sound {τ τ' : FT} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂) (hs : callF τ = some τ')
    (e₁ : isa.call s₁ = some s₁') (e₂ : isa.call s₂ = some s₂') :
    isa.callAddrs s₁ = isa.callAddrs s₂ ∧ Agree τ' s₁' s₂' := by
  unfold callF at hs
  split at hs <;> [rename_i hc; cases hs]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hok, h8⟩ := hc
  cases hs
  have inv := ha hok
  have c₁ := callFx e₁
  have c₂ := callFx e₂
  refine ⟨by simp only [inv.rsp], fun _ => ?_⟩
  have hroom := inv.room
  have htop := inv.top
  -- What the call writes: the 8 bytes below the stack pointer, the same in both runs.
  have hout₁ : ∀ y, ¬ (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8 → s₁'.mem y = s₁.mem y := by
    intro y hy; rw [c₁.mem]; exact writeW_out (by simpa using hy)
  have hout₂ : ∀ y, ¬ (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8 → s₂'.mem y = s₂.mem y := by
    intro y hy; rw [c₂.mem, ← inv.rsp]; exact writeW_out (by simpa using hy)
  have hin : ∀ y, (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8 → s₁'.mem y = s₂'.mem y := by
    intro y hy
    have hy' : (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 64 / 8 := hy
    rw [c₁.mem, c₂.mem]
    simp only [Mem.writeW, Mem.write, ← inv.rsp, ← inv.unk, hy', ↓reduceIte]
  have hm : ∀ y, (s₁'.mem y = s₁.mem y ∧ s₂'.mem y = s₂.mem y) ∨ s₁'.mem y = s₂'.mem y := by
    intro y
    by_cases hy : (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8
    · exact .inr (hin y hy)
    · exact .inl ⟨hout₁ y hy, hout₂ y hy⟩
  have hfree₁ := below_free' inv (n := 8) (by omega_using [h8])
  have hsh₁ : s₁'.gpr .rsp - BitVec.ofNat 64 (τ.room - 8) = s₁.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₁.sp]; exact addr_sub_sub _ h8
  have hsh₂ : s₂'.gpr .rsp - BitVec.ofNat 64 (τ.room - 8) = s₂.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₂.sp]; exact addr_sub_sub _ h8
  have hr8 : (s₁.gpr .rsp - BitVec.ofNat 64 8).toNat = (s₁.gpr .rsp).toNat - 8 := toNat_sub_ofNat _ (by omega_using [h8, hroom])
  have hwa8 : wa s₁ τ (τ.room - 8) = s₁.gpr .rsp - BitVec.ofNat 64 8 := by
    simp only [wa, wb]; rw [← Offset.sub_ofNat_eq _ h8]
  have hrg : ∀ i, region s₁' i = region s₁ i := fun i => by simp only [region, c₁.wr]
  -- The argument area, above the return address the call writes.
  have haa₁ : ∀ τ' : FT, τ'.room = τ.room - 8 → τ'.depth = τ.depth + 8 → aa s₁' τ' = aa s₁ τ :=
    fun τ' h1 h2 => aa_shift (by rw [h1]; exact hsh₁) (by rw [h1, h2]; omega_using [h8])
  have haa₂ : ∀ τ' : FT, τ'.room = τ.room - 8 → τ'.depth = τ.depth + 8 → aa s₂' τ' = aa s₂ τ :=
    fun τ' h1 h2 => aa_shift (by rw [h1]; exact hsh₂) (by rw [h1, h2]; omega_using [h8])
  have hm₁ : ∀ k < τ.an, s₁'.mem (aa s₁ τ k) = s₁.mem (aa s₁ τ k) := fun k hk =>
    hout₁ _ (by rw [← hwa8]; exact aa_sep inv.room (inv.aTop (by omega_using [hk])) hk (by omega_using []))
  have hm₂ : ∀ k < τ.an, s₂'.mem (aa s₁ τ k) = s₂.mem (aa s₁ τ k) := fun k hk =>
    hout₂ _ (by rw [← hwa8]; exact aa_sep inv.room (inv.aTop (by omega_using [hk])) hk (by omega_using []))
  refine ⟨agree_killSp inv.base (by rw [c₁.sp, c₂.sp, inv.rsp]) c₁.gpr c₂.gpr c₁.flags c₂.flags c₁.xmm c₂.xmm
      c₁.wr c₂.wr hm,
    by rw [c₁.sp, c₂.sp, inv.rsp], by rw [c₁.unk, c₂.unk, inv.unk], by rw [c₁.wr, c₂.wr, inv.wr],
    fun h => by rw [c₁.wr]; exact inv.lens h, by rw [c₁.wr]; exact inv.nfr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, inv.mbFit, ?_, ?_, ?_,
    fun h => by dsimp only at h ⊢; rw [c₁.sp, hr8]; have := inv.aTop h; omega_using [h8, hroom, this],
    aFree_of (haa₁ _ rfl rfl) rfl fun k hk r hr => inv.aFree k hk r (by rwa [c₁.wr] at hr),
    inv.saFit, sa_keep inv hm₁ hm₂ (haa₁ _ rfl rfl) (haa₂ _ rfl rfl) rfl, inv.spFit,
    inv.pb.out inv.base.wf₁ inv.base.wf₂ c₁.wr c₂.wr
      (fun y ⟨r, hr, hc⟩ => hout₁ y (fun hy => hfree₁ y hy r hr hc))
      (fun y ⟨r, hr, hc⟩ => hout₂ y (fun hy => hfree₁ y hy r (inv.wr ▸ hr) hc)) rfl rfl⟩
  · dsimp only; rw [c₁.sp]; omega_using [hroom, hr8]
  · dsimp only; rw [c₁.sp]; omega_using [h8, hroom, htop, hr8]
  · intro i hi
    dsimp only
    rw [hrg, c₁.sp]
    exact Region.sub_trans (inv.frames i hi) (sub_down _ 8 τ.depth)
  · intro i h₁ h₂
    rw [c₁.wr] at h₂
    have := inv.others i h₁ h₂
    simp only [wb] at this ⊢
    rw [hrg, hsh₁, show τ.room - 8 + (τ.depth + 8) = τ.room + τ.depth by omega_using [h8]]
    exact this
  · intro j hj
    dsimp only at hj ⊢
    rcases List.mem_cons.mp hj with rfl | hj
    · omega_using []
    · have := inv.rasIn j hj; omega_using [this]
  · dsimp only
    exact List.pairwise_cons.mpr ⟨fun j hj => by have := inv.rasIn j hj; omega_using [h8, this], inv.rasSorted⟩
  · intro j hj i hi
    simp only [raSlot]
    -- The taint is given up to its `room`: left to unification, `wa_shift hsh₁` takes seconds to find it.
    rw [wa_shift (τ := τ) (τ' := ⟨_, _, _, _, τ.room - 8, _, _, _, _, _, _, _, _, _, _⟩) hsh₁, hrg]
    dsimp only at hj
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [hwa8]
      exact Region.Disjoint.sub_left (Offset.base_disjoint_below (s₁.gpr .rsp) (n := 8) (k := τ.depth) (by omega_using [h8, hroom, htop]))
        (inv.frames i hi)
    · exact inv.rasFr j hj i hi
  · intro j hj hn hw
    rw [c₁.wr] at hw
    dsimp only at hj
    simp only [wa, wb] at hw ⊢
    rw [hsh₁] at hw
    rw [hsh₁, hsh₂, ← inv.rsp]
    show s₁'.mem (wa s₁ τ j) = s₂'.mem (wa s₁ τ j)
    rcases hm (wa s₁ τ j) with ⟨h₁, h₂⟩ | h
    · rw [h₁, h₂]
      have := inv.dead j (by omega_using [h8, hj]) hn hw
      rwa [← wa_eq inv.rsp] at this
    · exact h
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), ?_, ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₁.gpr _ hp.2]; exact inv.one₁.ub p hp.1
    · exact mb_out (τ := τ) inv.base.wf₁ inv.one₁ inv.mbFit c₁.wr
        (fun y ⟨r, hr, hc⟩ => hout₁ y (fun hy => hfree₁ y hy r hr hc))
    · exact sp_keep inv.one₁ inv.spFit hm₁ c₁.wr (haa₁ _ rfl rfl) rfl
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), ?_, ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₂.gpr _ hp.2]; exact inv.one₂.ub p hp.1
    · exact mb_out (τ := τ) inv.base.wf₂ inv.one₂ inv.mbFit c₂.wr
        (fun y ⟨r, hr, hc⟩ => hout₂ y (fun hy => hfree₁ y hy r (inv.wr ▸ hr) hc))
    · exact sp_keep inv.one₂ inv.spFit (by rw [← aa_eq inv.rsp]; exact hm₂) c₂.wr (haa₂ _ rfl rfl) rfl
  · intro i hi; simp only [hrg, wa, wb]; rw [hsh₁]; exact inv.fw i hi

theorem retFx {a b c : State} (h : isa.ret a b = some c) :
    c.gpr .rsp = b.gpr .rsp + BitVec.ofNat 64 8 ∧ (∀ r, r ≠ .rsp → c.gpr r = b.gpr r) ∧
    (c.cf = b.cf ∧ c.zf = b.zf ∧ c.sf = b.sf ∧ c.of = b.of) ∧ c.xmm = b.xmm ∧ c.wr = b.wr ∧
    c.unknowns = b.unknowns ∧ c.mem = b.mem := by
  simp only [isa, ret] at h
  split at h <;> [skip; cases h]
  cases h
  exact ⟨by simp only [State.setReg, ↓reduceIte]; rfl, fun _ h => setReg_ne h, ⟨rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl⟩

theorem ret_sound {τ τ' : FT} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂) (hs : retF τ = some τ')
    (e₁ : isa.ret a₁ b₁ = some c₁) (e₂ : isa.ret a₂ b₂ = some c₂) :
    isa.retAddrs b₁ = isa.retAddrs b₂ ∧ Agree τ' c₁ c₂ := by
  unfold retF at hs
  split at hs <;> [rename_i hc; cases hs]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨hok, hhd⟩, h8⟩ := hc
  cases hs
  have inv := ha hok
  obtain ⟨sp₁, g₁, f₁, x₁, w₁, u₁, m₁⟩ := retFx e₁
  obtain ⟨sp₂, g₂, f₂, x₂, w₂, u₂, m₂⟩ := retFx e₂
  refine ⟨by simp only [inv.rsp], fun _ => ?_⟩
  have hroom := inv.room
  have htop := inv.top
  obtain ⟨tl, hras⟩ : ∃ tl, τ.ras = τ.room :: tl := by
    cases h : τ.ras with
    | nil => rw [h] at hhd; cases hhd
    | cons x tl => rw [h] at hhd; cases hhd; exact ⟨tl, rfl⟩
  have hsorted := inv.rasSorted
  rw [hras] at hsorted
  have hsh₁ : c₁.gpr .rsp - BitVec.ofNat 64 (τ.room + 8) = b₁.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [sp₁]; exact addr_add_sub _ _ _
  have hsh₂ : c₂.gpr .rsp - BitVec.ofNat 64 (τ.room + 8) = b₂.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [sp₂]; exact addr_add_sub _ _ _
  have hr8 : (b₁.gpr .rsp + BitVec.ofNat 64 8).toNat = (b₁.gpr .rsp).toNat + 8 := toNat_add_ofNat _ (by omega_using [h8, htop])
  have hwaR : wa b₁ τ τ.room = b₁.gpr .rsp := by simp only [wa, wb, BitVec.sub_add_cancel]
  have hrg : ∀ i, region c₁ i = region b₁ i := fun i => by simp only [region, w₁]
  -- The stack pointer after the return, in the innermost frame (`spBase`).
  have hsp₁ : ∀ p ∈ spBase τ, c₁.gpr p.1 = (region c₁ p.2.1).base + BitVec.ofNat 64 p.2.2 := by
    intro p hp
    unfold spBase at hp
    split at hp <;> [rename_i a ha; cases hp]
    split at hp <;> [rename_i hle; cases hp]
    rcases List.mem_singleton.mp hp with rfl
    obtain ⟨tl, hfw⟩ : ∃ tl, τ.fw = a :: tl := by
      cases h : τ.fw with
      | nil => rw [h] at ha; cases ha
      | cons x tl => rw [h] at ha; cases ha; exact ⟨tl, rfl⟩
    have h0 := inv.fw 0 (by rw [hfw]; exact Nat.succ_pos _)
    rw [List.getElem_of_eq hfw, List.getElem_cons_zero] at h0
    dsimp only
    rw [hrg, h0, sp₁, wa, wb, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hle,
      BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have hsp₂ : ∀ p ∈ spBase τ, c₂.gpr p.1 = (region c₂ p.2.1).base + BitVec.ofNat 64 p.2.2 := by
    intro p hp
    have h := hsp₁ p hp
    have hr : p.1 = .rsp := by
      unfold spBase at hp
      split at hp <;> [skip; cases hp]
      split at hp <;> [skip; cases hp]
      rw [List.mem_singleton.mp hp]
    rw [hr] at h ⊢
    rw [show region c₂ p.2.1 = region c₁ p.2.1 by simp only [region, w₁, w₂, inv.wr], sp₂, ← inv.rsp, ← sp₁]
    exact h
  have hk := agree_killSp inv.base (by rw [sp₁, sp₂, inv.rsp]) g₁ g₂ f₁ f₂ x₁ x₂ w₁ w₂
      (fun y => .inl ⟨by rw [m₁], by rw [m₂]⟩)
  have hbase : Taint.Agree { killSp τ.t with bases := spBase τ ++ kill τ.t .rsp } c₁ c₂ :=
    ⟨hk.rf, hk.wr,
      ⟨hk.wf₁.1, fun p hp => (List.mem_append.mp hp).elim (hsp₁ p) (hk.wf₁.2 p)⟩,
      ⟨hk.wf₂.1, fun p hp => (List.mem_append.mp hp).elim (hsp₂ p) (hk.wf₂.2 p)⟩,
      hk.ok, hk.slots, hk.lo, hk.xr⟩
  have haa₁ : ∀ τ' : FT, τ'.room = τ.room + 8 → τ'.depth = τ.depth - 8 → aa c₁ τ' = aa b₁ τ :=
    fun τ' h1 h2 => aa_shift (by rw [h1]; exact hsh₁) (by rw [h1, h2]; omega_using [h8])
  have haa₂ : ∀ τ' : FT, τ'.room = τ.room + 8 → τ'.depth = τ.depth - 8 → aa c₂ τ' = aa b₂ τ :=
    fun τ' h1 h2 => aa_shift (by rw [h1]; exact hsh₂) (by rw [h1, h2]; omega_using [h8])
  have hm₁ : ∀ k < τ.an, c₁.mem (aa b₁ τ k) = b₁.mem (aa b₁ τ k) := fun _ _ => by rw [m₁]
  have hm₂ : ∀ k < τ.an, c₂.mem (aa b₁ τ k) = b₂.mem (aa b₁ τ k) := fun _ _ => by rw [m₂]
  refine ⟨hbase,
    by rw [sp₁, sp₂, inv.rsp], by rw [u₁, u₂, inv.unk], by rw [w₁, w₂, inv.wr],
    fun h => by rw [w₁]; exact inv.lens h, by rw [w₁]; exact inv.nfr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, inv.mbFit, ?_, ?_, ?_,
    fun h => by dsimp only at h ⊢; rw [sp₁, hr8]; have := inv.aTop h; omega_using [h8, this],
    aFree_of (haa₁ _ rfl rfl) rfl fun k hk r hr => inv.aFree k hk r (by rwa [w₁] at hr),
    inv.saFit, sa_keep inv hm₁ hm₂ (haa₁ _ rfl rfl) (haa₂ _ rfl rfl) rfl, inv.spFit,
    inv.pb.out inv.base.wf₁ inv.base.wf₂ w₁ w₂ (fun y _ => by rw [m₁]) (fun y _ => by rw [m₂]) rfl rfl⟩
  · dsimp only; rw [sp₁]; omega_using [hroom, hr8]
  · dsimp only; rw [sp₁]; omega_using [htop, hr8]
  · intro i hi
    dsimp only
    rw [hrg, sp₁]
    have hd := inv.rasFr τ.room (by rw [hras]; exact List.mem_cons_self) i hi
    simp only [raSlot, hwaR] at hd
    exact sub_shrink (inv.frames i hi) hd h8 (by omega_using [htop])
  · intro i h₁ h₂
    rw [w₁] at h₂
    have := inv.others i h₁ h₂
    simp only [wb] at this ⊢
    rw [hrg, hsh₁, show τ.room + 8 + (τ.depth - 8) = τ.room + τ.depth by omega_using [h8]]
    exact this
  · intro j hj
    dsimp only at hj ⊢
    rw [hras] at hj
    have h1 := (List.pairwise_cons.mp hsorted).1 j hj
    have h2 := inv.rasIn j (by rw [hras]; exact List.mem_cons_of_mem _ hj)
    omega_using [h1, h2]
  · dsimp only
    rw [hras]
    exact (List.pairwise_cons.mp hsorted).2
  · intro j hj i hi
    dsimp only at hj
    rw [hras] at hj
    simp only [raSlot, wa, wb]
    rw [hsh₁, hrg]
    exact inv.rasFr j (by rw [hras]; exact List.mem_cons_of_mem _ hj) i hi
  · intro j hj hn hw
    rw [w₁] at hw
    dsimp only at hj
    simp only [wa, wb] at hw ⊢
    rw [hsh₁] at hw
    rw [hsh₁, hsh₂, m₁, m₂]
    exact inv.dead j (by omega_using [h8, hj]) hn hw
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), ?_, ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [g₁ _ hp.2]; exact inv.one₁.ub p hp.1
    · exact mb_out (τ := τ) inv.base.wf₁ inv.one₁ inv.mbFit w₁ (fun y _ => by rw [m₁])
    · exact sp_keep inv.one₁ inv.spFit hm₁ w₁ (haa₁ _ rfl rfl) rfl
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), ?_, ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [g₂ _ hp.2]; exact inv.one₂.ub p hp.1
    · exact mb_out (τ := τ) inv.base.wf₂ inv.one₂ inv.mbFit w₂ (fun y _ => by rw [m₂])
    · exact sp_keep inv.one₂ inv.spFit (fun _ _ => by rw [m₂]) w₂ (haa₂ _ rfl rfl) rfl
  · intro i hi; simp only [hrg, wa, wb]; rw [hsh₁]; exact inv.fw i hi

/-! ## Soundness: frames -/

/-- What the allocation of a frame of `b` bytes does to the state. -/
structure AllocFx (b : Nat) (s s' : State) : Prop where
  sp : s'.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 b
  gpr : ∀ r, r ≠ .rsp → s'.gpr r = s.gpr r
  flags : s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of
  xmm : s'.xmm = s.xmm
  wr : s'.wr = ⟨s.gpr .rsp - BitVec.ofNat 64 b, b⟩ :: s.wr
  unk : s'.unknowns = s.unknowns
  mem : s'.mem = s.mem
  lt : b < 4096

theorem allocFx {b : Nat} {s s' : State} (h : isa.push (.alloc b) s = some s') : AllocFx b s s' := by
  simp only [isa, push] at h
  split at h <;> [rename_i hc; cases h]
  cases h
  exact ⟨by simp only [State.setReg, ↓reduceIte], fun _ h => setReg_ne h, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
    rfl, hc.2.1⟩

theorem region_cons_zero {s : State} {r : Region} {l : List Region} (h : s.wr = r :: l) : region s 0 = r := by
  simp only [region, h, List.getD_cons_zero]

theorem region_cons_succ {s : State} {r : Region} {l : List Region} (h : s.wr = r :: l) (i : Nat) :
    region s (i + 1) = l.getD i ⟨0, 0⟩ := by
  simp only [region, h, List.getD_cons_succ]

/-- The wellformedness facts of the writable regions, whether or not the
base analysis knows any. -/
theorem wr_facts {τ : FT} {s₁ s₂ : State} (inv : RInv τ s₁ s₂) :
    List.Forall₂ (fun r l => l ≤ r.len) s₁.wr τ.t.lens ∧ s₁.wr.Pairwise Region.Disjoint ∧
      ∀ r ∈ s₁.wr, r.len ≤ 2 ^ 64 := by
  by_cases h : τ.t.lens = []
  · rw [inv.lens h, h]; exact ⟨.nil, .nil, fun _ h => by cases h⟩
  · exact inv.base.wf₁.1 h

theorem push_sound {τ τ' : FT} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : pushF τ i = some τ') (e₁ : isa.push i s₁ = some s₁') (e₂ : isa.push i s₂ = some s₂') :
    isa.addrs i s₁ = isa.addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i <;> simp only [pushF, reduceCtorEq] at hs
  rename_i b
  split at hs <;> [rename_i hc; cases hs]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hok, hb0⟩, hb4⟩, hb8⟩, hbr⟩ := hc
  cases hs
  have inv := ha hok
  have c₁ := allocFx e₁
  have c₂ := allocFx e₂
  refine ⟨rfl, fun _ => ?_⟩
  have hroom := inv.room
  have htop := inv.top
  have hsh₁ : s₁'.gpr .rsp - BitVec.ofNat 64 (τ.room - b) = s₁.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₁.sp]; exact addr_sub_sub _ hbr
  have hsh₂ : s₂'.gpr .rsp - BitVec.ofNat 64 (τ.room - b) = s₂.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₂.sp]; exact addr_sub_sub _ hbr
  have hrb : (s₁.gpr .rsp - BitVec.ofNat 64 b).toNat = (s₁.gpr .rsp).toNat - b := toNat_sub_ofNat _ (by omega_using [hbr, hroom])
  have hwab : ∀ k, wa s₁ τ (τ.room - b + k) = s₁.gpr .rsp - BitVec.ofNat 64 b + BitVec.ofNat 64 k := fun k => by
    simp only [wa, wb]
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← Offset.sub_ofNat_eq _ hbr]
  have hr0 : region s₁' 0 = ⟨s₁.gpr .rsp - BitVec.ofNat 64 b, b⟩ := region_cons_zero c₁.wr
  have hrs : ∀ i, region s₁' (i + 1) = region s₁ i := fun i => region_cons_succ c₁.wr i
  have hrs₂ : ∀ i, region s₂' (i + 1) = region s₂ i := fun i => region_cons_succ c₂.wr i
  have hba : ∀ i k, byteAddr s₁' (i + 1) k = byteAddr s₁ i k := fun i k => by simp only [byteAddr, hrs]
  have hba₂ : ∀ i k, byteAddr s₂' (i + 1) k = byteAddr s₂ i k := fun i k => by simp only [byteAddr, hrs₂]
  have hfree := below_free' inv (n := b) hbr
  obtain ⟨hF, hP, hB⟩ := wr_facts inv
  -- The new frame is disjoint from every writable region.
  have hdis : ∀ r ∈ s₁.wr, Region.Disjoint ⟨s₁.gpr .rsp - BitVec.ofNat 64 b, b⟩ r := by
    intro r hr a ha hc
    exact hfree a (by simp only [Region.Contains] at ha; omega_using [ha]) r hr hc
  have hwr₂ : s₂'.wr = s₁'.wr := by rw [c₁.wr, c₂.wr, inv.rsp, inv.wr]
  have hbase : Taint.Agree (shiftIn τ.t b) s₁' s₂' := by
    have wf : ∀ {s s' : State}, AllocFx b s s' → s.gpr .rsp = s₁.gpr .rsp → s.wr = s₁.wr → Wf τ.t s →
        Wf (shiftIn τ.t b) s' := by
      intro s s' c hsp hwr hw
      refine ⟨fun _ => ?_, fun p hp => ?_⟩
      · rw [c.wr, hsp, hwr]
        exact ⟨.cons (Nat.le_refl _) hF, List.pairwise_cons.mpr ⟨hdis, hP⟩, fun r hr => by
          rcases List.mem_cons.mp hr with rfl | hr
          · simp only; omega_using [hb4]
          · exact hB r hr⟩
      · simp only [shiftIn, List.mem_cons, List.mem_map] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩
        · simp only [region_cons_zero c.wr, c.sp, BitVec.add_zero]
        · simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hq
          simp only [region_cons_succ c.wr, c.gpr _ hq.2, hw.2 q hq.1]
          rfl
    refine ⟨⟨fun r hr => ?_, fun hf => ?_⟩, fun _ => hwr₂.symm, wf c₁ rfl rfl inv.base.wf₁,
      wf c₂ inv.rsp.symm inv.wr.symm inv.base.wf₂, ?_, ?_, noLo, fun r hr => by
        rw [c₁.xmm, c₂.xmm]; exact inv.base.xr r hr⟩
    · by_cases h : r = .rsp
      · subst h; rw [c₁.sp, c₂.sp, inv.rsp]
      · rw [c₁.gpr r h, c₂.gpr r h]; exact inv.base.rf.1 r hr
    · obtain ⟨a, b', c, d⟩ := inv.base.rf.2 hf
      rw [c₁.flags.1, c₂.flags.1, c₁.flags.2.1, c₂.flags.2.1, c₁.flags.2.2.1, c₂.flags.2.2.1,
        c₁.flags.2.2.2, c₂.flags.2.2.2]
      exact ⟨a, b', c, d⟩
    · intro sl hsl
      simp only [shiftIn, List.mem_map] at hsl
      obtain ⟨q, hq, rfl⟩ := hsl
      exact inv.base.ok q hq
    · intro sl hsl k hk₁ hk₂
      simp only [shiftIn, List.mem_map] at hsl
      obtain ⟨q, hq, rfl⟩ := hsl
      simp only at hk₁ hk₂ ⊢
      rw [hba, hba₂, c₁.mem, c₂.mem]
      exact inv.base.slots q hq k hk₁ hk₂
  -- The argument area, above the new frame.
  have haa₁ : ∀ τ' : FT, τ'.room = τ.room - b → τ'.depth = τ.depth + b → aa s₁' τ' = aa s₁ τ :=
    fun τ' h1 h2 => aa_shift (by rw [h1]; exact hsh₁) (by rw [h1, h2]; omega_using [hbr])
  have haa₂ : ∀ τ' : FT, τ'.room = τ.room - b → τ'.depth = τ.depth + b → aa s₂' τ' = aa s₂ τ :=
    fun τ' h1 h2 => aa_shift (by rw [h1]; exact hsh₂) (by rw [h1, h2]; omega_using [hbr])
  have hwb : wa s₁ τ (τ.room - b) = s₁.gpr .rsp - BitVec.ofNat 64 b := by
    have := hwab 0
    simp only [Nat.add_zero, BitVec.add_zero] at this
    exact this
  refine ⟨hbase, by rw [c₁.sp, c₂.sp, inv.rsp], by rw [c₁.unk, c₂.unk, inv.unk], hwr₂.symm,
    fun h => by simp [shiftIn] at h, by rw [c₁.wr]; simp only [List.length_cons]; have := inv.nfr; omega_using [this],
    ?_, ?_, ?_, ?_, ?_, inv.rasSorted, ?_, ?_, ?_, ?_, ?_, ?_,
    fun h => by dsimp only at h ⊢; rw [c₁.sp, hrb]; have := inv.aTop h; omega_using [hbr, hroom, this], aFree_of (haa₁ _ rfl rfl) rfl ?_, inv.saFit,
    sa_keep inv (fun _ _ => by rw [c₁.mem]) (fun _ _ => by rw [c₂.mem]) (haa₁ _ rfl rfl) (haa₂ _ rfl rfl) rfl,
    fun e he => by
      simp only [List.mem_map] at he
      obtain ⟨e, he, rfl⟩ := he
      exact inv.spFit e he, ?_⟩
  rotate_right
  · -- The public bytes: those of the new frame that `sec` does not list, and the others'.
    intro i k hk
    dsimp only at hk
    cases i with
    | zero =>
      rw [pbGet_cons_zero, testBit_frameBits, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hk
      refine ⟨by simp only [shiftIn, List.getD_cons_zero]; exact hk.1, ?_⟩
      have hb₁ : byteAddr s₁' 0 k = wa s₁ τ (τ.room - b + k) := by
        rw [hwab]; simp only [byteAddr, hr0]
      have hb₂ : byteAddr s₂' 0 k = wa s₂ τ (τ.room - b + k) := by
        rw [← wa_eq inv.rsp, ← hb₁]; simp only [byteAddr, region, hwr₂]
      rw [hb₁, hb₂, c₁.mem, c₂.mem]
      exact inv.dead _ (by omega_using [hbr, hk.1]) (fun h => by rw [show _ = true from h] at hk; cases hk.2)
        (below_free inv (by omega_using [hbr, hk.1]))
    | succ i =>
      rw [pbGet_cons_succ] at hk
      obtain ⟨h1, h2⟩ := inv.pb i k hk
      refine ⟨by simp only [shiftIn, List.getD_cons_succ]; exact h1, ?_⟩
      rw [hba, hba₂, c₁.mem, c₂.mem]
      exact h2
  · dsimp only; rw [c₁.sp]; omega_using [hroom, hrb]
  · dsimp only; rw [c₁.sp]; omega_using [hbr, hroom, htop, hrb]
  · intro i hi
    dsimp only at hi ⊢
    rw [c₁.sp]
    cases i with
    | zero => rw [hr0]; exact Region.sub_prefix (by omega_using [])
    | succ i => rw [hrs]; exact Region.sub_trans (inv.frames i (by omega_using [hi])) (sub_down _ b τ.depth)
  · intro i h₁ h₂
    dsimp only at h₁
    rw [c₁.wr, List.length_cons] at h₂
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega_using [h₁]⟩
    have := inv.others i (by omega_using [h₁]) (by omega_using [h₂])
    simp only [wb] at this ⊢
    rw [hrs, hsh₁, show τ.room - b + (τ.depth + b) = τ.room + τ.depth by omega_using [hbr]]
    exact this
  · intro j hj
    dsimp only at hj ⊢
    have := inv.rasIn j hj; omega_using [this]
  · intro j hj i hi
    dsimp only at hj hi
    simp only [raSlot, wa, wb]
    rw [hsh₁]
    cases i with
    | zero =>
      rw [hr0]
      have hj' := inv.rasIn j hj
      rw [Offset.sub_ofNat_eq _ hbr]
      exact Offset.disjoint _ (.inl (by omega_using [hbr, hj'])) (by omega_using [hbr, hroom]) (by omega_using [hroom, htop, hj'])
    | succ i => rw [hrs]; exact inv.rasFr j hj i (by omega_using [hi])
  · intro j hj hn hw
    dsimp only at hj hn
    simp only [wa, wb] at hw ⊢
    rw [hsh₁] at hw
    rw [hsh₁, hsh₂, c₁.mem, c₂.mem]
    exact inv.dead j (by omega_using [hbr, hj]) hn (fun r hr => hw r (by rw [c₁.wr]; exact List.mem_cons_of_mem _ hr))
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨e, he, rfl⟩ := he
    simp only [shiftIn, List.getD_cons_succ]
    exact inv.mbFit e he
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), fun e he => ?_, sp_of (haa₁ _ rfl rfl) fun e he => ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₁.gpr _ hp.2]; exact inv.one₁.ub p hp.1
    · simp only [List.mem_map] at he
      obtain ⟨e, he, rfl⟩ := he
      simp only [hba, hrs, c₁.mem]
      exact inv.one₁.mb e he
    · simp only [List.mem_map] at he
      obtain ⟨e, he, rfl⟩ := he
      rw [hrs, c₁.mem]
      exact inv.one₁.sp e he
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), fun e he => ?_, sp_of (haa₂ _ rfl rfl) fun e he => ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₂.gpr _ hp.2]; exact inv.one₂.ub p hp.1
    · simp only [List.mem_map] at he
      obtain ⟨e, he, rfl⟩ := he
      simp only [hba₂, hrs₂, c₂.mem]
      exact inv.one₂.mb e he
    · simp only [List.mem_map] at he
      obtain ⟨e, he, rfl⟩ := he
      rw [hrs₂, c₂.mem]
      exact inv.one₂.sp e he
  · intro i hi
    simp only [wa, wb]
    rw [hsh₁]
    cases i with
    | zero =>
      have := hwab 0
      simp only [wa, wb, Nat.add_zero, BitVec.add_zero] at this
      rw [hr0, List.getElem_cons_zero]
      exact this.symm
    | succ i => rw [hrs, List.getElem_cons_succ]; exact inv.fw i (Nat.lt_of_succ_lt_succ hi)
  · intro k hk r hr
    rw [c₁.wr] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · have := aa_sep inv.room (inv.aTop (by omega_using [hk])) hk (i := τ.room - b) (n := b) (by omega_using [hbr])
      rw [hwb] at this
      simp only [Region.Contains]
      omega_using [this]
    · exact inv.aFree k hk r hr

/-- What the free of a frame of `b` bytes does to the state: the frame's
bytes are `lose`'s, as the unknowns say. -/
structure FreeFx (b : Nat) (s s' : State) : Prop where
  head : s.wr = ⟨s.gpr .rsp, b⟩ :: s'.wr
  sp : s'.gpr .rsp = s.gpr .rsp + BitVec.ofNat 64 b
  gpr : ∀ r, r ≠ .rsp → s'.gpr r = s.gpr r
  flags : s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of
  xmm : s'.xmm = s.xmm
  unk : s'.unknowns = fun n => s.unknowns (n + b / 4)
  mem : s'.mem = lose s.mem (s.gpr .rsp) b s.unknowns

theorem freeFx {b : Nat} {a s s' : State} (h : isa.pop (.free b) a s = some s') : FreeFx b s s' := by
  simp only [isa, pop] at h
  split at h <;> [rename_i hc; cases h]
  cases h
  obtain ⟨-, -, -, hsp, hwr, hhd⟩ := hc
  refine ⟨?_, by simp only [State.setReg, ↓reduceIte], fun _ h => setReg_ne h, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  rw [hwr]
  cases hw : a.wr with
  | nil => rw [hw] at hhd; cases hhd
  | cons r l => rw [hw] at hhd; cases hhd; rw [hsp]; rfl

theorem region_tail {s s' : State} {r : Region} (h : s.wr = r :: s'.wr) (i : Nat) :
    region s' i = region s (i + 1) := by
  simp only [region, h, List.getD_cons_succ]

theorem pop_sound {τ τ' : FT} {j : Instr} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : popF τ j = some τ') (e₁ : isa.pop j a₁ b₁ = some c₁) (e₂ : isa.pop j a₂ b₂ = some c₂) :
    isa.addrs j b₁ = isa.addrs j b₂ ∧ Agree τ' c₁ c₂ := by
  cases j <;> simp only [popF, reduceCtorEq] at hs
  rename_i b
  split at hs <;> [rename_i hc; cases hs]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨hok, hn1⟩, hhd⟩, hbd⟩, hras⟩ := hc
  cases hs
  have inv := ha hok
  have c₁' := freeFx e₁
  have c₂' := freeFx e₂
  refine ⟨rfl, fun _ => ?_⟩
  have hroom := inv.room
  have htop := inv.top
  have hne : τ.t.lens ≠ [] := by intro h; rw [h] at hhd; cases hhd
  obtain ⟨hF, hP, hB⟩ := inv.base.wf₁.1 hne
  obtain ⟨lt, hlt⟩ : ∃ lt, τ.t.lens = b :: lt := by
    cases h : τ.t.lens with
    | nil => exact absurd h hne
    | cons x lt => rw [h] at hhd; cases hhd; exact ⟨lt, rfl⟩
  have hw1 := c₁'.head
  have hsh₁ : c₁.gpr .rsp - BitVec.ofNat 64 (τ.room + b) = b₁.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₁'.sp]; exact addr_add_sub _ _ _
  have hsh₂ : c₂.gpr .rsp - BitVec.ofNat 64 (τ.room + b) = b₂.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₂'.sp]; exact addr_add_sub _ _ _
  have hwr₂ : c₂.wr = c₁.wr := by
    have h := c₂'.head
    rw [← inv.wr, hw1, ← inv.rsp] at h
    exact (List.cons.inj h).2.symm
  have hrb : (b₁.gpr .rsp + BitVec.ofNat 64 b).toNat = (b₁.gpr .rsp).toNat + b := toNat_add_ofNat _ (by omega_using [hbd, htop])
  have hrt : ∀ i, region c₁ i = region b₁ (i + 1) := region_tail hw1
  have hrt₂ : ∀ i, region c₂ i = region b₂ (i + 1) := region_tail c₂'.head
  have hba : ∀ i k, byteAddr c₁ i k = byteAddr b₁ (i + 1) k := fun i k => by simp only [byteAddr, hrt]
  have hba₂ : ∀ i k, byteAddr c₂ i k = byteAddr b₂ (i + 1) k := fun i k => by simp only [byteAddr, hrt₂]
  have hr0 : region b₁ 0 = ⟨b₁.gpr .rsp, b⟩ := region_cons_zero hw1
  have hlen : b₁.wr.length = c₁.wr.length + 1 := by rw [hw1, List.length_cons]
  -- The regions after the frame are disjoint from it.
  have hdis : ∀ i, Region.Disjoint (region b₁ (i + 1)) ⟨b₁.gpr .rsp, b⟩ := by
    intro i
    rw [hw1] at hP
    by_cases hi : i < c₁.wr.length
    · rw [region_cons_succ hw1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact Region.Disjoint.symm ((List.pairwise_cons.mp hP).1 _ (List.getElem_mem _))
    · intro x hx
      rw [region_cons_succ hw1, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega_using [hi]),
        Option.getD_none] at hx
      simp only [Region.Contains] at hx; omega
  -- Outside the frame, each run's memory is as it was; in it, the two runs'
  -- bytes are lost alike (the same address and unknowns), so bytes that
  -- agreed still agree.
  have hout₁ : ∀ y, ¬ (⟨b₁.gpr .rsp, b⟩ : Region).Contains y 1 → c₁.mem y = b₁.mem y := by
    intro y hy
    rw [c₁'.mem]
    exact lose_out (by simp only [Region.Contains] at hy; omega)
  have hout₂ : ∀ y, ¬ (⟨b₁.gpr .rsp, b⟩ : Region).Contains y 1 → c₂.mem y = b₂.mem y := by
    intro y hy
    rw [c₂'.mem, ← inv.rsp]
    exact lose_out (by simp only [Region.Contains] at hy; omega)
  have hrelA : ∀ y y', y = y' → b₁.mem y = b₂.mem y' → c₁.mem y = c₂.mem y' := by
    intro y y' e h
    subst e
    rw [c₁'.mem, c₂'.mem, ← inv.rsp, ← inv.unk]
    exact lose_congr _ _ _ h
  have hfr : (⟨b₁.gpr .rsp, b⟩ : Region) ∈ b₁.wr := by rw [hw1]; exact List.mem_cons_self ..
  have hmA₁ : ∀ k < τ.an, c₁.mem (aa b₁ τ k) = b₁.mem (aa b₁ τ k) :=
    fun k hk => hout₁ _ (inv.aFree k hk _ hfr)
  have hmA₂ : ∀ k < τ.an, c₂.mem (aa b₁ τ k) = b₂.mem (aa b₁ τ k) :=
    fun k hk => hout₂ _ (inv.aFree k hk _ hfr)
  have hsp₁ : ∀ e ∈ τ.sp, c₁.mem.readW (aa b₁ τ e.1) 64 = b₁.mem.readW (aa b₁ τ e.1) 64 := by
    intro e he
    apply Mem.readW_congr
    intro j hj
    simp only [Nat.reduceDiv] at hj
    rw [aa_add]
    exact hmA₁ _ (by have := inv.spFit e he; omega_using [hj, this])
  have hsp₂ : ∀ e ∈ τ.sp, c₂.mem.readW (aa b₂ τ e.1) 64 = b₂.mem.readW (aa b₂ τ e.1) 64 := by
    intro e he
    rw [← aa_eq inv.rsp]
    apply Mem.readW_congr
    intro j hj
    simp only [Nat.reduceDiv] at hj
    rw [aa_add]
    exact hmA₂ _ (by have := inv.spFit e he; omega_using [hj, this])
  have hmb₁ : ∀ e ∈ τ.mb, e.1 ≠ 0 →
      c₁.mem.readW (byteAddr b₁ e.1 e.2.1) 64 = b₁.mem.readW (byteAddr b₁ e.1 e.2.1) 64 := by
    intro e he h0
    apply Mem.readW_congr
    intro j hj
    simp only [Nat.reduceDiv] at hj
    rw [byteAddr_add]
    have := inv.mbFit e he
    obtain ⟨-, h2⟩ := byte_in inv.base.wf₁ (i := e.1) (k := e.2.1 + j) (by omega_using [hj, this])
    obtain ⟨i, hi⟩ : ∃ i, e.1 = i + 1 := ⟨e.1 - 1, by omega_using [h0]⟩
    rw [hi] at h2 ⊢
    exact hout₁ _ fun hc => hdis i _ h2 hc
  have hmb₂ : ∀ e ∈ τ.mb, e.1 ≠ 0 →
      c₂.mem.readW (byteAddr b₂ e.1 e.2.1) 64 = b₂.mem.readW (byteAddr b₂ e.1 e.2.1) 64 := by
    intro e he h0
    rw [← byteAddr_wr inv.wr]
    apply Mem.readW_congr
    intro j hj
    simp only [Nat.reduceDiv] at hj
    rw [byteAddr_add]
    have := inv.mbFit e he
    obtain ⟨-, h2⟩ := byte_in inv.base.wf₁ (i := e.1) (k := e.2.1 + j) (by omega_using [hj, this])
    obtain ⟨i, hi⟩ : ∃ i, e.1 = i + 1 := ⟨e.1 - 1, by omega_using [h0]⟩
    rw [hi] at h2 ⊢
    exact hout₂ _ fun hc => hdis i _ h2 hc
  have hbase : Taint.Agree (shiftOut τ.t) c₁ c₂ := by
    have wf : ∀ {s s' : State}, FreeFx b s s' → Wf τ.t s → Wf (shiftOut τ.t) s' := by
      intro s s' c hw
      refine ⟨fun _ => ?_, fun p hp => ?_⟩
      · obtain ⟨hF, hP, hB⟩ := hw.1 hne
        rw [c.head, hlt] at hF
        rw [c.head] at hP hB
        simp only [shiftOut, hlt, List.tail_cons]
        exact ⟨(List.forall₂_cons.mp hF).2, (List.pairwise_cons.mp hP).2,
          fun r hr => hB r (List.mem_cons_of_mem _ hr)⟩
      · simp only [shiftOut, List.mem_filterMap, kill, List.mem_filter, bne_iff_ne, ne_eq] at hp
        obtain ⟨q, ⟨hq, hqr⟩, hq'⟩ := hp
        split at hq' <;> [cases hq'; rename_i hq0]
        cases hq'
        simp only
        rw [c.gpr _ hqr, hw.2 q hq, region_tail c.head, Nat.sub_add_cancel (by omega_using [hq0])]
    refine ⟨⟨fun r hr => ?_, fun hf => ?_⟩, fun _ => hwr₂.symm, wf c₁' inv.base.wf₁, wf c₂' inv.base.wf₂,
      ?_, ?_, noLo, fun r hr => by rw [c₁'.xmm, c₂'.xmm]; exact inv.base.xr r hr⟩
    · by_cases h : r = .rsp
      · subst h; rw [c₁'.sp, c₂'.sp, inv.rsp]
      · rw [c₁'.gpr r h, c₂'.gpr r h]; exact inv.base.rf.1 r hr
    · obtain ⟨a, b', c, d⟩ := inv.base.rf.2 hf
      rw [c₁'.flags.1, c₂'.flags.1, c₁'.flags.2.1, c₂'.flags.2.1, c₁'.flags.2.2.1, c₂'.flags.2.2.1,
        c₁'.flags.2.2.2, c₂'.flags.2.2.2]
      exact ⟨a, b', c, d⟩
    · intro sl hsl
      simp only [shiftOut, List.mem_filterMap] at hsl
      obtain ⟨q, hq, hq'⟩ := hsl
      split at hq' <;> [cases hq'; rename_i hq0]
      cases hq'
      have := inv.base.ok q hq
      simp only [shiftOut, hlt, List.tail_cons]
      rw [hlt] at this
      obtain ⟨k, hk⟩ : ∃ k, q.1 = k + 1 := ⟨q.1 - 1, by omega_using [hq0]⟩
      rw [hk, List.getD_cons_succ] at this
      simp only [hk, Nat.add_sub_cancel]
      exact this
    · intro sl hsl k hk₁ hk₂
      simp only [shiftOut, List.mem_filterMap] at hsl
      obtain ⟨q, hq, hq'⟩ := hsl
      split at hq' <;> [cases hq'; rename_i hq0]
      cases hq'
      simp only at hk₁ hk₂ ⊢
      rw [hba, hba₂, Nat.sub_add_cancel (by omega_using [hq0])]
      exact hrelA _ _ (byteAddr_wr inv.wr _ _) (inv.base.slots q hq k hk₁ hk₂)
  -- The argument area, above the frame freed.
  have haa₁ : ∀ τ' : FT, τ'.room = τ.room + b → τ'.depth = τ.depth - b → aa c₁ τ' = aa b₁ τ :=
    fun τ' h1 h2 => aa_shift (by rw [h1]; exact hsh₁) (by rw [h1, h2]; omega_using [hbd])
  have haa₂ : ∀ τ' : FT, τ'.room = τ.room + b → τ'.depth = τ.depth - b → aa c₂ τ' = aa b₂ τ :=
    fun τ' h1 h2 => aa_shift (by rw [h1]; exact hsh₂) (by rw [h1, h2]; omega_using [hbd])
  have hsp' : ∀ {e : Nat × Nat × Nat},
      e ∈ τ.sp.filterMap (fun e => if e.2.1 = 0 then none else some (e.1, e.2.1 - 1, e.2.2)) →
      ∃ q ∈ τ.sp, q.2.1 ≠ 0 ∧ e = (q.1, q.2.1 - 1, q.2.2) := by
    intro e he
    simp only [List.mem_filterMap] at he
    obtain ⟨q, hq, hq'⟩ := he
    split at hq' <;> [cases hq'; rename_i hq0]
    cases hq'
    exact ⟨q, hq, hq0, rfl⟩
  refine ⟨hbase, by rw [c₁'.sp, c₂'.sp, inv.rsp], by rw [c₁'.unk, c₂'.unk, inv.unk], hwr₂.symm,
    ?_, by dsimp only; have := inv.nfr; omega_using [hlen, this], ?_, ?_, ?_, ?_, ?_, inv.rasSorted, ?_, ?_, ?_, ?_, ?_, ?_,
    fun h => by dsimp only at h ⊢; rw [c₁'.sp, hrb]; have := inv.aTop h; omega_using [hbd, this],
    aFree_of (haa₁ _ rfl rfl) rfl fun k hk r hr => inv.aFree k hk r (by rw [hw1]; exact List.mem_cons_of_mem _ hr),
    inv.saFit,
    sa_keep inv hmA₁ hmA₂ (haa₁ _ rfl rfl) (haa₂ _ rfl rfl) rfl,
    fun e he => by
      obtain ⟨q, hq, -, rfl⟩ := hsp' he
      exact inv.spFit q hq, ?_⟩
  rotate_right
  · intro i k hk
    dsimp only at hk
    rw [pbGet_tail] at hk
    obtain ⟨h1, h2⟩ := inv.pb (i + 1) k hk
    refine ⟨?_, ?_⟩
    · simp only [shiftOut, hlt, List.tail_cons]
      rw [hlt, List.getD_cons_succ] at h1
      exact h1
    · rw [hba, hba₂]
      exact hrelA _ _ (byteAddr_wr inv.wr _ _) h2
  · intro h
    have hF' := hF
    rw [hw1, hlt] at hF'
    have := forall₂_length (List.forall₂_cons.mp hF').2
    simp only [shiftOut, hlt, List.tail_cons] at h
    rw [h, List.length_nil] at this
    exact List.eq_nil_of_length_eq_zero this
  · dsimp only; rw [c₁'.sp]; omega_using [hroom, hrb]
  · dsimp only; rw [c₁'.sp]; omega_using [htop, hrb]
  · intro i hi
    dsimp only at hi ⊢
    rw [hrt, c₁'.sp]
    exact sub_shrink (inv.frames (i + 1) (by omega_using [hi])) (hdis i) hbd (by omega_using [htop])
  · intro i h₁ h₂
    dsimp only at h₁
    have := inv.others (i + 1) (by omega_using [h₁]) (by omega_using [hlen, h₂])
    simp only [wb] at this ⊢
    rw [hrt, hsh₁, show τ.room + b + (τ.depth - b) = τ.room + τ.depth by omega_using [hbd]]
    exact this
  · intro j hj
    dsimp only at hj ⊢
    have := inv.rasIn j hj
    have := hras j hj
    omega_arith
  · intro j hj i hi
    dsimp only at hj hi
    simp only [raSlot, wa, wb]
    rw [hsh₁, hrt]
    exact inv.rasFr j hj (i + 1) (by omega_using [hi])
  · intro j hj hn hw
    dsimp only at hj hn
    simp only [wa, wb] at hw ⊢
    rw [hsh₁] at hw
    rw [hsh₁, hsh₂]
    refine hrelA (wa b₁ τ j) (wa b₂ τ j) (wa_eq inv.rsp j) ?_
    show b₁.mem (wa b₁ τ j) = b₂.mem (wa b₂ τ j)
    change ∀ r ∈ c₁.wr, ¬ r.Contains (wa b₁ τ j) 1 at hw
    by_cases hin : (⟨b₁.gpr .rsp, b⟩ : Region).Contains (wa b₁ τ j) 1
    · -- A byte of the frame freed: public unless `sec` now lists it.
      have hrw : b₁.gpr .rsp = wb b₁ τ + BitVec.ofNat 64 τ.room := by simp only [wb, BitVec.sub_add_cancel]
      have hj' : τ.room ≤ j ∧ j < τ.room + b := by
        simp only [Region.Contains, hrw] at hin
        have h := (Offset.lt_iff (wa b₁ τ j) (wb b₁ τ) (d := τ.room) (n := b) (by omega_using [hroom, hrb])).mp (by omega_using [hin])
        simp only [wa, Mem.sub_ofNat_toNat _ (show j < 2 ^ 64 by omega_using [hbd, hroom, htop, hj])] at h
        exact h
      have hbit : (pbGet τ.pb 0).testBit (j - τ.room) = true := by
        have hn' : (secFree τ.sec (pbGet τ.pb 0) τ.room b).testBit j = false := Bool.eq_false_iff.mpr hn
        rw [testBit_secFree, Bool.or_eq_false_iff] at hn'
        have h2 := hn'.2
        simp only [show decide (τ.room ≤ j) = true from decide_eq_true hj'.1,
          show decide (j - τ.room < b) = true from decide_eq_true (by omega_using [hj']), Bool.true_and,
          Bool.not_eq_false'] at h2
        exact h2
      obtain ⟨-, hag⟩ := inv.pb 0 (j - τ.room) hbit
      have e₁ : byteAddr b₁ 0 (j - τ.room) = wa b₁ τ j := by
        rw [byteAddr, hr0]
        dsimp only
        rw [hrw, wa, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hj'.1]
      have e₂ : byteAddr b₂ 0 (j - τ.room) = wa b₂ τ j := by
        rw [byteAddr_wr inv.wr.symm, e₁, wa_eq inv.rsp]
      rw [← e₁, ← e₂]
      exact hag
    · have hw' : ∀ r ∈ b₁.wr, ¬ r.Contains (wa b₁ τ j) 1 := by
        rw [hw1]
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hin
        · exact hw r hr
      exact inv.dead j (by omega_using [hbd, hj]) (inSec_lor_left hn) hw'
  · intro e he
    simp only [List.mem_filterMap] at he
    obtain ⟨q, hq, hq'⟩ := he
    split at hq' <;> [cases hq'; rename_i hq0]
    cases hq'
    have := inv.mbFit q hq
    simp only [shiftOut, hlt, List.tail_cons]
    rw [hlt] at this
    obtain ⟨k, hk⟩ : ∃ k, q.1 = k + 1 := ⟨q.1 - 1, by omega_using [hq0]⟩
    rw [hk, List.getD_cons_succ] at this
    simp only [hk, Nat.add_sub_cancel]
    exact this
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), fun e he => ?_, sp_of (haa₁ _ rfl rfl) fun e he => ?_⟩
    rotate_left 2
    · obtain ⟨q, hq, hq0, rfl⟩ := hsp' he
      rw [hrt, hsp₁ q hq, Nat.sub_add_cancel (by omega_using [hq0])]
      exact inv.one₁.sp q hq
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₁'.gpr _ hp.2]; exact inv.one₁.ub p hp.1
    · simp only [List.mem_filterMap] at he
      obtain ⟨q, hq, hq'⟩ := he
      split at hq' <;> [cases hq'; rename_i hq0]
      cases hq'
      simp only
      rw [hba, hrt, Nat.sub_add_cancel (by omega_using [hq0]), hmb₁ q hq (fun h => hq0 (Or.inl h)),
        Nat.sub_add_cancel (by omega_using [hq0])]
      exact inv.one₁.mb q hq
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), fun e he => ?_, sp_of (haa₂ _ rfl rfl) fun e he => ?_⟩
    rotate_left 2
    · obtain ⟨q, hq, hq0, rfl⟩ := hsp' he
      rw [hrt₂, hsp₂ q hq, Nat.sub_add_cancel (by omega_using [hq0])]
      exact inv.one₂.sp q hq
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₂'.gpr _ hp.2]; exact inv.one₂.ub p hp.1
    · simp only [List.mem_filterMap] at he
      obtain ⟨q, hq, hq'⟩ := he
      split at hq' <;> [cases hq'; rename_i hq0]
      cases hq'
      simp only
      rw [hba₂, hrt₂, Nat.sub_add_cancel (by omega_using [hq0]), hmb₂ q hq (fun h => hq0 (Or.inl h)),
        Nat.sub_add_cancel (by omega_using [hq0])]
      exact inv.one₂.mb q hq
  · intro i hi
    simp only [hrt, wa, wb]
    rw [hsh₁, List.getElem_tail]
    exact inv.fw (i + 1) (by simp only [List.length_tail] at hi; omega_using [hi])

/-! ## The functions the kernel evaluates are the analysis's -/

theorem natsEq_eq (a b : List Nat) : natsEq a b = (a == b) := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x a ih =>
    cases b with
    | nil => rfl
    | cons y b =>
      show (Nat.beq x y && natsEq a b) = _
      rw [ih, KList.beq_eq]; simp [List.cons_beq_cons]

/-- What `step` adds to the base step is nothing for an instruction `isPlain` says is. -/
theorem plain_facts {i : Instr} (h : isPlain i = true) (τ : FT) :
    special τ i = none ∧ (∀ t, pbPost τ i (argPost τ i (post τ i t)) = t) ∧ ubNew τ i = none ∧ flOf i = none ∧
    mbAfter τ i = τ.mb ∧ (∀ r, Taint.clobbers i r = (Taint.dstOf i == some r)) ∧ writesMem i = false := by
  cases i
  case alu op d src | alu32 op d src =>
    cases op <;> cases src <;>
      simp_all [isPlain, flOf, special, post, argPost, pbPost, ubNew, mbAfter, storeW, writesMem, Taint.clobbers]
  case mov d src | mov32 d src =>
    cases src <;>
      simp_all [isPlain, flOf, special, post, argPost, pbPost, ubNew, mbAfter, storeW, writesMem, Taint.clobbers]
  case xop op =>
    cases op
    case bin op x x' =>
      cases op <;>
        simp_all [isPlain, flOf, special, post, argPost, pbPost, ubNew, mbAfter, storeW, writesMem, Taint.clobbers]
    all_goals
      simp_all [isPlain, flOf, special, post, argPost, pbPost, ubNew, mbAfter, storeW, writesMem, Taint.clobbers]
  case vmovdquStore l _ _ => cases l <;> simp_all [isPlain]
  all_goals
    simp_all [isPlain, flOf, special, post, argPost, pbPost, ubNew, mbAfter, storeW, writesMem, Taint.clobbers]

/-- An instruction that writes no memory leaves the public bytes of the regions. -/
theorem pbAfter_of_not_writes {i : Instr} (h : writesMem i = false) (τ : FT) : pbAfter τ i = τ.pb := by
  unfold pbAfter
  cases hs : storeW i with
  | none => simp only [h, Bool.false_eq_true, ↓reduceIte]
  | some q => simp only [writesMem, hs, Option.isSome_some, Bool.true_or, reduceCtorEq] at h

theorem ubDrop_eq {i : Instr} (hc : ∀ r, Taint.clobbers i r = (Taint.dstOf i == some r)) (ub : List (Reg × Nat)) :
    ubDrop (Taint.dstOf i) ub = ubKill ub i := by
  simp only [ubKill, hc]
  cases ub with
  | nil => cases Taint.dstOf i <;> rfl
  | cons p ub =>
    cases hd : Taint.dstOf i with
    | none => exact (List.filter_eq_self.mpr fun _ _ => rfl).symm
    | some d =>
      simp only [ubDrop, KList.filter_eq, regEq_eq]
      congr 1; funext q; rw [Bool.eq_iff_iff]
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
      exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩

theorem forceList_eq {α β : Type} (l : List β) (k : List β → α) : forceList l k = k l := by
  cases l <;> rfl

theorem forceOpt_eq {α β : Type} (o : Option β) (k : Option β → α) : forceOpt o k = k o := by
  cases o <;> rfl

theorem forceTAll_eq {α : Type} (t : Taint.T) (k : Taint.T → α) : forceTAll t k = k t := by
  obtain ⟨rg, f, l, b, sl, lo, x⟩ := t
  simp only [forceTAll, forceList_eq, RegSet.force_eq, Taint.forceT_eq]

/-- `step` changes only the base taint, the bounds, the flags, the pointers in
slots and the public bytes of the regions. -/
theorem step_same {τ τ' : FT} {i : Instr} (h : step τ i = some τ') :
    τ' = ⟨true, τ'.t, τ.nfr, τ.depth, τ.room, τ.sec, τ.ras, τ'.ub, τ'.fl, τ'.mb, τ.fw, τ.an, τ.sa, τ.sp, τ'.pb⟩ := by
  obtain ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ := τ
  unfold step at h
  cases ok
  · cases h
  · split at h <;> [skip; cases h]
    split at h <;> [skip; cases h]
    cases h
    rfl

theorem keepNats_eq (a b : List Nat) : keepNats a b = b := by
  unfold keepNats
  cases h : natsEq b a
  · rfl
  · rw [natsEq_eq] at h
    exact (eq_of_beq h).symm

theorem slowFn_run (i : Instr) (τ : FT) : (slowFn i).run τ = step τ i := by
  obtain ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ := τ
  simp only [slowFn]
  cases h : step ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ i with
  | none => rfl
  | some τ' =>
    simp only [forceTAll_eq, forceList_eq, forceOpt_eq, keepNats_eq]
    exact congrArg some (step_same h).symm

theorem slowFn_eq (i : Instr) : slowFn i = ⟨(step · i)⟩ :=
  congrArg RStep.mk (funext (slowFn_run i))

theorem runF_eq (b : Taint.Step) (t : Taint.T) : runF b t = b.run t := by
  unfold runF
  cases b.run t with
  | none => rfl
  | some t' => exact Taint.forceT_eq t' some

theorem fastFn_eq {i : Instr} (h : isPlain i = true) (hsp : isa.writesSp i = false) (τ : FT) :
    (fastFn (Taint.stepKDFn i) (Taint.dstOf i)).run τ = step τ i := by
  obtain ⟨hs, hp, hu, hf, hm, hc, hwm⟩ := plain_facts h τ
  have hb : baseStep τ i = (Taint.stepKDFn i).run τ.t := by
    rw [baseStep, hs, show (fun t => pbPost τ i (argPost τ i (post τ i t))) = id from funext hp, Option.map_id]
    exact taint_step _ _
  unfold step
  rw [hb, hu, hf, hm, hsp, pbAfter_of_not_writes hwm, hwm]
  obtain ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ := τ
  cases ok
  · rfl
  · simp only [fastFn, runF_eq, Bool.cond_true, Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
    cases (Taint.stepKDFn i).run t with
    | none => rfl
    | some t' => simp only [Option.toList, List.nil_append, ubDrop_eq hc, forceList_eq]

theorem pbMod_self (f : Nat → Nat) : ∀ (l : List Nat) (i : Nat), f (pbGet l i) = pbGet l i → pbMod f l i = l
  | [], _, _ => rfl
  | _ :: l, 0, h => congrArg (· :: l) h
  | a :: l, i + 1, h => congrArg (a :: ·) (pbMod_self f l i h)

theorem pbModKeep_eq (f : Nat → Nat) (l : List Nat) (i : Nat) : pbModKeep f l i = pbMod f l i := by
  unfold pbModKeep
  cases h : Nat.beq (f (pbGet l i)) (pbGet l i)
  · rfl
  · exact (pbMod_self f l i (Nat.eq_of_beq_eq_true h)).symm

/-- `pbAfter` of a store of a register without an index register. -/
theorem pbStore_eq {i : Instr} {m : MemOp} {w : Nat} {p : Taint.T → Bool} (hsw : storeW i = some (m, w))
    (hx : m.index = none) (hst : ∀ τ, stPub τ i = p τ.t) (τ : FT) :
    pbAfter τ i = pbStore τ.t τ.pb m w (p τ.t) := by
  unfold pbAfter pbStore
  simp only [hsw, hst, addrOfK_eq, storeRange, idxRange, hx, pbModKeep_eq, keepNats_eq]
  cases p τ.t
  · cases addrOf τ.t m with
    | none => rfl
    | some q =>
      obtain ⟨ri, d⟩ := q
      by_cases hfit : d + w ≤ τ.t.lens.getD ri 0
      · simp only [Bool.false_eq_true, ↓reduceIte, hfit, Nat.add_sub_cancel_left, KList.ble_eq, decide_true,
          Bool.cond_true, Bool.cond_false]
      · simp only [Bool.false_eq_true, ↓reduceIte, hfit, KList.ble_eq, decide_false, Bool.cond_false]
  · cases addrOf τ.t m with
    | none => rfl
    | some q =>
      obtain ⟨ri, d⟩ := q
      by_cases hfit : d + w ≤ τ.t.lens.getD ri 0
      · simp only [↓reduceIte, hfit, KList.ble_eq, decide_true, Bool.cond_true]
      · simp only [↓reduceIte, hfit, KList.ble_eq, decide_false, Bool.cond_false, Bool.cond_true]

/-- `mbAfter` of a store of `w` bytes at `m`, from the register `src` if a
64-bit store, as `mbAfter` computes it. -/
def mbStoreM (τ : FT) (m : MemOp) (w : Nat) (src : Option Reg) : List (Nat × Nat × Nat × Nat) :=
  match storeRange τ m w with
  | some (ri, lo, hi) =>
    match src with
    | some r =>
      match τ.t.bases.find? (·.1 == r), addrOf τ.t m with
      | some (_, pj, pk), some _ => (ri, lo, pj, pk) :: mbKill τ.mb ri lo hi
      | _, _ => mbKill τ.mb ri lo hi
    | none => mbKill τ.mb ri lo hi
  | none => []

theorem mbKill_eq (mb : List (Nat × Nat × Nat × Nat)) (ri d w : Nat) :
    KList.filter (fun e => !Nat.beq e.1 ri || Nat.ble (e.2.1 + 8) d || Nat.ble (d + w) e.2.1) mb =
      mbKill mb ri d (d + w) := by
  simp only [mbKill, KList.filter_eq, KList.beq_eq, KList.ble_eq, bne]

/-- `mbStore` is `mbAfter`'s, for a store without an index register. -/
theorem mbStore_eq {m : MemOp} (hx : m.index = none) (w : Nat) (src : Option Reg) (τ : FT) :
    mbStoreM τ m w src = mbStore τ.t τ.mb m w src := by
  obtain ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ := τ
  have hf : ∀ r, KList.find? (fun p => regEq p.1 r) t.bases = t.bases.find? (·.1 == r) := fun r => by
    simp only [KList.find?_eq, regEq_eq]
  unfold mbStoreM mbStore
  simp only [storeRange, idxRange, hx, addrOfK_eq, mbKill_eq, hf]
  cases addrOf t m with
  | none => cases mb <;> cases src <;> (try rfl) <;> (dsimp only; split <;> rfl)
  | some q =>
    obtain ⟨ri, d⟩ := q
    by_cases hfit : d + w ≤ t.lens.getD ri 0
    · simp only [hfit, ↓reduceIte, KList.ble_eq, decide_true, Bool.cond_true]
      cases src with
      | none => cases mb <;> rfl
      | some r =>
        cases mb <;> dsimp only <;> cases t.bases.find? (·.1 == r) with
        | none => rfl
        | some q => obtain ⟨b, pj, pk⟩ := q; rfl
    · simp only [hfit, ↓reduceIte, KList.ble_eq, decide_false, Bool.cond_false]
      cases mb <;> cases src <;> (try rfl) <;> (dsimp only; split <;> rfl)

theorem storeStepKD_noSlots (t : Taint.T) (m : MemOp) (w : Nat) (p : Bool) :
    (Taint.storeStepKD t m w p).map (fun t' => ({ t' with slots := [] } : Taint.T)) =
      if memPub t m = true then some { t with slots := [] } else none := by
  obtain ⟨rg, f, l, b, sl, lo, x⟩ := t
  simp only [Taint.storeStepKD]
  cases memPub ⟨rg, f, l, b, sl, lo, x⟩ m <;> rfl

theorem storeStep_noSlots (t : Taint.T) (m : MemOp) (w : Nat) (p : Bool) :
    (storeStep t m w p).map (fun t' => ({ t' with slots := [] } : Taint.T)) =
      if memPub t m = true then some { t with slots := [] } else none := by
  simp only [storeStep]
  split <;> rfl

/-- The base step of a store that `special` leaves to the base analysis. -/
theorem baseStep_store {τ : FT} {i : Instr} {m : MemOp} {w : Nat} {p : Bool} (hs : special τ i = none)
    (hp : ∀ t, pbPost τ i (argPost τ i (post τ i t)) = t)
    (hb : (Taint.stepKDFn i).run τ.t = Taint.storeStepKD τ.t m w p) :
    (baseStep τ i).map (fun t' => ({ t' with slots := [] } : Taint.T)) =
      if memPub τ.t m = true then some { τ.t with slots := [] } else none := by
  rw [baseStep, hs, show (fun t => pbPost τ i (argPost τ i (post τ i t))) = id from funext hp, Option.map_id,
    ← storeStepKD_noSlots τ.t m w p, ← hb]
  exact congrArg (Option.map _) (taint_step _ _)

theorem fastStore_eq {i : Instr} {m : MemOp} {w : Nat} {p : Taint.T → Bool} {src : Option Reg}
    (hsp : isa.writesSp i = false)
    (hbase : ∀ τ, (baseStep τ i).map (fun t' => ({ t' with slots := [] } : Taint.T)) =
      if memPub τ.t m = true then some { τ.t with slots := [] } else none)
    (hu : ∀ τ, ubNew τ i = none) (hf : flOf i = none) (hc : ∀ r, Taint.clobbers i r = false)
    (hm : ∀ τ, mbAfter τ i = mbStore τ.t τ.mb m w src) (hwm : writesMem i = true)
    (hpb : ∀ τ, pbAfter τ i = pbStore τ.t τ.pb m w (p τ.t)) (τ : FT) :
    (fastStore m w p src).run τ = step τ i := by
  have hk : ubKill τ.ub i = τ.ub := by
    simp only [ubKill, hc, Bool.not_false]; exact List.filter_eq_self.mpr fun _ _ => rfl
  have hb := hbase τ
  unfold step
  rw [hu, hf, hm, hsp, hk, hpb, hwm]
  obtain ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ := τ
  cases ok
  · rfl
  · obtain ⟨rg, f, l, b, sl, lo, x⟩ := t
    simp only [fastStore, Bool.cond_true, Bool.not_false, Bool.and_self, ↓reduceIte, forceList_eq]
    simp only at hb
    cases hbs : baseStep ⟨true, ⟨rg, f, l, b, sl, lo, x⟩, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ i with
    | none =>
      rw [hbs] at hb
      cases hmp : memPub ⟨rg, f, l, b, sl, lo, x⟩ m
      · rfl
      · rw [hmp] at hb; cases hb
    | some t' =>
      rw [hbs] at hb
      cases hmp : memPub ⟨rg, f, l, b, sl, lo, x⟩ m
      · rw [hmp] at hb; cases hb
      · rw [hmp] at hb
        simp only [Option.map_some, ↓reduceIte, Option.some.injEq] at hb
        simp only [Bool.cond_true, Option.toList, List.nil_append, hb]

theorem mbStoreI_eq {i : Instr} {m : MemOp} {w : Nat} (hsw : storeW i = some (m, w))
    (hi : ∀ m' r, i ≠ .store m' r) (τ : FT) : mbAfter τ i = mbStoreI τ m w := by
  unfold mbAfter mbStoreI
  simp only [hsw]
  obtain ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ := τ
  cases hr : storeRange ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ m w with
  | none => cases mb <;> rfl
  | some q =>
    obtain ⟨ri, lo, hi'⟩ := q
    cases i <;> first | exact absurd rfl (hi _ _) | (cases mb <;> rfl)

theorem pbStoreI_eq {i : Instr} {m : MemOp} {w : Nat} (hsw : storeW i = some (m, w))
    (hst : ∀ τ, stPub τ i = false) (τ : FT) : pbAfter τ i = pbStoreI τ m w := by
  unfold pbAfter pbStoreI
  simp only [hsw, hst, Bool.false_eq_true, ↓reduceIte, pbModKeep_eq, keepNats_eq]
  rfl

theorem fastStoreI_eq {i : Instr} {m : MemOp} {w : Nat}
    (hsp : isa.writesSp i = false)
    (hbase : ∀ τ, (baseStep τ i).map (fun t' => ({ t' with slots := [] } : Taint.T)) =
      if memPub τ.t m = true then some { τ.t with slots := [] } else none)
    (hu : ∀ τ, ubNew τ i = none) (hf : flOf i = none) (hc : ∀ r, Taint.clobbers i r = false)
    (hm : ∀ τ, mbAfter τ i = mbStoreI τ m w) (hwm : writesMem i = true)
    (hpb : ∀ τ, pbAfter τ i = pbStoreI τ m w) (τ : FT) :
    (fastStoreI m w).run τ = step τ i := by
  have hk : ubKill τ.ub i = τ.ub := by
    simp only [ubKill, hc, Bool.not_false]; exact List.filter_eq_self.mpr fun _ _ => rfl
  have hb := hbase τ
  unfold step
  rw [hu, hf, hm, hsp, hk, hpb, hwm]
  obtain ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ := τ
  cases ok
  · rfl
  · obtain ⟨rg, f, l, b, sl, lo, x⟩ := t
    simp only [fastStoreI, Bool.cond_true, Bool.not_false, Bool.and_self, ↓reduceIte, forceList_eq]
    simp only at hb
    cases hbs : baseStep ⟨true, ⟨rg, f, l, b, sl, lo, x⟩, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ i with
    | none =>
      rw [hbs] at hb
      cases hmp : memPub ⟨rg, f, l, b, sl, lo, x⟩ m
      · rfl
      · rw [hmp] at hb; cases hb
    | some t' =>
      rw [hbs] at hb
      cases hmp : memPub ⟨rg, f, l, b, sl, lo, x⟩ m
      · rw [hmp] at hb; cases hb
      · rw [hmp] at hb
        simp only [Option.map_some, ↓reduceIte, Option.some.injEq] at hb
        simp only [Bool.cond_true, Option.toList, List.nil_append, hb]

theorem insReg_eq (d : Reg) (t : Taint.T) : insReg d t = { t with regs := t.regs.insert d } := by
  cases t; rfl

theorem insX_eq (x : XReg) (t : Taint.T) : insX x t = { t with xregs := t.xregs.insert x } := by
  cases t; rfl

theorem ubOfK_eq : ubOfK = ubOf := by
  funext l r; simp only [ubOfK, ubOf, KList.find?_eq, regEq_eq]

theorem fastG_eq {i : Instr} {pf : Taint.T → Taint.T} {fl' : Option (Reg × Reg)}
    {u : Option (Reg × Reg) → List (Reg × Nat) → List (Reg × Nat)} {τ : FT}
    (hsp : isa.writesSp i = false) (hs : special τ i = none)
    (hp : ∀ t, pbPost τ i (argPost τ i (post τ i t)) = pf t)
    (hf : flOf i = fl') (hm : mbAfter τ i = τ.mb) (hwm : writesMem i = false)
    (hu : (ubNew τ i).toList ++ ubKill τ.ub i = u τ.fl τ.ub) :
    (fastG (Taint.stepKDFn i) pf fl' u).run τ = step τ i := by
  have hb : baseStep τ i = ((Taint.stepKDFn i).run τ.t).map pf := by
    rw [baseStep, hs, show (fun t => pbPost τ i (argPost τ i (post τ i t))) = pf from funext hp]
    exact congrArg (Option.map pf) (taint_step _ _)
  unfold step
  rw [hb, hf, hm, hsp, hu, pbAfter_of_not_writes hwm, hwm]
  obtain ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ := τ
  cases ok
  · rfl
  · simp only [fastG, Bool.cond_true, Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
    cases (Taint.stepKDFn i).run t with
    | none => rfl
    | some t' => simp only [Option.map_some, Taint.forceT_eq, forceList_eq]

theorem fastU_eq {i : Instr} {u : List (Reg × Nat) → List (Reg × Nat)} {τ : FT}
    (hsp : isa.writesSp i = false) (hs : special τ i = none)
    (hp : ∀ t, pbPost τ i (argPost τ i (post τ i t)) = t)
    (hf : flOf i = none) (hm : mbAfter τ i = τ.mb) (hwm : writesMem i = false)
    (hu : (ubNew τ i).toList ++ ubKill τ.ub i = u τ.ub) :
    (fastU (Taint.stepKDFn i) u).run τ = step τ i := by
  have hb : baseStep τ i = (Taint.stepKDFn i).run τ.t := by
    rw [baseStep, hs, show (fun t => pbPost τ i (argPost τ i (post τ i t))) = id from funext hp, Option.map_id]
    exact taint_step _ _
  unfold step
  rw [hb, hf, hm, hsp, hu, pbAfter_of_not_writes hwm, hwm]
  obtain ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ := τ
  cases ok
  · rfl
  · simp only [fastU, runF_eq, Bool.cond_true, Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
    cases (Taint.stepKDFn i).run t with
    | none => rfl
    | some t' => simp only [forceList_eq]

theorem ubDrop2_eq {i : Instr} {a b : Reg} (hc : ∀ r, Taint.clobbers i r = (r == a || r == b))
    (ub : List (Reg × Nat)) : ubDrop2 a b ub = ubKill ub i := by
  simp only [ubKill, hc]
  cases ub with
  | nil => rfl
  | cons p ub => simp only [ubDrop2, KList.filter_eq, regEq_eq]

theorem post_mb_nil {τ : FT} (h : τ.mb = []) (d : Reg) (m : MemOp) (t : Taint.T) :
    post τ (.mov d (.mem m)) t = t := by
  simp only [post, h, List.find?_nil]
  split <;> rfl

theorem argPost_nil {τ : FT} (ha : τ.sa = []) (hp : τ.sp = []) (i : Instr) (t : Taint.T) :
    argPost τ i t = t := by
  unfold argPost saPub
  simp only [ha, hp, List.any_nil, Bool.false_eq_true, ↓reduceIte, List.find?_nil]
  split <;> (try split) <;> rfl

theorem pbPubK_eq (τ : FT) (m : MemOp) (w : Nat) : pbPubK τ.t τ.pb m w = pbPub τ m w := by
  unfold pbPubK pbPub; rw [addrOfK_eq]

theorem fastLoad_eq {i : Instr} {d : Reg} {m : MemOp} {w : Nat} {c : Taint.T → Bool}
    (hsp : isa.writesSp i = false)
    (hs : ∀ τ, special τ i = none) (hpost : ∀ τ t, τ.mb = [] → post τ i t = t)
    (hpb : ∀ τ t, pbPost τ i t =
      if (pbPub τ m w && c τ.t) = true then { t with regs := t.regs.insert d } else t)
    (hk : ∀ ub, ubKill ub i = ubDrop (some d) ub) (hu : ∀ τ, ubNew τ i = none) (hf : flOf i = none)
    (hwm : writesMem i = false) (hm : ∀ τ, mbAfter τ i = τ.mb) (τ : FT) :
    (fastLoad (Taint.stepKDFn i) d m w c i).run τ = step τ i := by
  have hb : baseStep τ i =
      ((Taint.stepKDFn i).run τ.t).map fun t' => pbPost τ i (argPost τ i (post τ i t')) := by
    rw [baseStep, hs]; exact congrArg (Option.map _) (taint_step _ _)
  unfold step
  rw [hb, hk, hm, hsp, hu, hf, pbAfter_of_not_writes hwm, hwm]
  have hq := pbPubK_eq τ m w
  have hpost' := hpost τ
  have hpb' := hpb τ
  obtain ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ := τ
  cases ok
  · rfl
  · simp only [fastLoad, Bool.cond_true, Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
    cases (Taint.stepKDFn i).run t with
    | none => rfl
    | some t' =>
      simp only at hq
      simp only [Option.map_some, Bool.cond_eq_ite, Option.toList, List.nil_append, hq, Taint.forceT_eq,
        forceList_eq, insReg_eq]
      cases mb <;> cases sa <;> cases sp <;> (try simp only [hpost' _ rfl]) <;> (try simp only [argPost_nil]) <;>
        rw [hpb']

theorem stepFn_eq (i : Instr) (τ : FT) : (stepFn i).run τ = step τ i := by
  unfold stepFn
  cases hsp : isa.writesSp i
  · cases hpl : isPlain i
    · simp only [Bool.cond_false]
      cases i
      case store m r | store32 m r | store8 m r | store16 m r =>
        cases hx : m.index
        · simp only [hx, Option.isNone_none, Bool.cond_true]
          refine fastStore_eq hsp (fun τ => baseStep_store ?_ (fun _ => rfl) rfl) (fun _ => rfl) rfl (fun _ => rfl)
            (fun τ => ?_) rfl (pbStore_eq rfl hx fun _ => rfl) τ
          · simp only [special, hx, storeW]
          · rw [← mbStore_eq hx]; unfold mbAfter mbStoreM; simp only [storeW]; rfl
        · simp only [hx, Option.isNone_some, Bool.cond_false]
      case movdquStore m x =>
        cases hx : m.index
        · simp only [hx, Option.isNone_none, Bool.cond_true]
          refine fastStore_eq hsp (fun τ => ?_) (fun _ => rfl) rfl (fun _ => rfl)
            (fun τ => ?_) rfl (pbStore_eq rfl hx fun τ => ?_) τ
          · cases hxp : xpub τ.t x
            · exact baseStep_store (p := false) (by simp only [special, hx, hxp, Bool.false_eq_true, ↓reduceIte])
                (fun _ => rfl) rfl
            · have hs : special τ (.movdquStore m x) = storeStep τ.t m 16 true := by
                simp only [special, hx, hxp, ↓reduceIte]
              cases hmp : memPub τ.t m
              · have h1 : storeStep τ.t m 16 true = none := by
                  simp only [storeStep, hmp, Bool.false_eq_true, ↓reduceIte]
                have h := baseStep_store (m := m) (w := 16) (p := false) (hs.trans h1) (fun _ => rfl) rfl
                rwa [hmp] at h
              · rw [baseStep, hs]
                simp only [storeStep, hmp, ↓reduceIte, Option.map_some]
          · rw [← mbStore_eq hx]; unfold mbAfter mbStoreM; simp only [storeW]; rfl
          · simp only [stPub, hx, Option.isNone_none, Bool.true_or, Bool.and_true]
        · simp only [hx, Option.isNone_some, Bool.cond_false]
      case vmovdquStore l m x =>
        cases l <;> cases hx : m.index
        all_goals first
          | (simp only [hx, Option.isNone_some, Bool.cond_false]
             refine fastStoreI_eq hsp (fun τ => baseStep_store (p := false) ?_ (fun _ => rfl) rfl) (fun _ => rfl) rfl
               (fun _ => rfl) (mbStoreI_eq rfl (fun _ _ h => nomatch h)) rfl (pbStoreI_eq rfl fun _ => rfl) τ
             simp only [special])
          | (simp only [hx, Option.isNone_none, Bool.cond_true]
             refine fastStore_eq hsp (fun τ => baseStep_store (p := false) ?_ (fun _ => rfl) rfl) (fun _ => rfl) rfl
               (fun _ => rfl) (fun τ => ?_) rfl (pbStore_eq rfl hx fun _ => rfl) τ
             · simp only [special]
             · rw [← mbStore_eq hx]; unfold mbAfter mbStoreM; simp only [storeW]; rfl)
      case vmovdqu32Store m x | evStore m x | e5ExtractStore m x k | stmxcsr m =>
        cases hx : m.index
        · simp only [hx, Option.isNone_none, Bool.cond_true]
          refine fastStore_eq hsp (fun τ => baseStep_store (p := false) ?_ (fun _ => rfl) rfl) (fun _ => rfl) rfl
            (fun _ => rfl) (fun τ => ?_) rfl (pbStore_eq rfl hx fun _ => rfl) τ
          · simp only [special]
          · rw [← mbStore_eq hx]; unfold mbAfter mbStoreM; simp only [storeW]; rfl
        · simp only [hx, Option.isNone_some, Bool.cond_false]
          refine fastStoreI_eq hsp (fun τ => baseStep_store (p := false) ?_ (fun _ => rfl) rfl) (fun _ => rfl) rfl
            (fun _ => rfl) (mbStoreI_eq rfl (fun _ _ h => nomatch h)) rfl (pbStoreI_eq rfl fun _ => rfl) τ
          simp only [special]
      case mov d src =>
        cases src with
        | reg => rfl
        | mem m =>
          exact fastLoad_eq hsp (fun _ => rfl) (fun τ t h => post_mb_nil h d m t)
            (fun _ _ => by simp only [pbPost, Bool.and_true])
            (fun ub => (ubDrop_eq (i := .mov d (.mem m)) (fun _ => rfl) ub).symm) (fun _ => rfl) rfl rfl
            (fun _ => rfl) τ
        | imm v =>
          refine fastU_eq hsp rfl (fun _ => rfl) rfl rfl rfl ?_
          rw [← ubDrop_eq (i := .mov d (.imm v)) (fun _ => rfl)]
          cases hm : v.msb <;> simp [ubNew, hm] <;> rfl
      case mov32 d src =>
        cases src with
        | reg => rfl
        | mem m =>
          exact fastLoad_eq hsp (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => by simp only [pbPost, Bool.and_true])
            (fun ub => (ubDrop_eq (i := .mov32 d (.mem m)) (fun _ => rfl) ub).symm) (fun _ => rfl) rfl rfl
            (fun _ => rfl) τ
        | imm v =>
          refine fastU_eq hsp rfl (fun _ => rfl) rfl rfl rfl ?_
          rw [← ubDrop_eq (i := .mov32 d (.imm v)) (fun _ => rfl)]
          rfl
      case cmov c d src =>
        have hk : ∀ ub, ubKill ub (.cmov c d src) = ubDrop (some d) ub := fun ub =>
          (ubDrop_eq (i := .cmov c d src) (fun _ => rfl) ub).symm
        cases src with
        | mem m =>
          cases c <;>
            exact fastLoad_eq hsp (fun _ => rfl) (fun _ _ _ => rfl)
              (fun _ _ => by simp only [pbPost, Bool.and_assoc]) hk (fun _ => rfl) rfl rfl (fun _ => rfl) τ
        | reg x =>
          cases c
          case b =>
            refine fastG_eq hsp rfl (fun _ => rfl) rfl rfl rfl ?_
            rw [hk]
            obtain ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ := τ
            simp only [ubNew, cmovUb, ubOfK_eq]
            rcases fl with _ | ⟨a, b⟩
            · rfl
            · simp only [regEq_eq]
              by_cases h : (a, b) = (x, d)
              · cases h
                simp only [beq_self_eq_true, Bool.and_self, Bool.cond_true, ↓reduceIte]
                cases ubOf ub d <;> rfl
              · have h1 : (some (a, b) == some (x, d)) = false := by simpa using h
                have h2 : (a == x && b == d) = false := by
                  rw [Bool.and_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]
                  by_cases ha : a = x
                  · exact .inr fun hb => h (by rw [ha, hb])
                  · exact .inl ha
                simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Bool.cond_false, Option.toList, List.nil_append]
          all_goals exact fastU_eq hsp rfl (fun _ => rfl) rfl rfl rfl (hk τ.ub)
        | imm v => cases c <;> exact fastU_eq hsp rfl (fun _ => rfl) rfl rfl rfl (hk τ.ub)
      case alu op d src =>
        cases op
        case xor =>
          cases src with
          | reg d' =>
            have hd : d = d' := by simpa [isPlain] using hpl
            subst hd
            refine fastG_eq hsp rfl
              (fun _ => by simp only [post, pbPost, argPost, beq_self_eq_true, ↓reduceIte, insReg_eq]) rfl rfl rfl ?_
            exact (ubDrop_eq (i := .alu .xor d (.reg d)) (fun _ => rfl) τ.ub).symm
          | _ => rfl
        case and =>
          cases src with
          | imm v =>
            refine fastU_eq hsp rfl (fun _ => rfl) rfl rfl rfl ?_
            rw [← ubDrop_eq (i := .alu .and d (.imm v)) (fun _ => rfl)]
            cases hm : v.msb <;> simp [ubNew, hm] <;> rfl
          | _ => rfl
        case cmp =>
          cases src with
          | reg b =>
            refine fastG_eq hsp rfl (fun _ => rfl) rfl rfl rfl ?_
            exact (ubDrop_eq (i := .alu .cmp d (.reg b)) (fun _ => rfl) τ.ub).symm
          | _ => rfl
        all_goals (cases src <;> rfl)
      case alu32 op d src =>
        cases op
        case xor =>
          cases src with
          | reg d' =>
            have hd : d = d' := by simpa [isPlain] using hpl
            subst hd
            refine fastG_eq hsp rfl
              (fun _ => by simp only [post, pbPost, argPost, beq_self_eq_true, ↓reduceIte, insReg_eq]) rfl rfl rfl ?_
            exact (ubDrop_eq (i := .alu32 .xor d (.reg d)) (fun _ => rfl) τ.ub).symm
          | _ => rfl
        case and =>
          cases src with
          | imm v =>
            refine fastU_eq hsp rfl (fun _ => rfl) rfl rfl rfl ?_
            rw [← ubDrop_eq (i := .alu32 .and d (.imm v)) (fun _ => rfl)]
            rfl
          | _ => rfl
        all_goals (cases src <;> rfl)
      case xop op =>
        cases op with
        | bin bop x x' =>
          cases bop
          case pxor =>
            have hk : ubKill τ.ub (.xop (.bin .pxor x x')) = τ.ub := by
              simp only [ubKill, Taint.clobbers, Taint.dstOf]
              exact List.filter_eq_self.mpr fun _ _ => rfl
            by_cases hxx : x = x'
            · subst hxx
              simp only [beq_self_eq_true, Bool.cond_true]
              exact fastG_eq hsp rfl (fun _ => by simp [post, argPost, pbPost, insX_eq]) rfl rfl rfl
                ((congrArg _ hk).trans (List.nil_append _))
            · have hne : (x == x') = false := by simpa using hxx
              simp only [hne, Bool.cond_false]
              exact fastG_eq hsp rfl (fun _ => by simp [post, argPost, pbPost, hne]) rfl rfl rfl
                ((congrArg _ hk).trans (List.nil_append _))
          all_goals rfl
        | _ => rfl
      case mul r =>
        exact fastU_eq hsp rfl (fun _ => rfl) rfl rfl rfl (ubDrop2_eq (i := .mul r) (fun _ => rfl) τ.ub).symm
      case mulx hi lo src =>
        exact fastU_eq hsp rfl (fun _ => rfl) rfl rfl rfl
          (ubDrop2_eq (i := .mulx hi lo src) (fun _ => rfl) τ.ub).symm
      all_goals rfl
    · exact fastFn_eq hpl hsp τ
  · show none = _
    unfold step; rw [hsp]; simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem isSp_eq (d : Reg) : isSp d = (some d == some Reg.rsp) := by cases d <;> rfl

theorem isSpR_eq (d : Reg) : isSpR d = (d == Reg.rsp) := by cases d <;> rfl

theorem stepFn1_eq (i : Instr) : stepFn1 i = stepFn i := by
  unfold stepFn1 stepFn
  simp only [isSp_eq, isSpR_eq, Taint.stepKeepFn_eq, slowFn_eq]
  cases i with
  | mov d src | mov32 d src => cases src <;> rfl
  | alu op d src | alu32 op d src => cases op <;> cases src <;> rfl
  | cmov c d src => cases c <;> cases src <;> rfl
  | xop op =>
    cases op with
    | bin op a b => cases op <;> rfl
    | _ => rfl
  | vmovdquStore l m x => cases l <;> rfl
  | _ => rfl

theorem stepFn1K_eq (i : Instr) : stepFn1K i = stepFn1 i := by
  cases i with
  | mov d src | mov32 d src => cases src <;> rfl
  | alu op d src | alu32 op d src => cases op <;> cases src <;> rfl
  | cmov c d src => cases c <;> cases src <;> rfl
  | xop op =>
    cases op with
    | bin op a b => cases op <;> rfl
    | _ => rfl
  | vmovdquStore l m x => cases l <;> rfl
  | _ => rfl

theorem stepF_eq : stepF = step := by
  funext τ i; show (stepFn1K i).run τ = _; rw [stepFn1K_eq, stepFn1_eq]; exact stepFn_eq i τ

theorem eq2_iff {a b : Nat × Nat} : eq2 a b = true ↔ a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp [eq2]

theorem eq3_iff {a b : Nat × Nat × Nat} : eq3 a b = true ↔ a = b := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp [eq3, and_assoc]

theorem eq4_iff {a b : Nat × Nat × Nat × Nat} : eq4 a b = true ↔ a = b := by
  obtain ⟨a1, a2, a3, a4⟩ := a; obtain ⟨b1, b2, b3, b4⟩ := b
  simp [eq4, and_assoc]

theorem subl_sublist : ∀ {as bs : List (Nat × Nat × Nat)}, subl as bs = true → as.Sublist bs
  | [], _, _ => List.nil_sublist _
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, h => by
    change (bif eq3 a b then subl as bs else subl (a :: as) bs) = true at h
    cases he : eq3 a b
    · rw [he] at h; exact (subl_sublist h).cons b
    · rw [he] at h; rw [eq3_iff.mp he]; exact (subl_sublist h).cons_cons b

theorem slotsLe_eq (as bs : List (Nat × Nat × Nat)) : slotsLe as bs = as.all (bs.contains ·) := by
  unfold slotsLe
  cases h : subl as bs
  · simp only [Bool.false_or, KList.all_eq, mem3_eq]
  · simp only [Bool.true_or]
    symm
    simp only [List.all_eq_true, List.contains_iff_mem]
    exact fun x hx => (subl_sublist h).subset hx

theorem leKF_eq : leKF = Taint.le := by
  funext τ σ
  rw [← leK_eq]
  simp only [leKF, leK, natsEq_eq, slotsLe_eq, mem3_eq, KList.all_eq]

theorem any_eq2 (l : List (Nat × Nat)) (p : Nat × Nat) : KList.any l (eq2 p) = l.contains p := by
  rw [KList.any_eq, Bool.eq_iff_iff, List.any_eq_true, List.contains_iff_mem]
  exact ⟨fun ⟨x, hx, h⟩ => (eq2_iff.mp h) ▸ hx, fun h => ⟨p, h, eq2_iff.mpr rfl⟩⟩

theorem any_eq4 (l : List (Nat × Nat × Nat × Nat)) (p : Nat × Nat × Nat × Nat) :
    KList.any l (eq4 p) = l.contains p := by
  rw [KList.any_eq, Bool.eq_iff_iff, List.any_eq_true, List.contains_iff_mem]
  exact ⟨fun ⟨x, hx, h⟩ => (eq4_iff.mp h) ▸ hx, fun h => ⟨p, h, eq4_iff.mpr rfl⟩⟩

theorem leF_eq : leF = le := by
  funext τ σ
  simp only [leF, le, KList.beq_eq, natsEq_eq, leKF_eq, ← leK_eq, any_eq2, any_eq4, KList.all_eq, ubOfK_eq,
    KList.ble_eq, mem3_eq]

theorem eqs3_eq : ∀ {as bs : List (Nat × Nat × Nat)}, eqs3 as bs = true → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, h => by
    change (eq3 a b && eqs3 as bs) = true at h
    rw [Bool.and_eq_true] at h
    rw [eq3_iff.mp h.1, eqs3_eq h.2]

theorem meetT_eq : meetT = Taint.meet := by
  funext τ₁ τ₂
  obtain ⟨r₁, f₁, l₁, b₁, s₁, lo₁, x₁⟩ := τ₁
  obtain ⟨r₂, f₂, l₂, b₂, s₂, lo₂, x₂⟩ := τ₂
  have hb : KList.filter (memB · b₂) b₁ = b₁.filter (b₂.contains ·) := by
    simp only [KList.filter_eq, memB_eq]
  have hs : (bif eqs3 s₁ s₂ then s₁ else KList.filter (mem3 · s₂) s₁) = s₁.filter (s₂.contains ·) := by
    cases h : eqs3 s₁ s₂
    · simp only [Bool.cond_false, KList.filter_eq, mem3_eq]
    · rw [Bool.cond_true, ← eqs3_eq h]
      exact (List.filter_eq_self.mpr fun x hx => List.contains_iff_mem.mpr hx).symm
  simp only [meetT, Taint.meet, natsEq_eq, hb, hs]
  cases h : (l₁ == l₂) <;> simp_all

theorem meetF_eq : meetF = meet := by
  funext τ₁ τ₂
  simp only [meetF, meet, KList.beq_eq, natsEq_eq, meetT_eq, ubOfK_eq, KList.filter_eq, any_eq2, any_eq4, mem3_eq,
    Bool.cond_eq_ite]

/-! ## The analysis -/

/-- The residue analysis, as a `VG.Taint`. -/
def rtaint : VG.Taint isa where
  T := FT
  Agree := Agree
  step := stepF
  step_sound ha hs := step_sound ha (stepF_eq ▸ hs)
  condPub τ _ := τ.ok && τ.t.flags
  cond_sound := cond_sound
  meet := meetF
  meet_left h := meetF_eq ▸ meet_left h
  meet_right h := meetF_eq ▸ meet_right h
  le := leF
  le_sound hle := le_sound (leF_eq ▸ hle)
  call := callF
  call_sound := call_sound
  ret := retF
  ret_sound := ret_sound
  push := pushF
  push_sound := push_sound
  pop := popF
  pop_sound := pop_sound

end VG.X86_64.RTaint
