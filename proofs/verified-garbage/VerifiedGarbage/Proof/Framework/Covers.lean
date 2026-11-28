module

import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# Covering regions

`Covers rs rs'`: every access the regions `rs` permit, the regions `rs'`
permit. Inlining verified code (`Inline.lean`) and calls narrow a state's
permissions to regions that its own cover.
-/

@[expose] public section

namespace VG

/-- Every access that `rs` permits, `rs'` permits. -/
def Covers (rs rs' : List Region) : Prop := ∀ a n, InRegions rs a n → InRegions rs' a n

namespace Covers

theorem refl (rs : List Region) : Covers rs rs := fun _ _ h => h

theorem trans {rs rs' rs'' : List Region} (h : Covers rs rs') (h' : Covers rs' rs'') :
    Covers rs rs'' := fun a n hi => h' a n (h a n hi)

theorem nil {rs : List Region} : Covers [] rs := fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil

theorem append {rs rs' ts ts' : List Region} (h : Covers rs rs') (h' : Covers ts ts') :
    Covers (rs ++ ts) (rs' ++ ts') := by
  intro a n ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r', hr', hc'⟩ := h a n ⟨r, hr, hc⟩; exact ⟨r', List.mem_append_left _ hr', hc'⟩
  · obtain ⟨r', hr', hc'⟩ := h' a n ⟨r, hr, hc⟩; exact ⟨r', List.mem_append_right _ hr', hc'⟩

/-- Both lists of regions are within `rs'`. -/
theorem append_left {rs ts rs' : List Region} (h : Covers rs rs') (h' : Covers ts rs') :
    Covers (rs ++ ts) rs' := by
  intro a n ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact h a n ⟨r, hr, hc⟩
  · exact h' a n ⟨r, hr, hc⟩

theorem cons {r : Region} {rs rs' : List Region} (h : Covers [r] rs') (h' : Covers rs rs') :
    Covers (r :: rs) rs' := append_left (rs := [r]) h h'

theorem pair {a b : Region} {rs : List Region} (ha : Covers [a] rs) (hb : Covers [b] rs) :
    Covers [a, b] rs := ha.cons (hb.cons nil)

/-- Each region is within `rs'`. -/
theorem of_forall {rs rs' : List Region} (h : ∀ r ∈ rs, Covers [r] rs') : Covers rs rs' :=
  fun a n ⟨r, hr, hc⟩ => h r hr a n ⟨_, List.mem_singleton_self _, hc⟩

/-- Each region is one of `rs'`. -/
theorem of_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' :=
  fun _ _ ⟨r, hr, hc⟩ => ⟨r, h r hr, hc⟩

/-- Regions within the writable regions are within all of them. -/
theorem right {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun a n hi =>
  let ⟨r, hr, hc⟩ := h a n hi
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem left {rs rd wr : List Region} (h : Covers rs rd) : Covers rs (rd ++ wr) := fun a n hi =>
  let ⟨r, hr, hc⟩ := h a n hi
  ⟨r, List.mem_append_left _ hr, hc⟩

/-- Sub-regions: each region of `rs` lies at some offset within a region of `rs'`. -/
theorem of_sub {rs rs' : List Region}
    (h : ∀ r ∈ rs, ∃ r' ∈ rs', ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len) :
    Covers rs rs' := by
  intro a n ⟨r, hr, hc⟩
  obtain ⟨r', hr', off, hb, hl⟩ := h r hr
  refine ⟨r', hr', ?_⟩
  unfold Region.Contains at *
  rw [hb] at hc
  have : (a - r'.base).toNat ≤ (a - (r'.base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - r'.base = (a - (r'.base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by
        rw [Offset.sub_add_eq, BitVec.sub_add_cancel],
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega_using [hc, hl, this]

/-- The region of an access the regions `rs` permit. -/
theorem one {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) : Covers [⟨a, n⟩] rs := by
  intro a' n' ⟨r0, hr0, hc⟩
  simp only [List.mem_singleton] at hr0
  subst hr0
  obtain ⟨r, hr, hc'⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc hc' ⊢
  rw [show a' - r.base = (a' - a) + (a - r.base) by rw [Offset.sub_add_sub_cancel], BitVec.toNat_add]
  have := Nat.mod_le ((a' - a).toNat + (a - r.base).toNat) (2 ^ 64)
  omega_using [hc, hc']

/-- A frame's push inserts its region into the writable regions of both
states. -/
theorem push {xs ys xs' ys' : List Region} (f : Region) (h : Covers (xs ++ ys) (xs' ++ ys')) :
    Covers (xs ++ f :: ys) (xs' ++ f :: ys') := fun a n hi =>
  (InRegions_append_cons.mp hi).elim (fun hc => InRegions_append_cons.mpr (.inl hc))
    fun hi => InRegions_append_cons.mpr (.inr (h a n hi))

end Covers

end VG
