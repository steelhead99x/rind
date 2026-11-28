module

public import VerifiedGarbage.Proof.Framework.RegSet

/-!
# The order of register sets

`subset` is a partial order, with `union` and `inter` its join and meet, for
the monotonicity of the taint analyses (`Taint.Frame`).
-/

@[expose] public section

namespace VG

namespace RegSet

variable {R : Type} [RegIdx R]

omit [RegIdx R] in
theorem subset_iff {a b : RegSet R} :
    a.subset b = true ↔ ∀ i, a.bits.testBit i = true → b.bits.testBit i = true := by
  rw [subset_eq, beq_iff_eq]
  constructor
  · intro h i hi
    rw [← h, Nat.testBit_and, Bool.and_eq_true] at hi
    exact hi.2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases ha : a.bits.testBit i
    · rfl
    · rw [h i ha]; rfl

omit [RegIdx R] in
theorem subset_refl (a : RegSet R) : a.subset a = true := subset_iff.mpr fun _ h => h

omit [RegIdx R] in
theorem subset_trans {a b c : RegSet R} (h₁ : a.subset b = true) (h₂ : b.subset c = true) :
    a.subset c = true :=
  subset_iff.mpr fun i h => subset_iff.mp h₂ i (subset_iff.mp h₁ i h)

omit [RegIdx R] in
theorem empty_subset (a : RegSet R) : (empty : RegSet R).subset a = true :=
  subset_iff.mpr fun i h => by simp [empty] at h

theorem insert_mono {a b : RegSet R} (h : a.subset b = true) (r : R) :
    (a.insert r).subset (b.insert r) = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [insert_bits, Nat.testBit_or, Bool.or_eq_true] at hi ⊢
  exact hi.imp (subset_iff.mp h i) id

theorem erase_mono {a b : RegSet R} (h : a.subset b = true) (r : R) :
    (a.erase r).subset (b.erase r) = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [erase_bits, Nat.testBit_xor, Nat.testBit_and] at hi ⊢
  cases ha : a.bits.testBit i <;> cases hr : (bit r).testBit i <;> simp_all [subset_iff.mp h i]

theorem erase_subset (a : RegSet R) (r : R) : (a.erase r).subset a = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [erase_bits, Nat.testBit_xor, Nat.testBit_and] at hi
  cases ha : a.bits.testBit i <;> simp_all

theorem subset_insert (a : RegSet R) (r : R) : a.subset (a.insert r) = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [insert_bits, Nat.testBit_or, hi, Bool.true_or]

omit [RegIdx R] in
theorem inter_mono {a b c d : RegSet R} (h₁ : a.subset c = true) (h₂ : b.subset d = true) :
    (a.inter b).subset (c.inter d) = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [inter_bits, Nat.testBit_and, Bool.and_eq_true] at hi ⊢
  exact ⟨subset_iff.mp h₁ i hi.1, subset_iff.mp h₂ i hi.2⟩

theorem mem_mono {a b : RegSet R} (h : a.subset b = true) {r : R} (hr : a.mem r = true) :
    b.mem r = true := mem_of_subset h hr

/-- The union of two sets. -/
def union (a b : RegSet R) : RegSet R := ⟨Nat.lor a.bits b.bits⟩

omit [RegIdx R] in
theorem subset_union_left (a b : RegSet R) : a.subset (a.union b) = true :=
  subset_iff.mpr fun i h => by
    show (a.bits ||| b.bits).testBit i = true
    rw [Nat.testBit_or, h, Bool.true_or]

omit [RegIdx R] in
theorem subset_union_right (a b : RegSet R) : b.subset (a.union b) = true :=
  subset_iff.mpr fun i h => by
    show (a.bits ||| b.bits).testBit i = true
    rw [Nat.testBit_or, h, Bool.or_true]

omit [RegIdx R] in
theorem union_subset {a b c : RegSet R} (ha : a.subset c = true) (hb : b.subset c = true) :
    (a.union b).subset c = true :=
  subset_iff.mpr fun i h => by
    have h : (a.bits ||| b.bits).testBit i = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    exact h.elim (subset_iff.mp ha i) (subset_iff.mp hb i)

omit [RegIdx R] in
theorem inter_subset_left (a b : RegSet R) : (a.inter b).subset a = true :=
  subset_iff.mpr fun i h => by
    rw [inter_bits, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1

omit [RegIdx R] in
theorem inter_subset_right (a b : RegSet R) : (a.inter b).subset b = true :=
  subset_iff.mpr fun i h => by
    rw [inter_bits, Nat.testBit_and, Bool.and_eq_true] at h; exact h.2

omit [RegIdx R] in
theorem subset_inter {a b c : RegSet R} (hb : a.subset b = true) (hc : a.subset c = true) :
    a.subset (b.inter c) = true :=
  subset_iff.mpr fun i h => by
    rw [inter_bits, Nat.testBit_and, subset_iff.mp hb i h, subset_iff.mp hc i h]; rfl

omit [RegIdx R] in
theorem subset_of_bits_zero {a : RegSet R} (h : a.bits = 0) (b : RegSet R) :
    a.subset b = true :=
  subset_iff.mpr fun i hi => by rw [h, Nat.zero_testBit] at hi; cases hi

/-- `Φ` stays a subset of `σ` with `d` changed, if `d` is not in `F ⊇ Φ`. -/
theorem subset_insert_of {Φ σ : RegSet R} (hΦ : Φ.subset σ = true)
    (d : R) : Φ.subset (σ.insert d) = true :=
  subset_trans hΦ (subset_insert σ d)

theorem subset_erase_of {Φ F σ : RegSet R} (hΦF : Φ.subset F = true) (hΦ : Φ.subset σ = true)
    {d : R} (hd : F.mem d = false) : Φ.subset (σ.erase d) = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [erase_bits, Nat.testBit_xor, Nat.testBit_and, subset_iff.mp hΦ i hi, testBit_bit]
  have hF := subset_iff.mp hΦF i hi
  have hne : RegIdx.idx d ≠ i := by
    intro e
    have : F.mem d = true := (mem_iff (s := F) (r := d)).mpr (e ▸ hF)
    rw [hd] at this; cases this
  simp [hne]

end RegSet

end VG
