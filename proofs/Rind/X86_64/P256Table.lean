import Rind.X86_64.Funs
import Rind.P256Group
open Aeneas Aeneas.Std rind.spec

/-!
# rind's P-256 generator table on x86_64

`tabulated` proves that the table `admin/p256-precomp` writes for x86_64, as
Aeneas translates it, holds the multiples of G that `base_multiply`'s Booth
driver selects: entry j of row i, counting entries from 1, is j·2⁷ⁱ·G in
Montgomery form. The kernel checks each entry against the one before it with
`nist.addOk`, which needs no inversion, and each row's first entry as twice
the last row's 64th, since 2 · 64 = 2⁷.
-/

namespace rind.x86_64

namespace P256Base

/-- Entry `j` of row `i`, counting from 1, is j·2^(7i)·G in Montgomery form
with coordinates below p. -/
def Tabulated7 (t : Std.Array (Std.Array U64 512#usize) 37#usize) : Prop :=
  ∀ i < 37, ∀ j, 1 ≤ j → j ≤ 64 →
    p256Represents2 (p256Pow p256G (2 ^ (7 * i) * j)) (pairNat ((t.val[i]!).val.drop (8 * (j - 1))))

/-- Entry `j` of row `i`, counting entries from 1: Montgomery-form coordinates. -/
def tableEntry (t : Std.Array (Std.Array U64 512#usize) 37#usize) (i j : Nat) : Nat × Nat :=
  pairNat ((t.val[i]!).val.drop (8 * (j - 1)))

/-- The point whose Montgomery-form coordinates these are. -/
def unmont (xy : Nat × Nat) : Nat × Nat :=
  (p256RInv * xy.1 % p256, p256RInv * xy.2 % p256)

/-- Each row's first entry is twice the last row's 64th, starting from G, and
each row's other entries are the sums of their predecessor and the first,
with every coordinate below `p256`. -/
def tableOk (t : Std.Array (Std.Array U64 512#usize) 37#usize) : Bool :=
  some (unmont (tableEntry t 0 1)) == p256G &&
  (List.range 37).all (fun i =>
    (List.range 64).all (fun k => (tableEntry t i (k + 1)).1 < p256 && (tableEntry t i (k + 1)).2 < p256) &&
    nist.addOk p256 (unmont (tableEntry t i 1)) (unmont (tableEntry t i 1)) (unmont (tableEntry t i 2)) &&
    (List.range 62).all fun k =>
      nist.addOk p256 (unmont (tableEntry t i (k + 2))) (unmont (tableEntry t i 1)) (unmont (tableEntry t i (k + 3)))) &&
  (List.range 36).all fun i =>
    nist.addOk p256 (unmont (tableEntry t i 64)) (unmont (tableEntry t i 64)) (unmont (tableEntry t (i + 1) 1))

theorem tabulated_of_ok {t : Std.Array (Std.Array U64 512#usize) 37#usize} (h : tableOk t = true) :
    Tabulated7 t := by
  simp only [tableOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨hG, hrows⟩, hnext⟩ := h
  obtain ⟨g, hg⟩ : ∃ g, nist.fromM g = p256G := fromM_of_onCurve p256OnCurve_G
  let A i j := unmont (tableEntry t i j)
  have hrow : ∀ i < 37, nist.fromM ((2 ^ (7 * i)) • g) = some (A i 1) →
      ∀ j, 1 ≤ j → j ≤ 64 → nist.fromM (j • (2 ^ (7 * i)) • g) = some (A i j) := by
    intro i hi hb j hj1 hj
    induction j, hj1 using Nat.le_induction with
    | base => rwa [one_nsmul]
    | succ j hj1 ih =>
      obtain ⟨⟨-, h2⟩, hk⟩ := hrows i hi
      rw [succ_nsmul, ← nist.fromM_add, ih (by omega), hb]
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hj2
      · exact nist.addOk_spec h2
      · have := nist.addOk_spec (hk (j - 2) (by omega))
        rwa [show j - 2 + 2 = j by omega, show j - 2 + 3 = j + 1 by omega] at this
  have hbase : ∀ i < 37, nist.fromM ((2 ^ (7 * i)) • g) = some (A i 1) := by
    intro i hi
    induction i with
    | zero =>
      rw [mul_zero, pow_zero, one_nsmul, hg]
      exact hG.symm
    | succ i ih =>
      have h64 := hrow i (by omega) (ih (by omega)) 64 (by omega) le_rfl
      rw [show 2 ^ (7 * (i + 1)) = 64 * 2 ^ (7 * i) + 64 * 2 ^ (7 * i) by ring, add_nsmul, mul_nsmul',
        ← nist.fromM_add, h64]
      exact nist.addOk_spec (hnext i (by omega))
  intro i hi j hj1 hj
  obtain ⟨⟨hlt, -⟩, -⟩ := hrows i hi
  obtain ⟨h1, h2⟩ := by simpa using hlt (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega] at h1 h2
  rw [← hg, p256Pow, nist.pow_fromM, mul_comm, mul_nsmul', hrow i hi (hbase i hi) j hj1 hj]
  exact ⟨h1, h2, rfl⟩

/-- rind's x86_64 generator table holds the multiples of G that
`base_multiply`'s Booth driver selects. -/
theorem tabulated : Tabulated7 mid.p256.precomp.CURVE_GENERATOR_PRECOMP :=
  tabulated_of_ok (by decide +kernel)

/-- Row 0's first 32 entries are G to 32G, as `p256Tabulates` reads a row:
what a twin multiplication's generator half selects from. -/
theorem first_row : ∀ j, 1 ≤ j → j ≤ 32 →
    p256Represents2 (p256Pow p256G j)
      (pairNat ((mid.p256.precomp.CURVE_GENERATOR_PRECOMP.val[0]!).val.drop (8 * (j - 1)))) := by
  intro j hj1 hj
  have := tabulated 0 (by omega) j hj1 (by omega)
  simpa using this

end P256Base

end rind.x86_64
