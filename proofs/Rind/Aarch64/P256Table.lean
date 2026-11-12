import Rind.Aarch64.S2nBignum
import Rind.P256Group
open Aeneas Aeneas.Std rind.spec

/-!
# rind's P-256 generator table

`tabulated` proves that the table `admin/p256-precomp` writes, as Aeneas
translates it, holds the multiples of G that s2n-bignum's proof of
`p256_scalarmulbase` assumes. The kernel checks each entry against the one
before it with `addOk`, which needs no inversion, and `p256Pow_fromM` turns
those sums into multiples.
-/

namespace rind.aarch64

/-- Entry `j` of row `i`, counting entries from 1, as `p256Tabulates` reads it:
Montgomery-form coordinates. -/
def tableEntry (t : Std.Array (Std.Array U64 256#usize) 43#usize) (i j : Nat) : Nat × Nat :=
  pairNat ((t.val[i]!).val.drop (8 * (j - 1)))

/-- The point whose Montgomery-form coordinates these are. -/
def unmont (xy : Nat × Nat) : Nat × Nat :=
  (p256RInv * xy.1 % p256, p256RInv * xy.2 % p256)

/-- Each row's first entry is the last row's 64th multiple, starting from G,
and each row's other entries are the sums of their predecessor and the first,
with every coordinate below `p256`. -/
def tableOk (t : Std.Array (Std.Array U64 256#usize) 43#usize) : Bool :=
  some (unmont (tableEntry t 0 1)) == p256G &&
  (List.range 43).all (fun i =>
    (List.range 32).all (fun k => (tableEntry t i (k + 1)).1 < p256 && (tableEntry t i (k + 1)).2 < p256) &&
    addOk (unmont (tableEntry t i 1)) (unmont (tableEntry t i 1)) (unmont (tableEntry t i 2)) &&
    (List.range 30).all fun k =>
      addOk (unmont (tableEntry t i (k + 2))) (unmont (tableEntry t i 1)) (unmont (tableEntry t i (k + 3)))) &&
  (List.range 42).all fun i =>
    addOk (unmont (tableEntry t i 32)) (unmont (tableEntry t i 32)) (unmont (tableEntry t (i + 1) 1))

theorem tabulates_of_ok {t : Std.Array (Std.Array U64 256#usize) 43#usize} (h : tableOk t = true) :
    p256Tabulates p256G t := by
  simp only [tableOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨hG, hrows⟩, hnext⟩ := h
  obtain ⟨g, hg⟩ : ∃ g, fromM g = p256G := fromM_of_onCurve p256OnCurve_G
  let A i j := unmont (tableEntry t i j)
  have hrow : ∀ i < 43, fromM ((2 ^ (6 * i)) • g) = some (A i 1) →
      ∀ j, 1 ≤ j → j ≤ 32 → fromM (j • (2 ^ (6 * i)) • g) = some (A i j) := by
    intro i hi hb j hj1 hj
    induction j, hj1 using Nat.le_induction with
    | base => rwa [one_nsmul]
    | succ j hj1 ih =>
      obtain ⟨⟨-, h2⟩, hk⟩ := hrows i hi
      rw [succ_nsmul, ← fromM_add, ih (by omega), hb]
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hj2
      · exact addOk_spec h2
      · have := addOk_spec (hk (j - 2) (by omega))
        rwa [show j - 2 + 2 = j by omega, show j - 2 + 3 = j + 1 by omega] at this
  have hbase : ∀ i < 43, fromM ((2 ^ (6 * i)) • g) = some (A i 1) := by
    intro i hi
    induction i with
    | zero =>
      rw [mul_zero, pow_zero, one_nsmul, hg]
      exact hG.symm
    | succ i ih =>
      have h32 := hrow i (by omega) (ih (by omega)) 32 (by omega) le_rfl
      rw [show 2 ^ (6 * (i + 1)) = 32 * 2 ^ (6 * i) + 32 * 2 ^ (6 * i) by ring, add_nsmul, mul_nsmul',
        ← fromM_add, h32]
      exact addOk_spec (hnext i (by omega))
  intro i hi j hj1 hj
  obtain ⟨⟨hlt, -⟩, -⟩ := hrows i hi
  obtain ⟨h1, h2⟩ := by simpa using hlt (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega] at h1 h2
  rw [← hg, p256Pow_fromM, mul_comm, mul_nsmul', hrow i hi (hbase i hi) j hj1 hj]
  exact ⟨h1, h2, rfl⟩

/-- rind's generator table holds the multiples of G that s2n-bignum's proof
of `p256_scalarmulbase` assumes. -/
theorem tabulated : p256Tabulates p256G mid.p256.precomp.CURVE_GENERATOR_PRECOMP :=
  tabulates_of_ok (by decide +kernel)

end rind.aarch64
