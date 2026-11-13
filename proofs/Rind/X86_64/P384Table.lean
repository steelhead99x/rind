import Rind.X86_64.Funs
import Rind.P384Group
open Aeneas Aeneas.Std rind.spec

/-!
# rind's P-384 comb tables

`tabulated` proves that the tables `admin/p384-precomp` writes, as Aeneas
translates them, hold the multiples of G that `JacobianMontPoint::base_multiply`'s
comb looks up: entry d of table j is d·2²⁰ʲ·G. The kernel checks each entry
against the one before it with `addOk`, which needs no inversion, and each
table's first entry against the previous table's by `mulCheck`.
-/

set_option exponentiation.threshold 400

namespace rind.x86_64

namespace P384

/-- Entry `d` of comb table `j`, counting from 1, is d·2^(20j)·G in Montgomery form. -/
def CombTabulated (t : Std.Array (Std.Array U64 192#usize) 20#usize) : Prop :=
  ∀ j < 20, ∀ d, 1 ≤ d → d ≤ 16 →
    p384Represents2 (p384Pow p384G (d * 2 ^ (20 * j))) (pairNat6 ((t.val[j]!).val.drop (12 * (d - 1))))

/-- Entry `d` of table `j`, counting entries from 1: Montgomery-form coordinates. -/
def combEntry (t : Std.Array (Std.Array U64 192#usize) 20#usize) (j d : Nat) : Nat × Nat :=
  pairNat6 ((t.val[j]!).val.drop (12 * (d - 1)))

/-- The point whose Montgomery-form coordinates these are. -/
def unmont (xy : Nat × Nat) : Nat × Nat :=
  (p384RInv * xy.1 % p384, p384RInv * xy.2 % p384)

/-- Table 0's first entry is G, each table's first entry is 2²⁰ times the
last table's, and each table's other entries are the sums of their
predecessor and the first, with every coordinate below `p384`. -/
def combOk (t : Std.Array (Std.Array U64 192#usize) 20#usize) : Bool :=
  some (unmont (combEntry t 0 1)) == p384G &&
  (List.range 20).all (fun j =>
    (List.range 16).all (fun d => (combEntry t j (d + 1)).1 < p384 && (combEntry t j (d + 1)).2 < p384) &&
    nist.addOk p384 (unmont (combEntry t j 1)) (unmont (combEntry t j 1)) (unmont (combEntry t j 2)) &&
    (List.range 14).all fun d =>
      nist.addOk p384 (unmont (combEntry t j (d + 2))) (unmont (combEntry t j 1)) (unmont (combEntry t j (d + 3)))) &&
  (List.range 19).all fun j =>
    nist.mulCheck p384 (unmont (combEntry t j 1)) 21 (2 ^ 20) == some (unmont (combEntry t (j + 1) 1))

theorem tabulated_of_ok {t : Std.Array (Std.Array U64 192#usize) 20#usize} (h : combOk t = true) :
    CombTabulated t := by
  simp only [combOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨hG, hrows⟩, hnext⟩ := h
  obtain ⟨g, hg, -, -⟩ := p384_fromM_G
  let A j d := unmont (combEntry t j d)
  have hrow : ∀ j < 20, nist.fromM ((2 ^ (20 * j)) • g) = some (A j 1) →
      ∀ d, 1 ≤ d → d ≤ 16 → nist.fromM (d • (2 ^ (20 * j)) • g) = some (A j d) := by
    intro j hj hb d hd1 hd
    induction d, hd1 using Nat.le_induction with
    | base => rwa [one_nsmul]
    | succ d hd1 ih =>
      obtain ⟨⟨-, h2⟩, hk⟩ := hrows j hj
      rw [succ_nsmul, ← nist.fromM_add, ih (by omega), hb]
      rcases Nat.eq_or_lt_of_le hd1 with rfl | hd2
      · exact nist.addOk_spec h2
      · have := nist.addOk_spec (hk (d - 2) (by omega))
        rwa [show d - 2 + 2 = d by omega, show d - 2 + 3 = d + 1 by omega] at this
  have hbase : ∀ j < 20, nist.fromM ((2 ^ (20 * j)) • g) = some (A j 1) := by
    intro j hj
    induction j with
    | zero =>
      rw [mul_zero, pow_zero, one_nsmul, hg]
      exact hG.symm
    | succ j ih =>
      have hm := nist.mulCheck_spec _ _ (ih (by omega)) 21 _ _ (hnext j (by omega))
      rwa [← mul_nsmul', ← pow_add, show 20 + 20 * j = 20 * (j + 1) by ring] at hm
  intro j hj d hd1 hd
  obtain ⟨⟨hlt, -⟩, -⟩ := hrows j hj
  obtain ⟨h1, h2⟩ := by simpa using hlt (d - 1) (by omega)
  rw [show d - 1 + 1 = d by omega] at h1 h2
  rw [← hg, p384Pow, nist.pow_fromM, mul_nsmul', hrow j hj (hbase j hj) d hd1 hd]
  exact ⟨h1, h2, rfl⟩

/-- rind's comb tables hold the multiples of G that `base_multiply` looks up. -/
theorem tabulated : CombTabulated mid.p384.precomp.CURVE_GENERATOR_PRECOMP_COMB :=
  tabulated_of_ok (by decide +kernel)

end P384

end rind.x86_64
