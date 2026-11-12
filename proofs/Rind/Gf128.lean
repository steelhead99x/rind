module
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.ComputeDegree
public import Rind.X86_64.Simd
@[expose] public section

/-!
# GF(2^128), as rind's PCLMULQDQ code computes it

rind multiplies GHASH keys in Vale's representation, each shifted by
`shift_key_1`, with a Karatsuba carry-less product and two folds by the
reflected modulus. `powers_spec` proves the six powers `ClmulTable::powers`
computes are Vale's `gf128_power h 1` to `gf128_power h 6`: the product folds
to a Montgomery product modulo the reflected modulus (`mulModel_spec`), which,
bit-reversed, is Vale's `gf128_mul_rev` of the unshifted keys
(`mul_shiftKey1`).
-/

open Polynomial rind.simd

local notation "P" => Polynomial (ZMod 2)

namespace rind.vale

noncomputable def toPoly {n : ℕ} (x : BitVec n) : P :=
  ∑ i ∈ Finset.range n, if x.getLsbD i then X ^ i else 0

theorem coeff_toPoly {n : ℕ} (x : BitVec n) (j : ℕ) :
    (toPoly x).coeff j = if x.getLsbD j then 1 else 0 := by
  unfold toPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [apply_ite (fun p : P => p.coeff j), coeff_X_pow, coeff_zero]
  by_cases hj : j < n
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.2 hj) h
  · rw [BitVec.getLsbD_of_ge x j (by omega)]
    simp only [Bool.false_eq_true, ite_false]
    apply Finset.sum_eq_zero
    intro i hi
    have : j ≠ i := by simp at hi; omega
    simp [this]

theorem toPoly_inj {n : ℕ} {x y : BitVec n} (h : toPoly x = toPoly y) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have := congrArg (·.coeff i) h
  simp only [coeff_toPoly] at this
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all

theorem toPoly_xor {n : ℕ} (x y : BitVec n) : toPoly (x ^^^ y) = toPoly x + toPoly y := by
  ext j
  simp only [coeff_add, coeff_toPoly, BitVec.getLsbD_xor]
  cases x.getLsbD j <;> cases y.getLsbD j <;> decide

theorem toPoly_zero {n : ℕ} : toPoly (0 : BitVec n) = 0 := by
  ext j; simp [coeff_toPoly]

theorem toPoly_zero' {n : ℕ} : toPoly (0#n) = 0 := toPoly_zero

theorem toPoly_shift (a : BitVec 64) (k : ℕ) (hk : k < 64) :
    toPoly (a.setWidth 128 <<< k) = X ^ k * toPoly a := by
  ext j
  simp only [coeff_toPoly, coeff_X_pow_mul', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h1 : k ≤ j
  · simp only [h1, ite_true]
    by_cases h2 : j < 128
    · simp [h2, show ¬ j < k by omega, show j - k < 128 by omega]
    · rw [BitVec.getLsbD_of_ge a (j - k) (by omega)]; simp [h2]
  · simp [h1, show j < k by omega]

theorem toPoly_clmulAux (a b : BitVec 64) (k : ℕ) (hk : k ≤ 64) :
    toPoly (clmulAux a b k) = toPoly a * ∑ i ∈ Finset.range k, if b.getLsbD i then X ^ i else 0 := by
  induction k with
  | zero => simp [clmulAux, toPoly_zero']
  | succ k ih =>
    rw [clmulAux, toPoly_xor, ih (by omega), Finset.sum_range_succ, mul_add]
    by_cases hb : b.getLsbD k
    · simp only [hb, ite_true, toPoly_shift a k (by omega), mul_comm]
    · simp only [hb, Bool.false_eq_true, ite_false, toPoly_zero, mul_zero]

theorem toPoly_clmul (a b : BitVec 64) : toPoly (clmul a b) = toPoly a * toPoly b := by
  unfold clmul
  rw [toPoly_clmulAux a b 64 le_rfl]
  rfl

def lo (x : BitVec 128) : BitVec 64 := x.extractLsb' 0 64
def hi (x : BitVec 128) : BitVec 64 := x.extractLsb' 64 64

theorem toPoly_halves (x : BitVec 128) : toPoly x = toPoly (lo x) + X ^ 64 * toPoly (hi x) := by
  ext j
  simp only [coeff_add, coeff_toPoly, coeff_X_pow_mul', lo, hi, BitVec.getLsbD_extractLsb']
  by_cases h : j < 64
  · simp [h, show ¬ 64 ≤ j by omega]
  · simp only [h, decide_false, Bool.false_and, show 64 ≤ j by omega, ite_true,
      Bool.false_eq_true, ite_false, zero_add]
    by_cases h2 : j - 64 < 64
    · simp [h2, show 64 + (j - 64) = j by omega]
    · rw [BitVec.getLsbD_of_ge x j (by omega)]; simp [h2]

theorem lo_append (h l : BitVec 64) : lo (h ++ l) = l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [lo, BitVec.getLsbD_extractLsb', hi', decide_true, Bool.true_and, Nat.zero_add,
    BitVec.getLsbD_append, ite_true]

theorem hi_append (h l : BitVec 64) : hi (h ++ l) = h := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [hi, BitVec.getLsbD_extractLsb', hi', decide_true, Bool.true_and,
    BitVec.getLsbD_append, show ¬ 64 + i < 64 by omega, ite_false, show 64 + i - 64 = i by omega]

theorem toPoly_append (h l : BitVec 64) : toPoly (h ++ l) = toPoly l + X ^ 64 * toPoly h := by
  rw [toPoly_halves, lo_append, hi_append]

theorem lo_xor (x y : BitVec 128) : lo (x ^^^ y) = lo x ^^^ lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'; simp [lo, hi']
theorem hi_xor (x y : BitVec 128) : hi (x ^^^ y) = hi x ^^^ hi y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'; simp [hi, hi']

def swap (x : BitVec 128) : BitVec 128 := lo x ++ hi x
def c64 : BitVec 64 := 0xc200000000000000#64

def mulModel (a b : BitVec 128) : BitVec 128 :=
  let lo1 := clmul (lo a) (lo b)
  let hi1 := clmul (hi a) (hi b)
  let mi := clmul (lo (swap a ^^^ a)) (lo (swap b ^^^ b))
  let mi2 := mi ^^^ lo1 ^^^ hi1
  let mi5 := mi2 ^^^ swap lo1 ^^^ clmul c64 (lo lo1)
  hi1 ^^^ swap mi5 ^^^ clmul c64 (lo mi5)

theorem toPoly_c64 : toPoly c64 = X ^ 63 + X ^ 62 + X ^ 57 := by
  ext j
  simp only [coeff_toPoly, coeff_add, coeff_X_pow]
  by_cases h : j < 64
  · interval_cases j <;> decide
  · rw [BitVec.getLsbD_of_ge c64 j (by omega)]
    simp [show j ≠ 63 by omega, show j ≠ 62 by omega, show j ≠ 57 by omega]

theorem two_eq_zero_P : (2 : P) = 0 := CharTwo.two_eq_zero


/-- The reflected GHASH modulus, which the reduction folds by. -/
@[irreducible] noncomputable def Q : P := X ^ 128 + X ^ 127 + X ^ 126 + X ^ 121 + 1

theorem mont_alg (A B A0 A1 B0 B1 l0 l1 m0 m1 : P) (hA : A = A0 + X ^ 64 * A1)
    (hB : B = B0 + X ^ 64 * B1) (hL : A0 * B0 = l0 + X ^ 64 * l1)
    (hM : m0 + X ^ 64 * m1 = (A0 + A1) * (B0 + B1) + A0 * B0 + A1 * B1 + (l1 + X ^ 64 * l0) +
      (X ^ 63 + X ^ 62 + X ^ 57) * l0) :
    A * B + X ^ 128 * (A1 * B1 + (m1 + X ^ 64 * m0) + (X ^ 63 + X ^ 62 + X ^ 57) * m0) =
      Q * (l0 + X ^ 64 * m0) := by
  subst hA hB
  unfold Q
  linear_combination ( X ^ 64 * hM + hL + (X ^ 64 * (A0 * B1 + A1 * B0) + X ^ 128 * A1 * B1 -
    X ^ 64 * m0 + X ^ 64 * A0 * B0 + X ^ 64 * A1 * B1 + X ^ 64 * l1) * two_eq_zero_P)

theorem mulModel_spec (a b : BitVec 128) :
    ∃ S, toPoly a * toPoly b + X ^ 128 * toPoly (mulModel a b) = Q * S := by
  set lo1 := clmul (lo a) (lo b) with hlo1
  set hi1 := clmul (hi a) (hi b) with hhi1
  set mi := clmul (lo (swap a ^^^ a)) (lo (swap b ^^^ b)) with hmi
  set mi5 := mi ^^^ lo1 ^^^ hi1 ^^^ swap lo1 ^^^ clmul c64 (lo lo1) with hmi5
  rw [show mulModel a b = hi1 ^^^ swap mi5 ^^^ clmul c64 (lo mi5) from rfl]
  have hL : toPoly (lo a) * toPoly (lo b) = toPoly (lo lo1) + X ^ 64 * toPoly (hi lo1) := by
    rw [← toPoly_clmul, ← hlo1, toPoly_halves]
  have hM : toPoly (lo mi5) + X ^ 64 * toPoly (hi mi5) =
      (toPoly (lo a) + toPoly (hi a)) * (toPoly (lo b) + toPoly (hi b)) +
        toPoly (lo a) * toPoly (lo b) + toPoly (hi a) * toPoly (hi b) +
        (toPoly (hi lo1) + X ^ 64 * toPoly (lo lo1)) + (X ^ 63 + X ^ 62 + X ^ 57) * toPoly (lo lo1) := by
    rw [← toPoly_halves, hmi5, toPoly_xor, toPoly_xor, toPoly_xor, toPoly_xor, hmi, toPoly_clmul,
      lo_xor, lo_xor, swap, swap, lo_append, lo_append, toPoly_xor, toPoly_xor, hlo1, hhi1,
      toPoly_clmul, toPoly_clmul, swap, toPoly_append, toPoly_clmul, toPoly_c64]
    ring
  simp only [toPoly_xor, swap, toPoly_append, toPoly_clmul, toPoly_c64, hhi1]
  clear_value lo1 hi1 mi mi5
  have h := mont_alg (toPoly a) (toPoly b) (toPoly (lo a)) (toPoly (hi a)) (toPoly (lo b)) (toPoly (hi b))
    (toPoly (lo lo1)) (toPoly (hi lo1)) (toPoly (lo mi5)) (toPoly (hi mi5)) (toPoly_halves a) (toPoly_halves b) hL hM
  exact ⟨_, h⟩

/-! ## Coefficients -/

theorem coeff_sum_C_mul_X_pow (f : ℕ → ZMod 2) (n j : ℕ) :
    (∑ i ∈ Finset.range n, C (f i) * X ^ i).coeff j = if j < n then f j else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hj : j < n
  · rw [Finset.sum_eq_single j] <;> simp_all [eq_comm]
  · simp only [hj, ite_false]
    apply Finset.sum_eq_zero; intro i hi; simp at hi; simp [show j ≠ i by omega]

theorem coeff_reverse (a : P) (n j : ℕ) :
    (reverse a n).coeff j = if j ≤ n then a.coeff (n - j) else 0 := by
  rw [reverse, coeff_sum_C_mul_X_pow]; simp

theorem coeff_mask (a : P) (n j : ℕ) : (mask a n).coeff j = if j < n then a.coeff j else 0 :=
  coeff_sum_C_mul_X_pow _ n j

/-- A polynomial of degree below 128, as a field element is. -/
def Small (p : P) : Prop := p.natDegree ≤ 127

theorem Small.coeff {p : P} (h : Small p) {j : ℕ} (hj : 128 ≤ j) : p.coeff j = 0 :=
  natDegree_le_iff_coeff_eq_zero.1 h j (by omega)

theorem small_of_coeff {p : P} (h : ∀ j, 128 ≤ j → p.coeff j = 0) : Small p :=
  natDegree_le_iff_coeff_eq_zero.2 fun j hj => h j (by omega)

theorem small_toPoly (x : BitVec 128) : Small (toPoly x) :=
  small_of_coeff fun j hj => by rw [coeff_toPoly, BitVec.getLsbD_of_ge x j hj]; rfl

theorem small_reflect {p : P} (h : Small p) : Small (reflect 127 p) :=
  small_of_coeff fun j hj => by
    rw [coeff_reflect, revAt_eq_self_of_lt (by omega)]; exact h.coeff hj

theorem reverse_eq_reflect {p : P} (h : Small p) : reverse p 127 = reflect 127 p := by
  ext j
  rw [coeff_reverse, coeff_reflect]
  by_cases hj : j ≤ 127
  · rw [ite_eq_left hj, revAt_le hj]
  · rw [ite_eq_right hj, revAt_eq_self_of_lt (by omega), h.coeff (by omega)]

theorem small_reverse (p : P) : Small (reverse p 127) :=
  small_of_coeff fun j hj => by rw [coeff_reverse, ite_eq_right (by omega)]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

theorem coeff_low (m : ℕ) : (gf128ModulusLowTerms).coeff m =
    if m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 7 then 1 else 0 := by
  simp only [gf128ModulusLowTerms, coeff_add, coeff_one, coeff_X, coeff_X_pow]
  by_cases h0 : m = 0 <;> by_cases h1 : m = 1 <;> by_cases h2 : m = 2 <;> by_cases h7 : m = 7 <;>
    simp_all

theorem coeff_shiftKey1 (x : P) (k : ℕ) : (shiftKey1 128 gf128ModulusLowTerms x).coeff k =
    (if k < 128 ∧ k ≠ 0 then x.coeff (k - 1) else 0) +
      x.coeff 127 * if k = 0 ∨ k = 121 ∨ k = 126 ∨ k = 127 then 1 else 0 := by
  have hs : shift x 1 = X * x := by simp [shift]
  have hg : shift (X ^ 128 + gf128ModulusLowTerms) (-1) = (X ^ 128 + gf128ModulusLowTerms).divX := by
    rfl
  simp only [shiftKey1, hs, hg, coeff_add, coeff_mask]
  have hX : ∀ j, (X * x).coeff j = if j = 0 then 0 else x.coeff (j - 1) := by
    intro j; rcases j with _ | j <;> simp [coeff_X_mul]
  rw [hX 128]
  simp only [show (128 : ℕ) ≠ 0 by omega, ite_false, show 128 - 1 = 127 by rfl]
  congr 1
  · rw [hX]; by_cases hk : k < 128 <;> by_cases h0 : k = 0 <;> simp_all
  · rcases zmod2_cases (x.coeff 127) with h | h
    · simp [h]
    · simp only [h, ne_eq, one_ne_zero, not_false_eq_true, ite_true, one_mul, coeff_divX, coeff_reverse,
        coeff_add, coeff_X_pow, coeff_low]
      by_cases hk : k ≤ 127
      · simp only [hk, ite_true]
        by_cases h0 : k = 0 <;> by_cases h1 : k = 121 <;> by_cases h2 : k = 126 <;>
          by_cases h3 : k = 127 <;> simp_all
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]; rfl
      · simp only [hk, ite_false]
        rw [ite_eq_right (by omega)]

theorem coeff_reflect127 (p : P) (j : ℕ) :
    (reflect 127 p).coeff j = if j ≤ 127 then p.coeff (127 - j) else p.coeff j := by
  rw [coeff_reflect]
  by_cases h : j ≤ 127
  · rw [revAt_le h, ite_eq_left h]
  · rw [revAt_eq_self_of_lt (by omega), ite_eq_right h]

theorem coeff_modulus (j : ℕ) : gf128Modulus.coeff j =
    (if j = 128 then 1 else 0) + if j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 7 then 1 else 0 := by
  unfold gf128Modulus
  rw [coeff_add, coeff_X_pow, coeff_low]

theorem shiftKey_reflect (x : P) (hx : Small x) :
    X * reflect 127 (shiftKey1 128 gf128ModulusLowTerms x) + reflect 127 x =
      C (x.coeff 127) * gf128Modulus := by
  ext j
  rw [coeff_add, coeff_C_mul, coeff_modulus]
  rcases j with _ | j
  · simp
  · rw [coeff_X_mul, coeff_reflect127, coeff_reflect127]
    simp only [coeff_shiftKey1]
    by_cases hj : j ≤ 127
    · rw [ite_eq_left hj]
      have h128 := hx.coeff (le_refl 128)
      interval_cases j <;> rcases zmod2_cases (x.coeff 127) with h | h <;>
        simp [h, h128, CharTwo.add_self_eq_zero] <;> generalize x.coeff _ = c <;> revert c <;> decide
    · rw [ite_eq_right hj, ite_eq_right (by omega), hx.coeff (show 128 ≤ j + 1 by omega)]
      simp only [ite_false, show ¬ (j = 0 ∨ j = 121 ∨ j = 126 ∨ j = 127) by omega,
        show ¬ (j + 1 = 0 ∨ j + 1 = 1 ∨ j + 1 = 2 ∨ j + 1 = 7) by omega,
        show ¬ (j + 1 = 128) by omega]
      simp only [mul_zero, add_zero, zero_add]
      split_ifs <;> first | rfl | omega

theorem reflect_succ {p : P} {N : ℕ} (h : p.natDegree ≤ N) :
    reflect (N + 1) p = X * reflect N p := by
  ext j
  rw [coeff_reflect]
  rcases j with _ | j
  · rw [revAt_zero, coeff_X_mul_zero]
    exact natDegree_le_iff_coeff_eq_zero.1 h _ (by omega)
  · rw [coeff_X_mul, coeff_reflect]
    by_cases hj : j ≤ N
    · rw [revAt_le hj, revAt_le (by omega)]; congr 1; omega
    · rw [revAt_eq_self_of_lt (by omega), revAt_eq_self_of_lt (by omega),
        natDegree_le_iff_coeff_eq_zero.1 h _ (by omega), natDegree_le_iff_coeff_eq_zero.1 h _ (by omega)]

theorem reflect_Q : reflect 128 Q = gf128Modulus := by
  unfold Q gf128Modulus gf128ModulusLowTerms
  simp only [reflect_add, reflect_monomial, reflect_one]
  rw [revAt_le (by omega), revAt_le (by omega), revAt_le (by omega), revAt_le (by omega)]
  norm_num
  ring

theorem natDegree_Q : Q.natDegree = 128 := by
  unfold Q; compute_degree!

theorem reflect_mont (A B R : P) (hA : Small A) (hB : Small B) (hR : Small R)
    (h : ∃ S, A * B + X ^ 128 * R = Q * S) :
    gf128Modulus ∣ X * reflect 127 A * reflect 127 B + reflect 127 R := by
  obtain ⟨S, hS⟩ := h
  have hQ0 : Q ≠ 0 := by intro h0; have := natDegree_Q; rw [h0] at this; simp at this
  have hlhs : (A * B + X ^ 128 * R).natDegree ≤ 255 := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_mul_le.trans (by unfold Small at hA hB; omega)
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_X_pow]; unfold Small at hR; omega
  have hS' : Small S := by
    by_cases h0 : S = 0
    · rw [h0]; unfold Small; simp
    · rw [hS, natDegree_mul hQ0 h0, natDegree_Q] at hlhs; unfold Small; omega
  have e1 : reflect 255 (A * B) = X * (reflect 127 A * reflect 127 B) := by
    rw [show (255 : ℕ) = 254 + 1 by norm_num,
      reflect_succ ((natDegree_mul_le).trans (by unfold Small at hA hB; omega)),
      ← reflect_mul A B hA hB]
  have e2 : reflect 255 (X ^ 128 * R) = reflect 127 R := by
    have := reflect_mul (X ^ 128 : P) R (F := 128) (G := 127) (by rw [natDegree_X_pow]) hR
    rw [show (128 + 127 : ℕ) = 255 by norm_num, reflect_monomial, revAt_le le_rfl, Nat.sub_self,
      pow_zero, one_mul] at this
    exact this
  have e3 : reflect 255 (Q * S) = gf128Modulus * reflect 127 S := by
    have := reflect_mul Q S (F := 128) (G := 127) natDegree_Q.le hS'
    rw [show (128 + 127 : ℕ) = 255 by norm_num, reflect_Q] at this
    exact this
  have := congrArg (reflect 255) hS
  rw [reflect_add, e1, e2, e3] at this
  exact Dvd.intro _ (by rw [← this, mul_assoc])

theorem natDegree_modulus : gf128Modulus.natDegree = 128 := by
  unfold gf128Modulus gf128ModulusLowTerms; compute_degree!

theorem monic_modulus : gf128Modulus.Monic := by
  unfold gf128Modulus gf128ModulusLowTerms; monicity!

theorem small_mod (p : P) : Small (p %ₘ gf128Modulus) := by
  have := natDegree_modByMonic_lt p monic_modulus (by
    intro h; have := natDegree_modulus; rw [h] at this; simp at this)
  rw [natDegree_modulus] at this; unfold Small; omega

theorem small_shiftKey1 (x : P) : Small (shiftKey1 128 gf128ModulusLowTerms x) :=
  small_of_coeff fun j hj => by
    rw [coeff_shiftKey1, ite_eq_right (by omega), ite_eq_right (by omega)]; simp

/-- Two polynomials of degree below 128 that `gf128Modulus` divides the difference of are equal. -/
theorem eq_of_dvd {p q : P} (hp : Small p) (hq : Small q) (h : gf128Modulus ∣ p - q) : p = q := by
  by_contra hne
  have h0 : p - q ≠ 0 := sub_ne_zero.2 hne
  have := natDegree_le_of_dvd h h0
  rw [natDegree_modulus] at this
  have := natDegree_sub_le p q
  unfold Small at hp hq; omega

/-- rind's multiply of two shifted keys is the shifted key of Vale's product. -/
theorem mul_shiftKey1 (x y : P) (hx : Small x) (hy : Small y) (a b : BitVec 128)
    (ha : toPoly a = shiftKey1 128 gf128ModulusLowTerms x)
    (hb : toPoly b = shiftKey1 128 gf128ModulusLowTerms y) :
    toPoly (mulModel a b) = shiftKey1 128 gf128ModulusLowTerms (gf128MulRev x y) := by
  have hw : gf128MulRev x y = reflect 127 (gf128Mul (reverse x 127) (reverse y 127)) :=
    reverse_eq_reflect (small_mod _)
  have e1 := reflect_mont _ _ _ (small_toPoly a) (small_toPoly b) (small_toPoly _) (mulModel_spec a b)
  rw [ha, hb] at e1
  have e2 := dvd_trans (dvd_mul_left gf128Modulus (C (x.coeff 127))) (shiftKey_reflect x hx).symm.dvd
  have e3 := dvd_trans (dvd_mul_left gf128Modulus (C (y.coeff 127))) (shiftKey_reflect y hy).symm.dvd
  have e4 := dvd_trans (dvd_mul_left gf128Modulus (C ((gf128MulRev x y).coeff 127)))
    (shiftKey_reflect (gf128MulRev x y) (small_reverse _)).symm.dvd
  have hrw : reflect 127 (gf128MulRev x y) = gf128Mul (reverse x 127) (reverse y 127) := by
    rw [hw, reflect_reflect]
  rw [hrw] at e4
  have e5 : gf128Modulus ∣ gf128Mul (reverse x 127) (reverse y 127) - reverse x 127 * reverse y 127 := by
    have := modByMonic_add_div (reverse x 127 * reverse y 127) gf128Modulus
    exact ⟨-(reverse x 127 * reverse y 127 /ₘ gf128Modulus), by
      unfold gf128Mul; linear_combination this⟩
  rw [reverse_eq_reflect hx, reverse_eq_reflect hy] at e4 e5
  rw [← AdjoinRoot.mk_eq_zero] at e1 e2 e3 e4 e5
  simp only [map_add, map_mul, map_sub] at e1 e2 e3 e4 e5
  set m := AdjoinRoot.mk gf128Modulus
  -- X is a unit modulo the modulus.
  have hunit : m X * m (X ^ 127 + X ^ 6 + X + 1) = 1 := by
    have hp : X * (X ^ 127 + X ^ 6 + X + 1) + 1 = gf128Modulus := by
      unfold gf128Modulus gf128ModulusLowTerms; ring
    have h0 : m (X * (X ^ 127 + X ^ 6 + X + 1)) + 1 = 0 := by
      rw [← map_one m, ← map_add, hp]; exact AdjoinRoot.mk_self
    have h2 : (2 : AdjoinRoot gf128Modulus) = 0 := by
      have := congrArg m two_eq_zero_P; rw [map_zero, map_ofNat] at this; assumption
    rw [map_mul] at h0
    linear_combination h0 - h2
  have key : m (reflect 127 (shiftKey1 128 gf128ModulusLowTerms (gf128MulRev x y))) =
      m (reflect 127 (toPoly (mulModel a b))) := by
    have : m X * (m (reflect 127 (shiftKey1 128 gf128ModulusLowTerms (gf128MulRev x y))) -
        m (reflect 127 (toPoly (mulModel a b)))) = 0 := by
      linear_combination e4 - m (reflect 127 y) * e2 - e5 +
        m X * m (reflect 127 (shiftKey1 128 gf128ModulusLowTerms x)) * e3 - m X * e1
    have := congrArg (m (X ^ 127 + X ^ 6 + X + 1) * ·) this
    simp only [mul_zero, ← mul_assoc, mul_comm (m (X ^ 127 + X ^ 6 + X + 1)) (m X), hunit,
      one_mul] at this
    exact sub_eq_zero.1 this
  have key' : m (reflect 127 (shiftKey1 128 gf128ModulusLowTerms (gf128MulRev x y)) -
      reflect 127 (toPoly (mulModel a b))) = 0 := by rw [map_sub, key, sub_self]
  rw [AdjoinRoot.mk_eq_zero] at key'
  have := eq_of_dvd (small_reflect (small_shiftKey1 _)) (small_reflect (small_toPoly _)) key'
  have := congrArg (reflect 127) this
  rw [reflect_reflect, reflect_reflect] at this
  exact this.symm

theorem mod_mul_mod (p q : P) : (p %ₘ gf128Modulus * q) %ₘ gf128Modulus = (p * q) %ₘ gf128Modulus := by
  apply modByMonic_eq_of_dvd_sub monic_modulus
  have := modByMonic_add_div p gf128Modulus
  exact ⟨-(p /ₘ gf128Modulus * q), by linear_combination q * this⟩

theorem mulRev_comm (a b : P) : gf128MulRev a b = gf128MulRev b a := by
  unfold gf128MulRev gf128Mul; rw [mul_comm]

theorem reverse_mulRev (a b : P) : reverse (gf128MulRev a b) 127 =
    (reverse a 127 * reverse b 127) %ₘ gf128Modulus := by
  unfold gf128MulRev
  have hs : Small (gf128Mul (reverse a 127) (reverse b 127)) := small_mod _
  rw [reverse_eq_reflect hs, reverse_eq_reflect (small_reflect hs), reflect_reflect]
  rfl

theorem mulRev_assoc (a b c : P) :
    gf128MulRev (gf128MulRev a b) c = gf128MulRev a (gf128MulRev b c) := by
  have h1 : gf128MulRev (gf128MulRev a b) c =
      reverse ((reverse a 127 * reverse b 127 * reverse c 127) %ₘ gf128Modulus) 127 := by
    rw [gf128MulRev, reverse_mulRev, gf128Mul, mod_mul_mod]
  have h2 : gf128MulRev a (gf128MulRev b c) =
      reverse ((reverse a 127 * reverse b 127 * reverse c 127) %ₘ gf128Modulus) 127 := by
    rw [gf128MulRev, reverse_mulRev, gf128Mul, mul_comm, mod_mul_mod, mul_comm, mul_assoc]
  rw [h1, h2]

theorem small_mulRev (a b : P) : Small (gf128MulRev a b) := small_reverse _

/-- `shift_key_1` on a 128-bit value: shifted left once, with the reflected
modulus added back if the top bit fell out. -/
def skBV (h : BitVec 128) : BitVec 128 :=
  (h <<< 1) ^^^ if h.getLsbD 127 then 0xc2000000000000000000000000000001#128 else 0

theorem bool_zmod (b : Bool) : (if b = true then (1 : ZMod 2) else 0) + 1 = if b = false then 1 else 0 := by
  cases b <;> decide

theorem toPoly_skBV (h : BitVec 128) :
    toPoly (skBV h) = shiftKey1 128 gf128ModulusLowTerms (toPoly h) := by
  ext k
  simp only [coeff_shiftKey1, coeff_toPoly, skBV, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft]
  by_cases hk : k < 128
  · by_cases hb : h.getLsbD 127
    · simp only [hb, ite_true, one_mul]
      by_cases h0 : k = 0
      · subst h0; simp
      · interval_cases k <;> simp_all [bool_zmod]
    · simp only [hb, Bool.false_eq_true, ite_false, zero_mul, add_zero]
      by_cases h0 : k = 0
      · subst h0; simp
      · simp [hk, h0, show ¬ k < 1 by omega]
  · rw [BitVec.getLsbD_of_ge _ k (by omega)]
    simp only [show ¬ k < 128 by omega, decide_false, Bool.false_and, Bool.false_xor, false_and,
      ite_false, zero_add]
    rw [ite_eq_right (show ¬ (k = 0 ∨ k = 121 ∨ k = 126 ∨ k = 127) by omega)]
    simp

theorem gPower_succ (a : P) {n : ℕ} (hn : 1 ≤ n) : gPower a (n + 1) = gf128MulRev a (gPower a n) := by
  rcases n with _ | n
  · omega
  · rfl

theorem small_gPower (a : P) (ha : Small a) (n : ℕ) : Small (gPower a n) := by
  rcases n with _ | _ | n
  · unfold Small gPower; simp
  · exact ha
  · exact small_mulRev _ _

/-- rind's tree of multiplies from `h` gives Vale's `gf128_power` of `h` for 1 to 6. -/
theorem powers_spec (h : BitVec 128) :
    let h1 := skBV h
    let h2 := mulModel h1 h1
    let h3 := mulModel h2 h1
    let h4 := mulModel h2 h2
    let h5 := mulModel h4 h1
    let h6 := mulModel h4 h2
    toPoly h1 = shiftKey1 128 gf128ModulusLowTerms (gPower (toPoly h) 1) ∧
    toPoly h2 = shiftKey1 128 gf128ModulusLowTerms (gPower (toPoly h) 2) ∧
    toPoly h3 = shiftKey1 128 gf128ModulusLowTerms (gPower (toPoly h) 3) ∧
    toPoly h4 = shiftKey1 128 gf128ModulusLowTerms (gPower (toPoly h) 4) ∧
    toPoly h5 = shiftKey1 128 gf128ModulusLowTerms (gPower (toPoly h) 5) ∧
    toPoly h6 = shiftKey1 128 gf128ModulusLowTerms (gPower (toPoly h) 6) := by
  intro h1 h2 h3 h4 h5 h6
  set H := toPoly h
  have hH : Small H := small_toPoly h
  have s := small_gPower H hH
  have p1 : toPoly h1 = shiftKey1 128 gf128ModulusLowTerms (gPower H 1) := toPoly_skBV h
  have p2 : toPoly h2 = shiftKey1 128 gf128ModulusLowTerms (gPower H 2) :=
    mul_shiftKey1 _ _ (s 1) (s 1) _ _ p1 p1
  have p3 : toPoly h3 = shiftKey1 128 gf128ModulusLowTerms (gPower H 3) := by
    rw [mul_shiftKey1 _ _ (s 2) (s 1) _ _ p2 p1, gPower_succ H (by omega), mulRev_comm]; rfl
  have p4 : toPoly h4 = shiftKey1 128 gf128ModulusLowTerms (gPower H 4) := by
    rw [mul_shiftKey1 _ _ (s 2) (s 2) _ _ p2 p2]
    simp only [gPower_succ H (show 1 ≤ 3 by omega), gPower_succ H (show 1 ≤ 2 by omega),
      gPower_succ H (show 1 ≤ 1 by omega), mulRev_assoc]
    rfl
  have p5 : toPoly h5 = shiftKey1 128 gf128ModulusLowTerms (gPower H 5) := by
    rw [mul_shiftKey1 _ _ (s 4) (s 1) _ _ p4 p1, gPower_succ H (show 1 ≤ 4 by omega), mulRev_comm]
    rfl
  have p6 : toPoly h6 = shiftKey1 128 gf128ModulusLowTerms (gPower H 6) := by
    rw [mul_shiftKey1 _ _ (s 4) (s 2) _ _ p4 p2, gPower_succ H (show 1 ≤ 5 by omega),
      gPower_succ H (show 1 ≤ 4 by omega), ← mulRev_assoc, mulRev_comm]
    rfl
  exact ⟨p1, p2, p3, p4, p5, p6⟩

end rind.vale
