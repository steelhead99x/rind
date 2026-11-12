import Rind.Spec
import Rind.Pratt
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
open rind.spec

/-!
# P-256's group law

`p256Pow` is HOL Light's `group_pow p256_group`, whose laws, such as
`p256Pow P (m * n) = p256Pow (p256Pow P m) n`, rest on the group law's
associativity. That is proven here from Mathlib's group of points on a
Weierstrass curve over a field, `WeierstrassCurve.Affine.Point`, so no axiom
states it: `p256Add` is that group's addition, and `p256Pow P n` the point
`n • P`, for a point `P` on the curve.

Mathlib's group needs `ZMod p256` to be a field, so `p256` is proven prime by
a Pratt certificate, which `Rind.Pratt` checks.
-/

namespace rind.spec

/-! ## `p256` is prime -/

theorem prime_1531 : Nat.Prime 1531 :=
  prime_of_lucas 2 [(2, 1), (3, 2), (5, 1), (17, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_65537 : Nat.Prime 65537 :=
  prime_of_lucas 3 [(2, 16)] (by decide +kernel) ⟨by norm_num, trivial⟩

theorem prime_490463 : Nat.Prime 490463 :=
  prime_of_lucas 14 [(2, 1), (7, 1), (53, 1), (661, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_17449 : Nat.Prime 17449 :=
  prime_of_lucas 14 [(2, 3), (3, 1), (727, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_6700417 : Nat.Prime 6700417 :=
  prime_of_lucas 5 [(2, 7), (3, 1), (17449, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, prime_17449, trivial⟩

theorem prime_2411 : Nat.Prime 2411 :=
  prime_of_lucas 6 [(2, 1), (5, 1), (241, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_3769 : Nat.Prime 3769 :=
  prime_of_lucas 7 [(2, 3), (3, 1), (157, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_204061199 : Nat.Prime 204061199 :=
  prime_of_lucas 11 [(2, 1), (11, 1), (23, 1), (107, 1), (3769, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_3769, trivial⟩

theorem prime_34282281433 : Nat.Prime 34282281433 :=
  prime_of_lucas 17 [(2, 3), (3, 1), (7, 1), (204061199, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, prime_204061199, trivial⟩

theorem prime_3677 : Nat.Prime 3677 :=
  prime_of_lucas 2 [(2, 2), (919, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, trivial⟩

theorem prime_66417393611 : Nat.Prime 66417393611 :=
  prime_of_lucas 6 [(2, 1), (5, 1), (53, 1), (173, 1), (197, 1), (3677, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_3677, trivial⟩

theorem prime_11290956913871 : Nat.Prime 11290956913871 :=
  prime_of_lucas 13 [(2, 1), (5, 1), (17, 1), (66417393611, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, prime_66417393611, trivial⟩

theorem prime_18169 : Nat.Prime 18169 :=
  prime_of_lucas 11 [(2, 3), (3, 1), (757, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_1087 : Nat.Prime 1087 :=
  prime_of_lucas 3 [(2, 1), (3, 1), (181, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_4349 : Nat.Prime 4349 :=
  prime_of_lucas 2 [(2, 2), (1087, 1)] (by decide +kernel) ⟨by norm_num, prime_1087, trivial⟩

theorem prime_78283 : Nat.Prime 78283 :=
  prime_of_lucas 3 [(2, 1), (3, 2), (4349, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, prime_4349, trivial⟩

theorem prime_704251 : Nat.Prime 704251 :=
  prime_of_lucas 2 [(2, 1), (3, 2), (5, 3), (313, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_46076956964474543 : Nat.Prime 46076956964474543 :=
  prime_of_lucas 5 [(2, 1), (23, 1), (18169, 1), (78283, 1), (704251, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, prime_18169, prime_78283, prime_704251, trivial⟩

theorem prime_774023187263532362759620327192479577272145303 : Nat.Prime 774023187263532362759620327192479577272145303 :=
  prime_of_lucas 3 [(2, 1), (3, 2), (2411, 1), (34282281433, 1), (11290956913871, 1), (46076956964474543, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, prime_2411, prime_34282281433, prime_11290956913871, prime_46076956964474543, trivial⟩

theorem prime_835945042244614951780389953367877943453916927241 : Nat.Prime 835945042244614951780389953367877943453916927241 :=
  prime_of_lucas 11 [(2, 3), (3, 3), (5, 1), (774023187263532362759620327192479577272145303, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, prime_774023187263532362759620327192479577272145303, trivial⟩

theorem p256_prime : Nat.Prime p256 :=
  prime_of_lucas 6 [(2, 1), (3, 1), (5, 2), (17, 1), (257, 1), (641, 1), (1531, 1), (65537, 1), (490463, 1), (6700417, 1), (835945042244614951780389953367877943453916927241, 1)] (by decide +kernel) ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_1531, prime_65537, prime_490463, prime_6700417, prime_835945042244614951780389953367877943453916927241, trivial⟩

/-! ## Mathlib's group of points on P-256's curve -/

instance : Fact (Nat.Prime p256) := ⟨p256_prime⟩

/-- `p256_group`'s curve, y² = x³ - 3x + b, over `ZMod p256`. -/
def p256Curve : WeierstrassCurve.Affine (ZMod p256) :=
  ({ a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -3, a₆ := b256 } : WeierstrassCurve (ZMod p256)).toAffine

/-- A point of Mathlib's group as `P256Point` writes it. -/
def fromM : p256Curve.Point → P256Point
  | .zero => none
  | .some x y _ => some (x.val, y.val)

/-- The group law over `ZMod p256`, as `p256Add` writes it. -/
def addF (x1 y1 x2 y2 : ZMod p256) : P256Point :=
  if x1 = x2 then
    if y1 = y2 ∧ y1 ≠ 0 then
      let m := (3 * x1 ^ 2 + -3) * (2 * y1)⁻¹
      let x3 := m ^ 2 - 2 * x1
      some (x3.val, (m * (x1 - x3) - y1).val)
    else none
  else
    let m := (y2 - y1) * (x2 - x1)⁻¹
    let x3 := m ^ 2 - (x1 + x2)
    some (x3.val, (m * (x1 - x3) - y1).val)

theorem mod_val (n : ℕ) : n % p256 = (n : ZMod p256).val := (ZMod.val_natCast _ _).symm

theorem sub_val (a b : ZMod p256) : p256Sub a.val b.val = (a - b).val := by
  have hb : b.val % p256 ≤ p256 := (Nat.mod_lt _ (Fact.out : Nat.Prime p256).pos).le
  rw [p256Sub, mod_val (a.val + _), Nat.cast_add, Nat.cast_sub hb, ZMod.natCast_self, ZMod.natCast_mod]
  simp [sub_eq_add_neg]

theorem inv_val (d : ZMod p256) : p256Inv d.val = (d⁻¹).val := by
  have hd : d.val < p256 := ZMod.val_lt d
  unfold p256Inv
  split_ifs with h
  · obtain ⟨hx, hm⟩ := Classical.choose_spec h.2
    have hc : (d * ((Classical.choose h.2 : ℕ) : ZMod p256)) = 1 := by
      have := congrArg (fun n : ℕ => (n : ZMod p256)) hm
      simpa [Nat.cast_mul] using this
    rw [← (eq_inv_of_mul_eq_one_right hc), ZMod.val_natCast_of_lt hx]
  · have hd0 : d = 0 := by
      by_contra hd0
      refine h ⟨hd, (d⁻¹).val, ZMod.val_lt _, ?_⟩
      rw [← ZMod.val_mul, mul_inv_cancel₀ hd0, ZMod.val_one]
    simp [hd0]

theorem val_mul (a b : ZMod p256) : a.val * b.val % p256 = (a * b).val := (ZMod.val_mul a b).symm

theorem val_add (a b : ZMod p256) : (a.val + b.val) % p256 = (a + b).val := (ZMod.val_add a b).symm

theorem val_sq (a : ZMod p256) : a.val ^ 2 % p256 = (a ^ 2).val := by
  rw [pow_two, pow_two, val_mul]

theorem val_ofNat_mul (k : ℕ) (hk : k < p256) (a : ZMod p256) :
    k * a.val % p256 = ((k : ZMod p256) * a).val := by
  rw [← val_mul, ZMod.val_natCast_of_lt hk]

theorem val_add_neg_three (a : ZMod p256) : (a.val + (p256 - 3)) % p256 = (a + -3).val := by
  rw [mod_val, Nat.cast_add, Nat.cast_sub (by simp [p256]), ZMod.natCast_self]
  simp

theorem add_val (x1 y1 x2 y2 : ZMod p256) :
    p256Add (some (x1.val, y1.val)) (some (x2.val, y2.val)) = addF x1 y1 x2 y2 := by
  simp only [p256Add, addF, (ZMod.val_injective p256).eq_iff, ne_eq, ZMod.val_eq_zero]
  have h2 := val_ofNat_mul 2 (by simp [p256])
  have h3 := val_ofNat_mul 3 (by simp [p256])
  simp only [Nat.cast_ofNat] at h2 h3
  split_ifs <;> simp only [val_sq, h2, h3, val_add_neg_three, inv_val, val_mul, sub_val, val_add]

open WeierstrassCurve.Affine in
theorem negY_eq (x y : ZMod p256) : p256Curve.negY x y = -y := by
  simp [p256Curve]

theorem two_ne_zero' : (2 : ZMod p256) ≠ 0 := by
  rw [show (2 : ZMod p256) = ((2 : ℕ) : ZMod p256) by simp, Ne, ZMod.natCast_eq_zero_iff]
  simp [p256]

open WeierstrassCurve.Affine in
/-- `p256Add` is the addition of Mathlib's group. -/
theorem fromM_add (X Y : p256Curve.Point) : p256Add (fromM X) (fromM Y) = fromM (X + Y) := by
  rcases X with _ | ⟨x1, y1, h1⟩ <;> rcases Y with _ | ⟨x2, y2, h2⟩
  · rfl
  · rw [← Point.zero_def, zero_add]; rfl
  · rw [← Point.zero_def, add_zero]; rfl
  simp only [fromM, add_val]
  by_cases hx : x1 = x2
  · subst hx
    by_cases hy : y1 = y2 ∧ y1 ≠ 0
    · obtain ⟨rfl, hy0⟩ := hy
      have hne : y1 ≠ p256Curve.negY x1 y1 := by
        rw [negY_eq]
        intro h
        apply hy0
        have : 2 * y1 = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_left two_ne_zero'
      rw [Point.add_self_of_Y_ne hne]
      have hl : p256Curve.slope x1 x1 y1 y1 = (3 * x1 ^ 2 + -3) * (2 * y1)⁻¹ := by
        rw [slope_of_Y_ne rfl hne, negY_eq]
        simp only [p256Curve, WeierstrassCurve.toAffine]
        ring
      simp only [addF, ne_eq, hy0, not_false_eq_true, and_self, ↓reduceIte, addY, negAddY, negY_eq, hl,
        addX]
      simp only [p256Curve, WeierstrassCurve.toAffine]
      congr 3 <;> ring
    · have hy' : y1 = p256Curve.negY x1 y2 := by
        rw [negY_eq]
        rcases Y_eq_of_X_eq h1.1 h2.1 rfl with h | h
        · subst h
          simp only [ne_eq, true_and, not_not] at hy
          simp [hy]
        · rwa [negY_eq] at h
      rw [Point.add_of_Y_eq rfl hy']
      simp [addF, hy]
  · rw [Point.add_of_X_ne hx]
    have hl : p256Curve.slope x1 x2 y1 y2 = (y2 - y1) * (x2 - x1)⁻¹ := by
      rw [slope_of_X_ne hx, ← neg_sub y2, ← neg_sub x2, neg_div_neg_eq, div_eq_mul_inv]
    simp only [addF, hx, ↓reduceIte, addY, negAddY, negY_eq, hl, addX]
    simp only [p256Curve, WeierstrassCurve.toAffine]
    congr 3 <;> ring

/-- `p256Pow` is Mathlib's multiplication of a point by a number. -/
theorem p256Pow_fromM (X : p256Curve.Point) (n : ℕ) : p256Pow (fromM X) n = fromM (n • X) := by
  induction n with
  | zero => simp [p256Pow, fromM]
  | succ n ih => rw [p256Pow, ih, fromM_add, succ_nsmul']

theorem natCast_eq_iff (a b : ℕ) : (a : ZMod p256) = b ↔ a % p256 = b % p256 :=
  ZMod.natCast_eq_natCast_iff' a b p256

theorem natCast_ne_zero {a : ℕ} (h : a % p256 ≠ 0) : (a : ZMod p256) ≠ 0 := by
  rwa [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

open WeierstrassCurve.Affine in
/-- Every point on the curve is a point of Mathlib's group: none is singular,
since y = 0 and x² = 1 would put b at ±2. -/
theorem fromM_of_onCurve {x y : ℕ} (h : p256OnCurve (some (x, y))) : ∃ X, fromM X = some (x, y) := by
  obtain ⟨hx, hy, he⟩ := h
  have heq : p256Curve.Equation (x : ZMod p256) y := by
    rw [equation_iff]
    have := (natCast_eq_iff _ _).mpr he
    push_cast [Nat.cast_sub (show 3 ≤ p256 by simp [p256])] at this
    rw [ZMod.natCast_self] at this
    simp only [p256Curve, WeierstrassCurve.toAffine]
    linear_combination this
  have hns : p256Curve.Nonsingular (x : ZMod p256) y := by
    rw [nonsingular_iff]
    refine ⟨heq, ?_⟩
    by_contra hc
    simp only [p256Curve, WeierstrassCurve.toAffine, ne_eq, not_or, not_not] at hc
    obtain ⟨h3, h2⟩ := hc
    have hy0 : (y : ZMod p256) = 0 := by
      have : 2 * (y : ZMod p256) = 0 := by linear_combination h2
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero'
    have h30 : (3 : ZMod p256) ≠ 0 := by
      simpa using natCast_ne_zero (a := 3) (by simp [p256])
    have hx1 : ((x : ZMod p256) - 1) * ((x : ZMod p256) + 1) = 0 := by
      have : 3 * (((x : ZMod p256) - 1) * ((x : ZMod p256) + 1)) = 0 := by linear_combination -h3
      exact (mul_eq_zero.mp this).resolve_left h30
    rw [equation_iff, hy0] at heq
    simp only [p256Curve, WeierstrassCurve.toAffine] at heq
    rcases mul_eq_zero.mp hx1 with h1 | h1
    · have : ((b256 - 2 : ℕ) : ZMod p256) = 0 := by
        push_cast [show 2 ≤ b256 by simp [b256]]
        linear_combination (-(x : ZMod p256) ^ 2 - (x : ZMod p256) + 2) * h1 - heq
      exact natCast_ne_zero (by simp [b256, p256]) this
    · have : ((b256 + 2 : ℕ) : ZMod p256) = 0 := by
        push_cast
        linear_combination (-(x : ZMod p256) ^ 2 + (x : ZMod p256) + 2) * h1 - heq
      exact natCast_ne_zero (by simp [b256, p256]) this
  exact ⟨.some _ _ hns, by simp [fromM, ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy]⟩

/-! ## Checking a sum without inverting -/

/-- Whether `p256Add (some P) (some Q) = some R`, for coordinates below
`p256`, checked by multiplying out the slope's denominator rather than
inverting it, so the kernel can evaluate it. -/
def addOk : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → Bool
  | (x1, y1), (x2, y2), (x3, y3) =>
    x1 < p256 && y1 < p256 && x2 < p256 && y2 < p256 && x3 < p256 && y3 < p256 &&
    if x1 = x2 then
      y1 == y2 && y1 != 0 &&
      (x3 + 2 * x1) * (2 * y1) ^ 2 % p256 == (3 * x1 ^ 2 + (p256 - 3)) ^ 2 % p256 &&
      (y3 + y1) * (2 * y1) % p256 == (3 * x1 ^ 2 + (p256 - 3)) * p256Sub x1 x3 % p256
    else
      (x3 + x1 + x2) * p256Sub x2 x1 ^ 2 % p256 == p256Sub y2 y1 ^ 2 % p256 &&
      (y3 + y1) * p256Sub x2 x1 % p256 == p256Sub y2 y1 * p256Sub x1 x3 % p256

theorem sub_cast (a b : ℕ) : (p256Sub a b : ZMod p256) = a - b := by
  rw [p256Sub, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_sub (Nat.mod_lt _ (Fact.out : Nat.Prime p256).pos).le, ZMod.natCast_self, ZMod.natCast_mod]
  ring

theorem addOk_spec {P Q R : ℕ × ℕ} (h : addOk P Q R = true) : p256Add (some P) (some Q) = some R := by
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  obtain ⟨x3, y3⟩ := R
  simp only [addOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hx1, hy1⟩, hx2⟩, hy2⟩, hx3⟩, hy3⟩, h⟩ := h
  have hv : ∀ {n : ℕ}, n < p256 → (n : ZMod p256).val = n := ZMod.val_natCast_of_lt
  rw [← hv hx1, ← hv hy1, ← hv hx2, ← hv hy2, add_val, addF]
  have h30 : (3 : ZMod p256) ≠ 0 := by
    simpa using natCast_ne_zero (a := 3) (by simp [p256])
  have hp3 : ((p256 - 3 : ℕ) : ZMod p256) = -3 := by
    rw [Nat.cast_sub (by simp [p256]), ZMod.natCast_self]; simp
  split_ifs at h with hx
  · subst hx
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨rfl, hy0⟩, he1⟩, he2⟩ := h
    have hy0' : (y1 : ZMod p256) ≠ 0 := natCast_ne_zero (by rwa [Nat.mod_eq_of_lt hy1])
    have h2 : (2 : ZMod p256) ≠ 0 := two_ne_zero'
    have e1 := (natCast_eq_iff _ _).mpr he1
    have e2 := (natCast_eq_iff _ _).mpr he2
    push_cast [hp3, sub_cast] at e1 e2
    simp only [hy0', ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    have hx : (x3 : ZMod p256) =
        ((3 * (x1 : ZMod p256) ^ 2 + -3) * (2 * (y1 : ZMod p256))⁻¹) ^ 2 - 2 * x1 := by
      field_simp
      linear_combination e1
    have hy : (y3 : ZMod p256) =
        (3 * (x1 : ZMod p256) ^ 2 + -3) * (2 * (y1 : ZMod p256))⁻¹ * (x1 - x3) - y1 := by
      field_simp
      linear_combination e2
    simp only [← hx, ← hy, hv hx3, hv hy3]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨he1, he2⟩ := h
    have hx' : (x1 : ZMod p256) ≠ x2 := by
      rwa [Ne, natCast_eq_iff, Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hx2]
    have hd : (x2 : ZMod p256) - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx')
    have e1 := (natCast_eq_iff _ _).mpr he1
    have e2 := (natCast_eq_iff _ _).mpr he2
    push_cast [sub_cast] at e1 e2
    simp only [hx', ↓reduceIte]
    have hx : (x3 : ZMod p256) =
        (((y2 : ZMod p256) - y1) * ((x2 : ZMod p256) - x1)⁻¹) ^ 2 - (x1 + x2) := by
      field_simp
      linear_combination e1
    have hy : (y3 : ZMod p256) =
        ((y2 : ZMod p256) - y1) * ((x2 : ZMod p256) - x1)⁻¹ * (x1 - x3) - y1 := by
      field_simp
      linear_combination e2
    simp only [← hx, ← hy, hv hx3, hv hy3]

theorem p256OnCurve_G : p256OnCurve p256G := by
  simp only [p256OnCurve, p256G, p256, b256]; decide

end rind.spec
