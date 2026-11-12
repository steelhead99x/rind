import Rind.Nist
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Field.ZMod

/-!
# The NIST curves' group law

`nist.pow p` is HOL Light's `group_pow` on the curve y² = x³ - 3x + b over
the integers mod a prime `p`, whose laws rest on the group law's
associativity. That is proven here, once for every such curve, from Mathlib's
group of points on a Weierstrass curve over a field,
`WeierstrassCurve.Affine.Point`, so no axiom states it: `nist.add p` is that
group's addition, and `nist.pow p P n` the point `n • P`, for a point `P` on
the curve. A curve's own file proves its `p` prime, which Mathlib's group
needs, and its generator's order, by `mulCheck`.
-/

namespace rind.spec.nist

variable {p : ℕ} [Fact p.Prime]

theorem p_pos : 0 < p := (Fact.out : p.Prime).pos

omit [Fact p.Prime] in
theorem three_le [Fact (3 < p)] : 3 ≤ p := (Fact.out : 3 < p).le

/-- The curve y² = x³ - 3x + b over `ZMod p`. -/
def curve (p b : ℕ) : WeierstrassCurve.Affine (ZMod p) :=
  ({ a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -3, a₆ := b } : WeierstrassCurve (ZMod p)).toAffine

/-- A point of Mathlib's group as `Point` writes it. -/
def fromM {b : ℕ} : (curve p b).Point → Point
  | .zero => none
  | .some x y _ => some (x.val, y.val)

/-- The group law over `ZMod p`, as `add` writes it. -/
def addF (x1 y1 x2 y2 : ZMod p) : Point :=
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

theorem mod_val (n : ℕ) : n % p = (n : ZMod p).val := (ZMod.val_natCast _ _).symm

theorem sub_val (a b : ZMod p) : sub p a.val b.val = (a - b).val := by
  have hb : b.val % p ≤ p := (Nat.mod_lt _ (Fact.out : Nat.Prime p).pos).le
  rw [sub, mod_val (a.val + _), Nat.cast_add, Nat.cast_sub hb, ZMod.natCast_self, ZMod.natCast_mod]
  simp [sub_eq_add_neg]

theorem inv_val (d : ZMod p) : inv p d.val = (d⁻¹).val := by
  have hd : d.val < p := ZMod.val_lt d
  unfold inv
  split_ifs with h
  · obtain ⟨hx, hm⟩ := Classical.choose_spec h.2
    have hc : (d * ((Classical.choose h.2 : ℕ) : ZMod p)) = 1 := by
      have := congrArg (fun n : ℕ => (n : ZMod p)) hm
      simpa [Nat.cast_mul] using this
    rw [ZMod.inv_eq_of_mul_eq_one p d _ hc, ZMod.val_natCast_of_lt hx]
  · have hd0 : d = 0 := by
      by_contra hd0
      refine h ⟨hd, (d⁻¹).val, ZMod.val_lt _, ?_⟩
      rw [← ZMod.val_mul, mul_inv_cancel₀ hd0, ZMod.val_one]
    simp [hd0]

theorem val_mul (a b : ZMod p) : a.val * b.val % p = (a * b).val := (ZMod.val_mul a b).symm

theorem val_add (a b : ZMod p) : (a.val + b.val) % p = (a + b).val := (ZMod.val_add a b).symm

theorem val_sq (a : ZMod p) : a.val ^ 2 % p = (a ^ 2).val := by
  rw [pow_two, pow_two, val_mul]

theorem val_ofNat_mul (k : ℕ) (hk : k < p) (a : ZMod p) :
    k * a.val % p = ((k : ZMod p) * a).val := by
  rw [← val_mul, ZMod.val_natCast_of_lt hk]

theorem val_add_neg_three [Fact (3 < p)] (a : ZMod p) : (a.val + (p - 3)) % p = (a + -3).val := by
  rw [mod_val, Nat.cast_add, Nat.cast_sub three_le, ZMod.natCast_self]
  simp

theorem add_val [Fact (3 < p)] (x1 y1 x2 y2 : ZMod p) :
    add p (some (x1.val, y1.val)) (some (x2.val, y2.val)) = addF x1 y1 x2 y2 := by
  simp only [add, addF, (ZMod.val_injective p).eq_iff, ne_eq, ZMod.val_eq_zero]
  have h2 := val_ofNat_mul (p := p) 2 (by have := three_le (p := p); omega)
  have h3 := val_ofNat_mul (p := p) 3 (Fact.out)
  simp only [Nat.cast_ofNat] at h2 h3
  split_ifs <;> simp only [val_sq, h2, h3, val_add_neg_three, inv_val, val_mul, sub_val, val_add]

open WeierstrassCurve.Affine in
theorem negY_eq (b : ℕ) (x y : ZMod p) : (curve p b).negY x y = -y := by
  simp [curve]

theorem natCast_ne_zero' {k : ℕ} (hk0 : 0 < k) (hk : k < p) : (k : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd hk0 hd) (by omega)

theorem two_ne_zero' [Fact (3 < p)] : (2 : ZMod p) ≠ 0 := by
  simpa using natCast_ne_zero' (p := p) (k := 2) (by omega) (by have := three_le (p := p); omega)

theorem three_ne_zero' [Fact (3 < p)] : (3 : ZMod p) ≠ 0 := by
  simpa using natCast_ne_zero' (p := p) (k := 3) (by omega) Fact.out

open WeierstrassCurve.Affine in
/-- `add` is the addition of Mathlib's group. -/
theorem fromM_add [Fact (3 < p)] {b : ℕ} (X Y : (curve p b).Point) : add p (fromM X) (fromM Y) = fromM (X + Y) := by
  rcases X with _ | ⟨x1, y1, h1⟩ <;> rcases Y with _ | ⟨x2, y2, h2⟩
  · rfl
  · rw [← Point.zero_def, zero_add]; rfl
  · rw [← Point.zero_def, add_zero]; rfl
  simp only [fromM, add_val]
  by_cases hx : x1 = x2
  · subst hx
    by_cases hy : y1 = y2 ∧ y1 ≠ 0
    · obtain ⟨rfl, hy0⟩ := hy
      have hne : y1 ≠ (curve p b).negY x1 y1 := by
        rw [negY_eq]
        intro h
        apply hy0
        have : 2 * y1 = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_left two_ne_zero'
      rw [Point.add_self_of_Y_ne hne]
      have hl : (curve p b).slope x1 x1 y1 y1 = (3 * x1 ^ 2 + -3) * (2 * y1)⁻¹ := by
        rw [slope_of_Y_ne rfl hne, negY_eq]
        simp only [curve, WeierstrassCurve.toAffine]
        ring
      simp only [addF, ne_eq, hy0, not_false_eq_true, and_self, ↓reduceIte, addY, negAddY, negY_eq, hl,
        addX]
      simp only [curve, WeierstrassCurve.toAffine]
      congr 3 <;> ring
    · have hy' : y1 = (curve p b).negY x1 y2 := by
        rw [negY_eq]
        rcases Y_eq_of_X_eq h1.1 h2.1 rfl with h | h
        · subst h
          simp only [ne_eq, true_and, not_not] at hy
          simp [hy]
        · rwa [negY_eq] at h
      rw [Point.add_of_Y_eq rfl hy']
      simp [addF, hy]
  · rw [Point.add_of_X_ne hx]
    have hl : (curve p b).slope x1 x2 y1 y2 = (y2 - y1) * (x2 - x1)⁻¹ := by
      rw [slope_of_X_ne hx, ← neg_sub y2, ← neg_sub x2, neg_div_neg_eq, div_eq_mul_inv]
    simp only [addF, hx, ↓reduceIte, addY, negAddY, negY_eq, hl, addX]
    simp only [curve, WeierstrassCurve.toAffine]
    congr 3 <;> ring

/-- `pow` is Mathlib's multiplication of a point by a number. -/
theorem pow_fromM [Fact (3 < p)] {b : ℕ} (X : (curve p b).Point) (n : ℕ) : pow p (fromM X) n = fromM (n • X) := by
  induction n with
  | zero => simp [pow, fromM]
  | succ n ih => rw [pow, ih, fromM_add, succ_nsmul']

theorem natCast_eq_iff (a b : ℕ) : (a : ZMod p) = b ↔ a % p = b % p :=
  ZMod.natCast_eq_natCast_iff' a b p

theorem natCast_ne_zero {a : ℕ} (h : a % p ≠ 0) : (a : ZMod p) ≠ 0 := by
  rwa [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

open WeierstrassCurve.Affine in
/-- Every point on the curve is a point of Mathlib's group, for a `b` other
than ±2 mod p: none is singular, since y = 0 and x² = 1 would put b at ±2. -/
theorem fromM_of_onCurve [Fact (3 < p)] {b : ℕ} (hb2 : (b + 2) % p ≠ 0) (hb2' : (b + (p - 2)) % p ≠ 0) {x y : ℕ}
    (h : OnCurve p b (some (x, y))) : ∃ X : (curve p b).Point, fromM X = some (x, y) := by
  obtain ⟨hx, hy, he⟩ := h
  have heq : (curve p b).Equation (x : ZMod p) y := by
    rw [equation_iff]
    have := (natCast_eq_iff _ _).mpr he
    push_cast [Nat.cast_sub (three_le (p := p))] at this
    rw [ZMod.natCast_self] at this
    simp only [curve, WeierstrassCurve.toAffine]
    linear_combination this
  have hns : (curve p b).Nonsingular (x : ZMod p) y := by
    rw [nonsingular_iff]
    refine ⟨heq, ?_⟩
    by_contra hc
    simp only [curve, WeierstrassCurve.toAffine, ne_eq, not_or, not_not] at hc
    obtain ⟨h3, h2⟩ := hc
    have hy0 : (y : ZMod p) = 0 := by
      have : 2 * (y : ZMod p) = 0 := by linear_combination h2
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero'
    have hx1 : ((x : ZMod p) - 1) * ((x : ZMod p) + 1) = 0 := by
      have : 3 * (((x : ZMod p) - 1) * ((x : ZMod p) + 1)) = 0 := by linear_combination -h3
      exact (mul_eq_zero.mp this).resolve_left three_ne_zero'
    rw [equation_iff, hy0] at heq
    simp only [curve, WeierstrassCurve.toAffine] at heq
    have hp2 : 2 ≤ p := by have := three_le (p := p); omega
    rcases mul_eq_zero.mp hx1 with h1 | h1
    · have : ((b + (p - 2) : ℕ) : ZMod p) = 0 := by
        push_cast [Nat.cast_sub hp2]
        rw [ZMod.natCast_self]
        linear_combination (-(x : ZMod p) ^ 2 - (x : ZMod p) + 2) * h1 - heq
      exact natCast_ne_zero hb2' this
    · have : ((b + 2 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination (-(x : ZMod p) ^ 2 + (x : ZMod p) + 2) * h1 - heq
      exact natCast_ne_zero hb2 this
  exact ⟨.some _ _ hns, by simp [fromM, ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy]⟩

/-! ## Checking a sum without inverting -/

/-- Whether `add p (some P) (some Q) = some R`, for coordinates below `p`,
checked by multiplying out the slope's denominator rather than inverting it,
so the kernel can evaluate it. -/
def addOk (p : ℕ) : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → Bool
  | (x1, y1), (x2, y2), (x3, y3) =>
    x1 < p && y1 < p && x2 < p && y2 < p && x3 < p && y3 < p &&
    if x1 = x2 then
      y1 == y2 && y1 != 0 &&
      (x3 + 2 * x1) * (2 * y1) ^ 2 % p == (3 * x1 ^ 2 + (p - 3)) ^ 2 % p &&
      (y3 + y1) * (2 * y1) % p == (3 * x1 ^ 2 + (p - 3)) * sub p x1 x3 % p
    else
      (x3 + x1 + x2) * sub p x2 x1 ^ 2 % p == sub p y2 y1 ^ 2 % p &&
      (y3 + y1) * sub p x2 x1 % p == sub p y2 y1 * sub p x1 x3 % p

theorem sub_cast (a b : ℕ) : (sub p a b : ZMod p) = a - b := by
  rw [sub, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_sub (Nat.mod_lt _ (Fact.out : Nat.Prime p).pos).le, ZMod.natCast_self, ZMod.natCast_mod]
  ring

theorem addOk_spec [Fact (3 < p)] {P Q R : ℕ × ℕ} (h : addOk p P Q R = true) : add p (some P) (some Q) = some R := by
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  obtain ⟨x3, y3⟩ := R
  simp only [addOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hx1, hy1⟩, hx2⟩, hy2⟩, hx3⟩, hy3⟩, h⟩ := h
  have hv : ∀ {n : ℕ}, n < p → (n : ZMod p).val = n := ZMod.val_natCast_of_lt
  rw [← hv hx1, ← hv hy1, ← hv hx2, ← hv hy2, add_val, addF]
  have hp3 : ((p - 3 : ℕ) : ZMod p) = -3 := by
    rw [Nat.cast_sub three_le, ZMod.natCast_self]; simp
  split_ifs at h with hx
  · subst hx
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨rfl, hy0⟩, he1⟩, he2⟩ := h
    have hy0' : (y1 : ZMod p) ≠ 0 := natCast_ne_zero (by rwa [Nat.mod_eq_of_lt hy1])
    have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero'
    have e1 := (natCast_eq_iff _ _).mpr he1
    have e2 := (natCast_eq_iff _ _).mpr he2
    push_cast [hp3, sub_cast] at e1 e2
    simp only [hy0', ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    have hx : (x3 : ZMod p) =
        ((3 * (x1 : ZMod p) ^ 2 + -3) * (2 * (y1 : ZMod p))⁻¹) ^ 2 - 2 * x1 := by
      field_simp
      linear_combination e1
    have hy : (y3 : ZMod p) =
        (3 * (x1 : ZMod p) ^ 2 + -3) * (2 * (y1 : ZMod p))⁻¹ * (x1 - x3) - y1 := by
      field_simp
      linear_combination e2
    simp only [← hx, ← hy, hv hx3, hv hy3]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨he1, he2⟩ := h
    have hx' : (x1 : ZMod p) ≠ x2 := by
      rwa [Ne, natCast_eq_iff, Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hx2]
    have hd : (x2 : ZMod p) - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx')
    have e1 := (natCast_eq_iff _ _).mpr he1
    have e2 := (natCast_eq_iff _ _).mpr he2
    push_cast [sub_cast] at e1 e2
    simp only [hx', ↓reduceIte]
    have hx : (x3 : ZMod p) =
        (((y2 : ZMod p) - y1) * ((x2 : ZMod p) - x1)⁻¹) ^ 2 - (x1 + x2) := by
      field_simp
      linear_combination e1
    have hy : (y3 : ZMod p) =
        ((y2 : ZMod p) - y1) * ((x2 : ZMod p) - x1)⁻¹ * (x1 - x3) - y1 := by
      field_simp
      linear_combination e2
    simp only [← hx, ← hy, hv hx3, hv hy3]

/-! ## The curve's points are the group's -/

theorem natCast_neg_mod (y : ℕ) : (((p - y % p) % p : ℕ) : ZMod p) = -(y : ZMod p) := by
  have hy : y % p < p := Nat.mod_lt _ p_pos
  rw [ZMod.natCast_mod, Nat.cast_sub hy.le, ZMod.natCast_self, zero_sub, ZMod.natCast_mod]

theorem onCurve_fromM [Fact (3 < p)] {b : ℕ} (X : (curve p b).Point) : OnCurve p b (fromM X) := by
  match X with
  | .zero => trivial
  | .some x y h =>
    refine ⟨ZMod.val_lt x, ZMod.val_lt y, ?_⟩
    have he := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at he
    simp only [curve, WeierstrassCurve.toAffine] at he
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast [Nat.cast_sub (three_le (p := p))]
    rw [ZMod.natCast_self, ZMod.natCast_val, ZMod.natCast_val]
    simp only [ZMod.cast_id', id]
    linear_combination he

theorem neg_fromM {b : ℕ} (X : (curve p b).Point) : neg p (fromM X) = fromM (-X) := by
  match X with
  | .zero => rfl
  | .some x y h =>
    simp only [fromM, WeierstrassCurve.Affine.Point.neg_some, neg, negY_eq, Option.some.injEq,
      Prod.mk.injEq, true_and]
    have h1 := natCast_neg_mod (p := p) y.val
    rw [ZMod.natCast_val, ZMod.cast_id', id] at h1
    rw [← h1, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.mod_lt _ p_pos)]

omit [Fact p.Prime] in
theorem eq_zero_of_fromM {b : ℕ} {X : (curve p b).Point} (h : fromM X = none) : X = 0 := by
  cases X with
  | zero => rfl
  | some => simp [fromM] at h

/-! ## A generator's order

The kernel computes (n - 1)·G by doubling and adding, checking each sum with
`addOk`, and finds -G, so n·G is infinity. For a prime n, G and its multiples
by [1, n) then have order n. -/

/-- `a`'s inverse mod `p`, by the extended Euclidean algorithm: each `r` is its
`s` times `a`, mod `p`. -/
def invEuclid (p : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, s0, _ => s0
  | fuel + 1, r0, r1, s0, s1 =>
    if r1 = 0 then s0 else invEuclid p fuel r1 (r0 % r1) s1 (sub p s0 (r0 / r1 * s1 % p))

/-- The sum of two points by the group law's formulas. `mulCheck` checks each
sum with `addOk`, so nothing relies on this being right. -/
def addEuclid (p : ℕ) : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
  | (x1, y1), (x2, y2) =>
    let m := if x1 = x2 then (3 * x1 ^ 2 + (p - 3)) * invEuclid p 1100 (2 * y1 % p) p 1 0 % p
      else sub p y2 y1 * invEuclid p 1100 (sub p x2 x1) p 1 0 % p
    let x3 := sub p (m ^ 2 % p) ((x1 + x2) % p)
    (x3, sub p (m * sub p x1 x3 % p) y1)

/-- `k` times the point `P`, for `k < 2 ^ fuel`, by doubling and adding, or
`none` if `addOk` refuses a sum. -/
def mulCheck (p : ℕ) (P : ℕ × ℕ) : ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _ => none
  | fuel + 1, k =>
    if k = 1 then some P
    else match mulCheck p P fuel (k / 2) with
      | none => none
      | some Q =>
        let D := addEuclid p Q Q
        if addOk p Q Q D then
          if k % 2 = 0 then some D
          else
            let S := addEuclid p D P
            if addOk p D P S then some S else none
        else none

theorem mulCheck_spec [Fact (3 < p)] {b : ℕ} (X : (curve p b).Point) (P : ℕ × ℕ) (hP : fromM X = some P) :
    ∀ fuel k R, mulCheck p P fuel k = some R → fromM (k • X) = some R
  | 0, _, _, h => by simp [mulCheck] at h
  | fuel + 1, k, R, h => by
    unfold mulCheck at h
    by_cases h1 : k = 1
    · simp only [h1, ↓reduceIte, Option.some.injEq] at h
      subst h h1
      rwa [one_nsmul]
    simp only [h1, ↓reduceIte] at h
    rcases hq : mulCheck p P fuel (k / 2) with _ | Q
    · simp [hq] at h
    have ih := mulCheck_spec X P hP fuel _ _ hq
    simp only [hq] at h
    by_cases hD : addOk p Q Q (addEuclid p Q Q) = true
    swap
    · simp [hD] at h
    by_cases h2 : k % 2 = 0
    · simp only [hD, h2, ↓reduceIte, Option.some.injEq] at h
      subst h
      rw [show k = k / 2 + k / 2 by omega, add_nsmul, ← fromM_add, ih]
      exact addOk_spec hD
    by_cases hS : addOk p (addEuclid p Q Q) P (addEuclid p (addEuclid p Q Q) P) = true
    · simp only [hD, h2, hS, ↓reduceIte, Option.some.injEq] at h
      subst h
      rw [show k = k / 2 + k / 2 + 1 by omega, add_nsmul, add_nsmul, one_nsmul, ← fromM_add, ← fromM_add, ih,
        addOk_spec hD, hP]
      exact addOk_spec hS
    · simp [hD, h2, hS] at h

/-- `P`'s multiples by [1, n) are finite points, as they are when its order is
n. -/
def OrderOf (p n : ℕ) (P : Point) : Prop := ∀ k, 0 < k → k < n → pow p P k ≠ none

/-- n·G is infinity, given `mulCheck`'s (n - 1)·G as -G. -/
theorem nsmul_G [Fact (3 < p)] {b n : ℕ} (hn : 1 ≤ n) {G N : ℕ × ℕ} {fuel : ℕ} (hm : mulCheck p G fuel (n - 1) = some N)
    (hN : neg p (some G) = some N) (X : (curve p b).Point) (hX : fromM X = some G) : n • X = 0 := by
  have h := mulCheck_spec X G hX fuel _ _ hm
  rw [← hN, ← hX, neg_fromM] at h
  apply eq_zero_of_fromM
  rw [show n = (n - 1) + 1 by omega, add_nsmul, one_nsmul, ← fromM_add, h, fromM_add, neg_add_cancel]
  rfl

theorem order_fromM [Fact (3 < p)] {b n : ℕ} (X : (curve p b).Point) (h : addOrderOf X = n) : OrderOf p n (fromM X) := by
  intro k hk0 hk hm
  rw [pow_fromM] at hm
  exact nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [h]; exact hk) (eq_zero_of_fromM hm)

/-- For a prime n, if n·G is infinity for a finite G, then G's multiples by
[1, n) have order n. -/
theorem mult_order [Fact (3 < p)] {b n : ℕ} [Fact n.Prime] (X : (curve p b).Point) (hX0 : X ≠ 0) (hn : n • X = 0)
    (d : ℕ) (hd0 : 0 < d) (hd : d < n) : OrderOf p n (pow p (fromM X) d) := by
  have hG : addOrderOf X = n := addOrderOf_eq_prime hn hX0
  rw [pow_fromM]
  refine order_fromM _ (addOrderOf_eq_prime (by rw [smul_comm, hn, nsmul_zero]) ?_)
  exact nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hG]; exact hd)

/-- For a prime n, if n·G is infinity for a finite G, then G's multiples by
[1, n) are finite points of the curve. -/
theorem mult_finite [Fact (3 < p)] {b n : ℕ} [Fact n.Prime] (X : (curve p b).Point) (hX0 : X ≠ 0) (hn : n • X = 0)
    (k : ℕ) (hk0 : 0 < k) (hk : k < n) :
    ∃ x y, pow p (fromM X) k = some (x, y) ∧ OnCurve p b (some (x, y)) := by
  have hG : addOrderOf X = n := addOrderOf_eq_prime hn hX0
  rcases hm : pow p (fromM X) k with _ | ⟨x, y⟩
  · exact absurd hm (order_fromM X hG k hk0 hk)
  · refine ⟨x, y, rfl, ?_⟩
    rw [← hm, pow_fromM]
    exact onCurve_fromM _

end rind.spec.nist
