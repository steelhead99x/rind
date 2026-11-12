import Rind.NistGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.FieldTheory.Finite.Basic

/-!
# The NIST curves' group order

Every finite point of y² = x³ - 3x + b over the integers mod a prime p has
order n, for a prime n with 2p + 1 < 3n, once the kernel checks that the cubic
x³ - 3x + b has no root mod p and that a finite G has n·G infinity. HOL Light
proves this as `P256_GROUP_ELEMENT_ORDER` from the group's size, which
Mathlib cannot count: it has no Hasse bound. The count here is elementary:

1. Each x gives at most two points, y and -y, so with infinity the group has
   at most 2p + 1 < 3n.
2. n divides the group's order, by Lagrange, since G has order n, so the
   order is n or 2n.
3. 2n is even, so by Cauchy the group would hold a point of order 2. That
   point is its own negative, so its y is 0 and its x a root of the cubic,
   which has none.
4. So the order is n, a prime, and every point but infinity has order n.
-/

namespace rind.spec.nist

/-! ## The cubic has no root

A residue mod the cubic f = x³ - 3x + b is a quadratic c₀ + c₁x + c₂x²,
a triple of numbers. A root r of f mod p would have r^p = r, by Fermat, so
q = x^p - x mod f would vanish at r, and so would any multiple of q mod f. The
kernel computes x^p mod f by squaring and multiplying, and checks that
q^(p³ - 2)·q is 1 mod f, which cannot vanish: an irreducible f makes the
residues a field of p³ elements, where q^(p³ - 2) is q's inverse. -/

/-- A residue mod the cubic, c₀ + c₁x + c₂x². -/
abbrev Residue := ℕ × ℕ × ℕ

/-- The residue's value at `r`. -/
def Residue.eval {p : ℕ} (A : Residue) (r : ZMod p) : ZMod p := A.1 + A.2.1 * r + A.2.2 * r ^ 2

/-- The product of two residues mod the cubic x³ - 3x + b and mod `p`, with
x³ as 3x - b and x⁴ as 3x² - bx. -/
def resMul (p b : ℕ) : Residue → Residue → Residue
  | (c0, c1, c2), (d0, d1, d2) =>
    let e3 := c1 * d2 + c2 * d1
    let e4 := c2 * d2
    ((c0 * d0 + (p - b % p) * e3) % p,
      (c0 * d1 + c1 * d0 + 3 * e3 + (p - b % p) * e4) % p,
      (c0 * d2 + c1 * d1 + c2 * d0 + 3 * e4) % p)

/-- The residue `A` to the power `k`, for `k < 2 ^ fuel`, by squaring and
multiplying. -/
def resPow (p b : ℕ) (A : Residue) : ℕ → ℕ → Residue
  | 0, _ => (1, 0, 0)
  | fuel + 1, k =>
    if k = 0 then (1, 0, 0)
    else
      let R := resPow p b A fuel (k / 2)
      let S := resMul p b R R
      if k % 2 = 0 then S else resMul p b S A

/-- Whether the kernel's computation shows that x³ - 3x + b has no root mod
`p`. The fuel covers P-521's p³, under 2¹⁵⁶⁴. -/
def noRoot (p b : ℕ) : Bool :=
  let h := resPow p b (0, 1, 0) 2048 p
  let q : Residue := (h.1, (h.2.1 + (p - 1)) % p, h.2.2)
  p ^ 3 < 2 ^ 2048 && resMul p b (resPow p b q 2048 (p ^ 3 - 2)) q == (1, 0, 0)

variable {p : ℕ} [Fact p.Prime]

theorem natCast_sub_mod (b : ℕ) : ((p - b % p : ℕ) : ZMod p) = -b := by
  rw [Nat.cast_sub (Nat.mod_lt _ p_pos).le, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

theorem resMul_eval {b : ℕ} {r : ZMod p} (hf : r ^ 3 - 3 * r + b = 0) (A B : Residue) :
    (resMul p b A B).eval r = A.eval r * B.eval r := by
  obtain ⟨c0, c1, c2⟩ := A
  obtain ⟨d0, d1, d2⟩ := B
  simp only [resMul, Residue.eval, ZMod.natCast_mod]
  push_cast [natCast_sub_mod]
  linear_combination (-((c1 * d2 + c2 * d1 : ZMod p) + c2 * d2 * r)) * hf

theorem resPow_eval {b : ℕ} {r : ZMod p} (hf : r ^ 3 - 3 * r + b = 0) (A : Residue) :
    ∀ fuel k, k < 2 ^ fuel → (resPow p b A fuel k).eval r = A.eval r ^ k
  | 0, k, hk => by
    obtain rfl : k = 0 := by omega
    simp [resPow, Residue.eval]
  | fuel + 1, k, hk => by
    unfold resPow
    by_cases h0 : k = 0
    · subst h0; simp [Residue.eval]
    have ih := resPow_eval hf A fuel (k / 2) (by rw [pow_succ] at hk; omega)
    simp only [h0, ↓reduceIte]
    split_ifs with h2
    · rw [resMul_eval hf, ih, ← pow_add]
      congr 1
      omega
    · rw [resMul_eval hf, resMul_eval hf, ih, ← pow_add, ← pow_succ]
      congr 1
      omega

/-- x³ - 3x + b has no root mod `p`, if `noRoot` holds. -/
theorem no_root {b : ℕ} (h : noRoot p b = true) (r : ZMod p) : r ^ 3 - 3 * r + b ≠ 0 := by
  intro hf
  simp only [noRoot, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨hp3, hc⟩ := h
  have hp : p < 2 ^ 2048 := lt_of_le_of_lt (Nat.le_self_pow (by norm_num) p) hp3
  have hx := resPow_eval hf (0, 1, 0) 2048 p hp
  simp only [Residue.eval, Nat.cast_zero, Nat.cast_one, zero_add, one_mul, zero_mul, add_zero,
    ZMod.pow_card] at hx
  set h := resPow p b (0, 1, 0) 2048 p
  set q : Residue := (h.1, (h.2.1 + (p - 1)) % p, h.2.2) with hqd
  have hq : q.eval r = 0 := by
    have e : q.eval r = h.eval r - r := by
      simp only [hqd, Residue.eval, ZMod.natCast_mod]
      push_cast [Nat.cast_sub p_pos, ZMod.natCast_self]
      ring
    rw [e, Residue.eval, hx, sub_self]
  have e : (resMul p b (resPow p b q 2048 (p ^ 3 - 2)) q).eval r = Residue.eval (1, 0, 0) r := by rw [hc]
  rw [resMul_eval hf, hq, mul_zero] at e
  simp [Residue.eval] at e

/-! ## Counting the points -/

variable [Fact (3 < p)] {b : ℕ}

omit [Fact (3 < p)] in
theorem odd_p [Fact (3 < p)] : p % 2 = 1 :=
  Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two (by have := (Fact.out : 3 < p); omega))

/-- A point as its x and which half of the field its y is in, which tells it
from the one other point with its x, -y. -/
def code : (curve p b).Point → Option (ZMod p × Bool)
  | .zero => none
  | .some x y _ => some (x, decide (y.val ≤ p / 2))

theorem code_injective : Function.Injective (code (p := p) (b := b)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rintro (_ | ⟨x1, y1, h1⟩) (_ | ⟨x2, y2, h2⟩) h
  · rfl
  · simp [code] at h
  · simp [code] at h
  simp only [code, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, hy⟩ := h
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h1.1 h2.1 rfl with rfl | hn
  · rfl
  rw [negY_eq] at hn
  subst hn
  by_cases h0 : y2 = 0
  · subst h0; simp
  exfalso
  rw [ZMod.neg_val] at hy
  simp only [h0, ↓reduceIte] at hy
  have hv : y2.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
  have := ZMod.val_lt y2
  have := odd_p (p := p)
  by_cases hc : y2.val ≤ p / 2 <;> simp [hc] at hy <;> omega

instance : Finite (curve p b).Point := Finite.of_injective _ code_injective

/-- The group has at most 2p + 1 points: infinity, and two for each x. -/
theorem card_le : Nat.card (curve p b).Point ≤ 2 * p + 1 := by
  refine (Nat.card_le_card_of_injective _ code_injective).trans (le_of_eq ?_)
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_prod, ZMod.card,
    Fintype.card_bool]
  ring

/-- No point has order 2, as its y would be 0 and its x a root of the cubic. -/
theorem addOrderOf_ne_two (hr : noRoot p b = true) (X : (curve p b).Point) : addOrderOf X ≠ 2 := by
  intro h2
  have h : X + X = 0 := by rw [← two_nsmul, ← h2, addOrderOf_nsmul_eq_zero]
  rcases X with _ | ⟨x, y, hxy⟩
  · rw [← WeierstrassCurve.Affine.Point.zero_def, addOrderOf_zero] at h2
    omega
  have hneg := eq_neg_of_add_eq_zero_left h
  rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq, negY_eq] at hneg
  have hy : y = 0 := by
    have : 2 * y = 0 := by linear_combination hneg.2
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero'
  have he := hxy.1
  rw [WeierstrassCurve.Affine.equation_iff, hy] at he
  simp only [curve, WeierstrassCurve.toAffine] at he
  exact no_root hr x (by linear_combination -he)

/-- Every point but infinity has order `n`, for a prime `n` with
2p + 1 < 3n that is the order of a point `G`, if `noRoot` holds. -/
theorem addOrderOf_eq {n : ℕ} [Fact n.Prime] (hr : noRoot p b = true) (hn : 2 * p + 1 < 3 * n)
    {G : (curve p b).Point} (hG0 : G ≠ 0) (hG : n • G = 0) {X : (curve p b).Point} (hX : X ≠ 0) :
    addOrderOf X = n := by
  have hn0 := (Fact.out : n.Prime).pos
  obtain ⟨k, hk⟩ : n ∣ Nat.card (curve p b).Point :=
    addOrderOf_eq_prime hG hG0 ▸ addOrderOf_dvd_natCard G
  have hle := card_le (p := p) (b := b)
  have hpos : 0 < Nat.card (curve p b).Point := Nat.card_pos
  have hcard : Nat.card (curve p b).Point = n := by
    have hk3 : k < 3 := by
      by_contra hk3
      have : n * 3 ≤ n * k := Nat.mul_le_mul_left n (by omega)
      omega
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    interval_cases k
    · omega
    · exfalso
      obtain ⟨Y, hY⟩ := exists_prime_addOrderOf_dvd_card' (G := (curve p b).Point) 2 ⟨n, by rw [hk]; ring⟩
      exact addOrderOf_ne_two hr Y hY
  rcases (Fact.out : n.Prime).eq_one_or_self_of_dvd _ (hcard ▸ addOrderOf_dvd_natCard X) with h | h
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hX
  · exact h

/-- Every finite point on the curve has order `n`, given what
`addOrderOf_eq` needs and a `b` other than ±2 mod p, which
`fromM_of_onCurve` needs. -/
theorem order_of_onCurve {n : ℕ} [Fact n.Prime] (hb2 : (b + 2) % p ≠ 0) (hb2' : (b + (p - 2)) % p ≠ 0)
    (hr : noRoot p b = true) (hn : 2 * p + 1 < 3 * n) {G : (curve p b).Point} (hG0 : G ≠ 0) (hG : n • G = 0)
    {P : Point} (hP : OnCurve p b P) (hP0 : P ≠ none) : OrderOf p n P := by
  rcases P with _ | ⟨x, y⟩
  · exact absurd rfl hP0
  obtain ⟨X, hX⟩ := fromM_of_onCurve hb2 hb2' hP
  rw [← hX]
  refine order_fromM X (addOrderOf_eq hr hn hG0 hG ?_)
  rintro rfl
  simp [fromM] at hX

end rind.spec.nist
