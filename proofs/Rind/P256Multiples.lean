import Rind.N256Prime
import Rind.NistOrder
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.OrderOfElement

/-!
# Integer multiples of P-256's points

ECDSA verification adds signed multiples of two points in its own Rust, so its
result is u₁G + u₂Q by the group's laws, which `Rind.P256Group` proves of
`p256Add` from Mathlib's group: `P256Laws` collects those the proofs use. They
also need that a point's multiples below n are finite, `P256OrderOf`. For G,
the kernel checks that n·G is infinity, and `Rind.NistOrder` counts the
curve's points to give every other finite point order n: `p256_order`.
-/

noncomputable section

namespace rind.spec

/-- `P`'s multiples by [1, n) are finite points, as they are when its order is
n. -/
abbrev P256OrderOf : P256Point → Prop := nist.OrderOf p256 n256

/-- The facts of `p256_group` that ECDSA verification's Rust relies on: the
curve's points form an abelian group under `p256Add`, with infinity its
identity and `p256Neg` its inverse, and `p256Pow` is repeated `p256Add`.
`p256Laws` proves them. -/
structure P256Laws : Prop where
  mul_none : ∀ P, p256OnCurve P → p256Add none P = P
  mul_comm : ∀ P Q, p256OnCurve P → p256OnCurve Q → p256Add P Q = p256Add Q P
  mul_assoc : ∀ P Q R, p256OnCurve P → p256OnCurve Q → p256OnCurve R →
    p256Add (p256Add P Q) R = p256Add P (p256Add Q R)
  mul_onCurve : ∀ P Q, p256OnCurve P → p256OnCurve Q → p256OnCurve (p256Add P Q)
  mul_neg : ∀ P, p256OnCurve P → p256Add P (p256Neg P) = none
  pow_zero : ∀ P, p256Pow P 0 = none
  pow_succ : ∀ P k, p256Pow P (k + 1) = p256Add P (p256Pow P k)

theorem p256_pos : 0 < p256 := nist.p_pos

theorem p256Neg_onCurve (P : P256Point) (h : p256OnCurve P) : p256OnCurve (p256Neg P) := by
  match P, h with
  | none, _ => trivial
  | some (x, y), ⟨hx, hy, he⟩ =>
    refine ⟨hx, Nat.mod_lt _ p256_pos, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff'] at he ⊢
    push_cast at he ⊢
    rw [nist.natCast_neg_mod, neg_sq, he]

/-- `P` multiplied by the integer `z`, as `p256_group`'s `group_zpow`. -/
def p256ZPow (P : P256Point) : Int → P256Point
  | .ofNat k => p256Pow P k
  | .negSucc k => p256Neg (p256Pow P (k + 1))

/-- The curve's points. -/
abbrev P256Curve := {P : P256Point // p256OnCurve P}

/-- `a`G + `b`Q. -/
def twin (G Q : P256Point) (a b : Int) : P256Point := p256Add (p256ZPow G a) (p256ZPow Q b)

namespace P256Laws

variable (h : P256Laws)
include h

/-- The abelian group of the curve's points that `h` gives. -/
@[reducible] def group : AddCommGroup P256Curve :=
  letI : Add P256Curve := ⟨fun P Q => ⟨p256Add P.1 Q.1, h.mul_onCurve _ _ P.2 Q.2⟩⟩
  letI : Neg P256Curve := ⟨fun P => ⟨p256Neg P.1, p256Neg_onCurve _ P.2⟩⟩
  letI : Zero P256Curve := ⟨⟨none, trivial⟩⟩
  { AddGroup.ofLeftAxioms
      (fun a b c => Subtype.ext (h.mul_assoc _ _ _ a.2 b.2 c.2))
      (fun a => Subtype.ext (by change p256Add none a.1 = a.1; exact h.mul_none _ a.2))
      (fun a => Subtype.ext (by
        change p256Add (p256Neg a.1) a.1 = none
        rw [h.mul_comm _ _ (p256Neg_onCurve _ a.2) a.2]
        exact h.mul_neg _ a.2)) with
    add_comm := fun a b => Subtype.ext (h.mul_comm _ _ a.2 b.2) }

/-- `p256Pow` is the group's multiple. -/
theorem pow_eq_nsmul (P : P256Curve) (k : Nat) :
    letI := h.group
    p256Pow P.1 k = (k • P).1 := by
  let := h.group
  induction k with
  | zero => rw [h.pow_zero, zero_smul]; rfl
  | succ k ih =>
    rw [h.pow_succ, succ_nsmul, add_comm]
    exact congrArg (p256Add P.1) ih

theorem zpow_eq_zsmul (P : P256Curve) (z : Int) :
    letI := h.group
    p256ZPow P.1 z = (z • P).1 := by
  let := h.group
  cases z with
  | ofNat k => simp only [p256ZPow, Int.ofNat_eq_natCast, natCast_zsmul]; exact h.pow_eq_nsmul P k
  | negSucc k =>
    simp only [p256ZPow, negSucc_zsmul]
    exact congrArg p256Neg (h.pow_eq_nsmul P (k + 1))

theorem zpow_onCurve (P : P256Point) (hP : p256OnCurve P) (z : Int) : p256OnCurve (p256ZPow P z) := by
  rw [h.zpow_eq_zsmul ⟨P, hP⟩]; exact Subtype.property _

omit h in
theorem zpow_natCast (P : P256Point) (k : Nat) : p256ZPow P k = p256Pow P k := rfl

theorem mul_zpow (P : P256Point) (hP : p256OnCurve P) (a b : Int) :
    p256Add (p256ZPow P a) (p256ZPow P b) = p256ZPow P (a + b) := by
  let := h.group
  rw [h.zpow_eq_zsmul ⟨P, hP⟩, h.zpow_eq_zsmul ⟨P, hP⟩, h.zpow_eq_zsmul ⟨P, hP⟩, add_zsmul]
  rfl

theorem neg_zpow (P : P256Point) (hP : p256OnCurve P) (a : Int) :
    p256Neg (p256ZPow P a) = p256ZPow P (-a) := by
  let := h.group
  rw [h.zpow_eq_zsmul ⟨P, hP⟩, h.zpow_eq_zsmul ⟨P, hP⟩, neg_zsmul]
  rfl

theorem twin_zero (G Q : P256Point) (hG : p256OnCurve G) (hQ : p256OnCurve Q) :
    twin G Q 0 0 = none := by
  let := h.group
  unfold twin
  rw [h.zpow_eq_zsmul ⟨G, hG⟩, h.zpow_eq_zsmul ⟨Q, hQ⟩, zero_smul, zero_smul]
  exact h.mul_none none trivial

theorem twin_onCurve (G Q : P256Point) (hG : p256OnCurve G) (hQ : p256OnCurve Q) (a b : Int) :
    p256OnCurve (twin G Q a b) :=
  h.mul_onCurve _ _ (h.zpow_onCurve G hG a) (h.zpow_onCurve Q hQ b)

theorem twin_double (G Q : P256Point) (hG : p256OnCurve G) (hQ : p256OnCurve Q) (a b : Int) :
    p256Add (twin G Q a b) (twin G Q a b) = twin G Q (2 * a) (2 * b) := by
  let := h.group
  have e : ∀ c d, twin G Q c d = ((c • (⟨G, hG⟩ : P256Curve)) + d • (⟨Q, hQ⟩ : P256Curve)).1 := by
    intro c d
    unfold twin
    rw [h.zpow_eq_zsmul ⟨G, hG⟩, h.zpow_eq_zsmul ⟨Q, hQ⟩]
    rfl
  rw [e, e, mul_zsmul, mul_zsmul]
  change ((_ + _) + (_ + _) : P256Curve).1 = _
  congr 1
  simp only [two_zsmul]
  abel

theorem twin_add_left (G Q : P256Point) (hG : p256OnCurve G) (hQ : p256OnCurve Q) (a b d : Int) :
    p256Add (twin G Q a b) (p256ZPow G d) = twin G Q (a + d) b := by
  let := h.group
  unfold twin
  rw [h.zpow_eq_zsmul ⟨G, hG⟩, h.zpow_eq_zsmul ⟨Q, hQ⟩, h.zpow_eq_zsmul ⟨G, hG⟩,
    h.zpow_eq_zsmul ⟨G, hG⟩]
  change ((_ + _) + _ : P256Curve).1 = (_ + _ : P256Curve).1
  rw [add_zsmul]
  congr 1
  abel

theorem twin_add_right (G Q : P256Point) (hG : p256OnCurve G) (hQ : p256OnCurve Q) (a b d : Int) :
    p256Add (twin G Q a b) (p256ZPow Q d) = twin G Q a (b + d) := by
  let := h.group
  unfold twin
  rw [h.zpow_eq_zsmul ⟨G, hG⟩, h.zpow_eq_zsmul ⟨Q, hQ⟩, h.zpow_eq_zsmul ⟨Q, hQ⟩,
    h.zpow_eq_zsmul ⟨Q, hQ⟩]
  change ((_ + _) + _ : P256Curve).1 = (_ + _ : P256Curve).1
  rw [add_zsmul]
  congr 1
  abel

/-- A point's multiples are finite below its order, n. -/
theorem zpow_ne_none (P : P256Point) (hP : p256OnCurve P) (ho : P256OrderOf P) (z : Int)
    (hz0 : z ≠ 0) (hz : z.natAbs < n256) : p256ZPow P z ≠ none := by
  let := h.group
  have hpos : 0 < z.natAbs := Int.natAbs_pos.mpr hz0
  rcases Int.natAbs_eq z with hz' | hz'
  · rw [hz', P256Laws.zpow_natCast]; exact ho _ hpos hz
  · rw [hz', ← h.neg_zpow P hP, P256Laws.zpow_natCast]
    intro hn
    apply ho _ hpos hz
    change p256Pow P z.natAbs = none
    match hq : p256Pow P z.natAbs with
    | none => rfl
    | some (x, y) => rw [hq] at hn; simp [nist.neg] at hn

/-- Distinct multiples of a point are distinct when they differ by less than
its order. -/
theorem zpow_ne (P : P256Point) (hP : p256OnCurve P) (ho : P256OrderOf P) (a b : Int) (hab : a ≠ b)
    (hn : (a - b).natAbs < n256) : p256ZPow P a ≠ p256ZPow P b := by
  intro heq
  apply h.zpow_ne_none P hP ho (a - b) (sub_ne_zero.mpr hab) hn
  rw [sub_eq_add_neg, ← h.mul_zpow P hP, heq, h.mul_zpow P hP, add_neg_cancel]
  let := h.group
  rw [h.zpow_eq_zsmul ⟨P, hP⟩, zero_smul]; rfl

theorem zpow_one (P : P256Point) (hP : p256OnCurve P) : p256ZPow P 1 = P := by
  let := h.group
  rw [h.zpow_eq_zsmul ⟨P, hP⟩, one_zsmul]

end P256Laws

/-- The group's laws, proven from Mathlib's group. -/
theorem p256Laws : P256Laws where
  mul_none P _ := by cases P <;> rfl
  mul_comm P Q hP hQ := by
    obtain ⟨X, rfl⟩ := exists_fromM P hP
    obtain ⟨Y, rfl⟩ := exists_fromM Q hQ
    dsimp only [p256Add]
    rw [nist.fromM_add, nist.fromM_add, add_comm]
  mul_assoc P Q R hP hQ hR := by
    obtain ⟨X, rfl⟩ := exists_fromM P hP
    obtain ⟨Y, rfl⟩ := exists_fromM Q hQ
    obtain ⟨Z, rfl⟩ := exists_fromM R hR
    dsimp only [p256Add]
    rw [nist.fromM_add, nist.fromM_add, nist.fromM_add, nist.fromM_add, add_assoc]
  mul_onCurve P Q hP hQ := by
    obtain ⟨X, rfl⟩ := exists_fromM P hP
    obtain ⟨Y, rfl⟩ := exists_fromM Q hQ
    dsimp only [p256Add]
    rw [nist.fromM_add]; exact nist.onCurve_fromM _
  mul_neg P hP := by
    obtain ⟨X, rfl⟩ := exists_fromM P hP
    dsimp only [p256Add, p256Neg]
    rw [nist.neg_fromM, nist.fromM_add, add_neg_cancel]; rfl
  pow_zero _ := rfl
  pow_succ _ _ := rfl

/-! ## The points' order

n·G is infinity: the kernel computes (n - 1)·G and finds -G. As n is prime,
G and its multiples by [1, n) have order n, and with the count of the curve's
points, every finite point does. -/

/-- n·G is infinity. -/
theorem n256_nsmul_G (X : p256Curve.Point) (hX : nist.fromM X = p256G) : n256 • X = 0 := by
  obtain ⟨G, hG⟩ : ∃ G, p256G = some G := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, p256Neg p256G = some N := ⟨_, rfl⟩
  rw [hG] at hN
  have hm : nist.mulCheck p256 G 256 (n256 - 1) = some N := by
    simp only [p256Neg, nist.neg, p256G, Option.some.injEq] at hG hN
    subst hG hN
    decide +kernel
  exact nist.nsmul_G (by simp [n256]) hm hN X (hX.trans hG)

instance : Fact (Nat.Prime n256) := ⟨prime_n256⟩

theorem fromM_G : ∃ X : p256Curve.Point, nist.fromM X = p256G ∧ X ≠ 0 ∧ n256 • X = 0 := by
  obtain ⟨X, hX⟩ := exists_fromM p256G p256OnCurve_G
  exact ⟨X, hX, by rintro rfl; simp [nist.fromM, p256G] at hX, n256_nsmul_G X hX⟩

/-- A multiple of G by a scalar in [1, n) has order n, as G does. -/
theorem g_mult_order (d : Nat) (hd0 : 0 < d) (hd : d < n256) : P256OrderOf (p256Pow p256G d) := by
  obtain ⟨X, hX, hX0, hn⟩ := fromM_G
  rw [← hX]
  exact nist.mult_order X hX0 hn d hd0 hd

/-- A multiple of G by a scalar in [1, n) is a finite point of the curve. -/
theorem g_mult (k : Nat) (hk0 : 0 < k) (hk : k < n256) :
    ∃ x y, p256Pow p256G k = some (x, y) ∧ p256OnCurve (some (x, y)) := by
  obtain ⟨X, hX, hX0, hn⟩ := fromM_G
  rw [← hX]
  exact nist.mult_finite X hX0 hn k hk0 hk

/-- x³ - 3x + b has no root mod p, so no point has order 2. -/
theorem p256_noRoot : nist.noRoot p256 b256 = true := by
  simp only [p256, b256]; decide +kernel

/-- Every finite point of the curve has order n, HOL Light's
`P256_GROUP_ELEMENT_ORDER`,
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/nistp256.ml#L166 -/
theorem p256_order (P : P256Point) (hP : p256OnCurve P) (hP0 : P ≠ none) : P256OrderOf P := by
  obtain ⟨X, -, hX0, hn⟩ := fromM_G
  exact nist.order_of_onCurve b256_ne_two.1 b256_ne_two.2 p256_noRoot (by simp [p256, n256]) hX0 hn hP hP0

end rind.spec

end
