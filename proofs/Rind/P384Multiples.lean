import Rind.P384Group
import Rind.NistOrder
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.OrderOfElement

/-!
# Integer multiples of P-384's points

ECDSA verification adds signed multiples of two points in its own Rust, so its
result is u₁G + u₂Q by the group's laws, which `Rind.P384Group` proves of
`p384Add` from Mathlib's group: `P384Laws` collects those the proofs use. They
also need that a point's multiples below n are finite, `P384OrderOf`. For G,
the kernel checks that n·G is infinity, and `Rind.NistOrder` counts the
curve's points to give every other finite point order n: `p384_order`.
-/

noncomputable section

namespace rind.spec

/-- `P`'s multiples by [1, n) are finite points, as they are when its order is
n. -/
abbrev P384OrderOf : nist.Point → Prop := nist.OrderOf p384 n384

/-- The facts of `p384_group` that ECDSA verification's Rust relies on: the
curve's points form an abelian group under `p384Add`, with infinity its
identity and `p384Neg` its inverse, and `p384Pow` is repeated `p384Add`.
`p384Laws` proves them. -/
structure P384Laws : Prop where
  mul_none : ∀ P, p384OnCurve P → p384Add none P = P
  mul_comm : ∀ P Q, p384OnCurve P → p384OnCurve Q → p384Add P Q = p384Add Q P
  mul_assoc : ∀ P Q R, p384OnCurve P → p384OnCurve Q → p384OnCurve R →
    p384Add (p384Add P Q) R = p384Add P (p384Add Q R)
  mul_onCurve : ∀ P Q, p384OnCurve P → p384OnCurve Q → p384OnCurve (p384Add P Q)
  mul_neg : ∀ P, p384OnCurve P → p384Add P (p384Neg P) = none
  pow_zero : ∀ P, p384Pow P 0 = none
  pow_succ : ∀ P k, p384Pow P (k + 1) = p384Add P (p384Pow P k)

theorem p384_pos : 0 < p384 := nist.p_pos

theorem p384Neg_onCurve (P : nist.Point) (h : p384OnCurve P) : p384OnCurve (p384Neg P) := by
  match P, h with
  | none, _ => trivial
  | some (x, y), ⟨hx, hy, he⟩ =>
    refine ⟨hx, Nat.mod_lt _ p384_pos, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff'] at he ⊢
    push_cast at he ⊢
    rw [nist.natCast_neg_mod, neg_sq, he]

/-- `P` multiplied by the integer `z`, as `p384_group`'s `group_zpow`. -/
def p384ZPow (P : nist.Point) : Int → nist.Point
  | .ofNat k => p384Pow P k
  | .negSucc k => p384Neg (p384Pow P (k + 1))

/-- The curve's points. -/
abbrev P384Curve := {P : nist.Point // p384OnCurve P}

/-- `a`G + `b`Q. -/
def twin384 (G Q : nist.Point) (a b : Int) : nist.Point := p384Add (p384ZPow G a) (p384ZPow Q b)

namespace P384Laws

variable (h : P384Laws)
include h

/-- The abelian group of the curve's points that `h` gives. -/
@[reducible] def group : AddCommGroup P384Curve :=
  letI : Add P384Curve := ⟨fun P Q => ⟨p384Add P.1 Q.1, h.mul_onCurve _ _ P.2 Q.2⟩⟩
  letI : Neg P384Curve := ⟨fun P => ⟨p384Neg P.1, p384Neg_onCurve _ P.2⟩⟩
  letI : Zero P384Curve := ⟨⟨none, trivial⟩⟩
  { AddGroup.ofLeftAxioms
      (fun a b c => Subtype.ext (h.mul_assoc _ _ _ a.2 b.2 c.2))
      (fun a => Subtype.ext (by change p384Add none a.1 = a.1; exact h.mul_none _ a.2))
      (fun a => Subtype.ext (by
        change p384Add (p384Neg a.1) a.1 = none
        rw [h.mul_comm _ _ (p384Neg_onCurve _ a.2) a.2]
        exact h.mul_neg _ a.2)) with
    add_comm := fun a b => Subtype.ext (h.mul_comm _ _ a.2 b.2) }

/-- `p384Pow` is the group's multiple. -/
theorem pow_eq_nsmul (P : P384Curve) (k : Nat) :
    letI := h.group
    p384Pow P.1 k = (k • P).1 := by
  let := h.group
  induction k with
  | zero => rw [h.pow_zero, zero_smul]; rfl
  | succ k ih =>
    rw [h.pow_succ, succ_nsmul, add_comm]
    exact congrArg (p384Add P.1) ih

theorem zpow_eq_zsmul (P : P384Curve) (z : Int) :
    letI := h.group
    p384ZPow P.1 z = (z • P).1 := by
  let := h.group
  cases z with
  | ofNat k => simp only [p384ZPow, Int.ofNat_eq_natCast, natCast_zsmul]; exact h.pow_eq_nsmul P k
  | negSucc k =>
    simp only [p384ZPow, negSucc_zsmul]
    exact congrArg p384Neg (h.pow_eq_nsmul P (k + 1))

theorem zpow_onCurve (P : nist.Point) (hP : p384OnCurve P) (z : Int) : p384OnCurve (p384ZPow P z) := by
  rw [h.zpow_eq_zsmul ⟨P, hP⟩]; exact Subtype.property _

omit h in
theorem zpow_natCast (P : nist.Point) (k : Nat) : p384ZPow P k = p384Pow P k := rfl

theorem mul_zpow (P : nist.Point) (hP : p384OnCurve P) (a b : Int) :
    p384Add (p384ZPow P a) (p384ZPow P b) = p384ZPow P (a + b) := by
  let := h.group
  rw [h.zpow_eq_zsmul ⟨P, hP⟩, h.zpow_eq_zsmul ⟨P, hP⟩, h.zpow_eq_zsmul ⟨P, hP⟩, add_zsmul]
  rfl

theorem neg_zpow (P : nist.Point) (hP : p384OnCurve P) (a : Int) :
    p384Neg (p384ZPow P a) = p384ZPow P (-a) := by
  let := h.group
  rw [h.zpow_eq_zsmul ⟨P, hP⟩, h.zpow_eq_zsmul ⟨P, hP⟩, neg_zsmul]
  rfl

theorem twin_zero (G Q : nist.Point) (hG : p384OnCurve G) (hQ : p384OnCurve Q) :
    twin384 G Q 0 0 = none := by
  let := h.group
  unfold twin384
  rw [h.zpow_eq_zsmul ⟨G, hG⟩, h.zpow_eq_zsmul ⟨Q, hQ⟩, zero_smul, zero_smul]
  exact h.mul_none none trivial

theorem twin_onCurve (G Q : nist.Point) (hG : p384OnCurve G) (hQ : p384OnCurve Q) (a b : Int) :
    p384OnCurve (twin384 G Q a b) :=
  h.mul_onCurve _ _ (h.zpow_onCurve G hG a) (h.zpow_onCurve Q hQ b)

theorem twin_double (G Q : nist.Point) (hG : p384OnCurve G) (hQ : p384OnCurve Q) (a b : Int) :
    p384Add (twin384 G Q a b) (twin384 G Q a b) = twin384 G Q (2 * a) (2 * b) := by
  let := h.group
  have e : ∀ c d, twin384 G Q c d = ((c • (⟨G, hG⟩ : P384Curve)) + d • (⟨Q, hQ⟩ : P384Curve)).1 := by
    intro c d
    unfold twin384
    rw [h.zpow_eq_zsmul ⟨G, hG⟩, h.zpow_eq_zsmul ⟨Q, hQ⟩]
    rfl
  rw [e, e, mul_zsmul, mul_zsmul]
  change ((_ + _) + (_ + _) : P384Curve).1 = _
  congr 1
  simp only [two_zsmul]
  abel

theorem twin_add_left (G Q : nist.Point) (hG : p384OnCurve G) (hQ : p384OnCurve Q) (a b d : Int) :
    p384Add (twin384 G Q a b) (p384ZPow G d) = twin384 G Q (a + d) b := by
  let := h.group
  unfold twin384
  rw [h.zpow_eq_zsmul ⟨G, hG⟩, h.zpow_eq_zsmul ⟨Q, hQ⟩, h.zpow_eq_zsmul ⟨G, hG⟩,
    h.zpow_eq_zsmul ⟨G, hG⟩]
  change ((_ + _) + _ : P384Curve).1 = (_ + _ : P384Curve).1
  rw [add_zsmul]
  congr 1
  abel

theorem twin_add_right (G Q : nist.Point) (hG : p384OnCurve G) (hQ : p384OnCurve Q) (a b d : Int) :
    p384Add (twin384 G Q a b) (p384ZPow Q d) = twin384 G Q a (b + d) := by
  let := h.group
  unfold twin384
  rw [h.zpow_eq_zsmul ⟨G, hG⟩, h.zpow_eq_zsmul ⟨Q, hQ⟩, h.zpow_eq_zsmul ⟨Q, hQ⟩,
    h.zpow_eq_zsmul ⟨Q, hQ⟩]
  change ((_ + _) + _ : P384Curve).1 = (_ + _ : P384Curve).1
  rw [add_zsmul]
  congr 1
  abel

/-- A point's multiples are finite below its order, n. -/
theorem zpow_ne_none (P : nist.Point) (hP : p384OnCurve P) (ho : P384OrderOf P) (z : Int)
    (hz0 : z ≠ 0) (hz : z.natAbs < n384) : p384ZPow P z ≠ none := by
  let := h.group
  have hpos : 0 < z.natAbs := Int.natAbs_pos.mpr hz0
  rcases Int.natAbs_eq z with hz' | hz'
  · rw [hz', P384Laws.zpow_natCast]; exact ho _ hpos hz
  · rw [hz', ← h.neg_zpow P hP, P384Laws.zpow_natCast]
    intro hn
    apply ho _ hpos hz
    change p384Pow P z.natAbs = none
    match hq : p384Pow P z.natAbs with
    | none => rfl
    | some (x, y) => rw [hq] at hn; simp [nist.neg] at hn

/-- Distinct multiples of a point are distinct when they differ by less than
its order. -/
theorem zpow_ne (P : nist.Point) (hP : p384OnCurve P) (ho : P384OrderOf P) (a b : Int) (hab : a ≠ b)
    (hn : (a - b).natAbs < n384) : p384ZPow P a ≠ p384ZPow P b := by
  intro heq
  apply h.zpow_ne_none P hP ho (a - b) (sub_ne_zero.mpr hab) hn
  rw [sub_eq_add_neg, ← h.mul_zpow P hP, heq, h.mul_zpow P hP, add_neg_cancel]
  let := h.group
  rw [h.zpow_eq_zsmul ⟨P, hP⟩, zero_smul]; rfl

theorem zpow_one (P : nist.Point) (hP : p384OnCurve P) : p384ZPow P 1 = P := by
  let := h.group
  rw [h.zpow_eq_zsmul ⟨P, hP⟩, one_zsmul]

end P384Laws

/-- The group's laws, proven from Mathlib's group. -/
theorem p384Laws : P384Laws where
  mul_none P _ := by cases P <;> rfl
  mul_comm P Q hP hQ := by
    obtain ⟨X, rfl⟩ := p384_exists_fromM P hP
    obtain ⟨Y, rfl⟩ := p384_exists_fromM Q hQ
    dsimp only [p384Add]
    rw [nist.fromM_add, nist.fromM_add, add_comm]
  mul_assoc P Q R hP hQ hR := by
    obtain ⟨X, rfl⟩ := p384_exists_fromM P hP
    obtain ⟨Y, rfl⟩ := p384_exists_fromM Q hQ
    obtain ⟨Z, rfl⟩ := p384_exists_fromM R hR
    dsimp only [p384Add]
    rw [nist.fromM_add, nist.fromM_add, nist.fromM_add, nist.fromM_add, add_assoc]
  mul_onCurve P Q hP hQ := by
    obtain ⟨X, rfl⟩ := p384_exists_fromM P hP
    obtain ⟨Y, rfl⟩ := p384_exists_fromM Q hQ
    dsimp only [p384Add]
    rw [nist.fromM_add]; exact nist.onCurve_fromM _
  mul_neg P hP := by
    obtain ⟨X, rfl⟩ := p384_exists_fromM P hP
    dsimp only [p384Add, p384Neg]
    rw [nist.neg_fromM, nist.fromM_add, add_neg_cancel]; rfl
  pow_zero _ := rfl
  pow_succ _ _ := rfl

/-! ## The points' order

`Rind.P384Group` proves G's order n; with the count of the curve's points,
every finite point has it. -/

/-- x³ - 3x + b has no root mod p, so no point has order 2. -/
theorem p384_noRoot : nist.noRoot p384 b384 = true := by
  simp only [p384, b384]; decide +kernel

/-- Every finite point of the curve has order n, HOL Light's
`P384_GROUP_ELEMENT_ORDER`,
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/nistp384.ml#L179 -/
theorem p384_order (P : nist.Point) (hP : p384OnCurve P) (hP0 : P ≠ none) : P384OrderOf P := by
  obtain ⟨X, -, hX0, hn⟩ := p384_fromM_G
  exact nist.order_of_onCurve b384_ne_two.1 b384_ne_two.2 p384_noRoot (by simp [p384, n384]) hX0 hn hP hP0

end rind.spec

end
