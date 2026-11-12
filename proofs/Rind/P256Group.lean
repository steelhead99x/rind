import Rind.NistGroup
import Rind.Pratt
open rind.spec

/-!
# P-256's group law

`p256Pow` is HOL Light's `group_pow p256_group`, whose laws, such as
`p256Pow P (m * n) = p256Pow (p256Pow P m) n`, rest on the group law's
associativity. `Rind.NistGroup` proves them from Mathlib's group of points on
a Weierstrass curve over a field, `WeierstrassCurve.Affine.Point`, so no axiom
states them: `p256Add` is that group's addition, and `p256Pow P n` the point
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

instance : Fact (3 < p256) := ⟨by simp [p256]⟩

/-- `p256_group`'s curve, y² = x³ - 3x + b, over `ZMod p256`. -/
abbrev p256Curve := nist.curve p256 b256

theorem b256_ne_two : (b256 + 2) % p256 ≠ 0 ∧ (b256 + (p256 - 2)) % p256 ≠ 0 := by
  simp only [b256, p256]; decide

theorem p256OnCurve_G : p256OnCurve p256G := by
  simp only [p256OnCurve, nist.OnCurve, p256G, p256, b256]; decide

/-- Every point on the curve is a point of Mathlib's group. -/
theorem fromM_of_onCurve {x y : Nat} (h : p256OnCurve (some (x, y))) :
    ∃ X : p256Curve.Point, nist.fromM X = some (x, y) :=
  nist.fromM_of_onCurve b256_ne_two.1 b256_ne_two.2 h

theorem exists_fromM (P : P256Point) (hP : p256OnCurve P) : ∃ X : p256Curve.Point, nist.fromM X = P := by
  match P, hP with
  | none, _ => exact ⟨0, rfl⟩
  | some (x, y), h => exact fromM_of_onCurve h

end rind.spec
