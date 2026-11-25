import Rind.NistGroup
import Rind.Pratt

/-!
# P-521's group

P-521's field prime and group order are prime, by Pratt certificates over the
primes HOL Light's `PRIME_P521` and `PRIME_N521` list, and n·G is infinity,
so G and its multiples by [1, n) have order n. `Rind.NistGroup` then gives
`p521Add` as Mathlib's group law.
-/

namespace rind.spec

namespace p521Prime

theorem prime_34110701 : Nat.Prime 34110701 :=
  prime_of_lucas 15 [(2, 2), (5, 2), (13, 1), (19, 1), (1381, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_308761441 : Nat.Prime 308761441 :=
  prime_of_lucas 17 [(2, 5), (3, 1), (5, 1), (13, 1), (49481, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_2400573761 : Nat.Prime 2400573761 :=
  prime_of_lucas 3 [(2, 6), (5, 1), (13, 1), (347, 1), (1663, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_65427463921 : Nat.Prime 65427463921 :=
  prime_of_lucas 17 [(2, 4), (3, 1), (5, 1), (7, 1), (13, 1), (2995763, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_108140989558681 : Nat.Prime 108140989558681 :=
  prime_of_lucas 17 [(2, 3), (3, 2), (5, 1), (13, 1), (683, 1), (1433, 1), (23609, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_2534364967 : Nat.Prime 2534364967 :=
  prime_of_lucas 3 [(2, 1), (3, 1), (7, 2), (8620289, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_145295143558111 : Nat.Prime 145295143558111 :=
  prime_of_lucas 7 [(2, 1), (3, 2), (5, 1), (7, 2), (13, 1), (2534364967, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_2534364967, trivial⟩

theorem prime_24098228377 : Nat.Prime 24098228377 :=
  prime_of_lucas 7 [(2, 3), (3, 1), (109, 1), (9211861, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_674750394557 : Nat.Prime 674750394557 :=
  prime_of_lucas 2 [(2, 2), (7, 1), (24098228377, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, prime_24098228377, trivial⟩

theorem prime_361725589517273017 : Nat.Prime 361725589517273017 :=
  prime_of_lucas 17 [(2, 3), (3, 1), (7, 1), (3191, 1), (674750394557, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_674750394557, trivial⟩

theorem prime_173308343918874810521923841 : Nat.Prime 173308343918874810521923841 :=
  prime_of_lucas 3 [(2, 8), (5, 1), (13, 1), (28793, 1), (361725589517273017, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_361725589517273017, trivial⟩

theorem prime_p521 : Nat.Prime p521 :=
  prime_of_lucas 3 [(2, 1), (3, 1), (5, 2), (11, 1), (17, 1), (31, 1), (41, 1), (53, 1), (131, 1), (157, 1), (521, 1), (1613, 1), (2731, 1), (8191, 1), (42641, 1), (51481, 1), (61681, 1), (409891, 1), (858001, 1), (5746001, 1), (7623851, 1), (34110701, 1), (308761441, 1), (2400573761, 1), (65427463921, 1), (108140989558681, 1), (145295143558111, 1), (173308343918874810521923841, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_34110701, prime_308761441, prime_2400573761, prime_65427463921, prime_108140989558681, prime_145295143558111, prime_173308343918874810521923841, trivial⟩

theorem prime_1458105463 : Nat.Prime 1458105463 :=
  prime_of_lucas 3 [(2, 1), (3, 5), (11, 1), (311, 1), (877, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_186406729 : Nat.Prime 186406729 :=
  prime_of_lucas 7 [(2, 3), (3, 1), (61, 1), (157, 1), (811, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_88599952463812275001 : Nat.Prime 88599952463812275001 :=
  prime_of_lucas 11 [(2, 3), (3, 1), (5, 5), (19, 1), (281, 1), (1187, 1), (186406729, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_186406729, trivial⟩

theorem prime_1647781915921980690468599 : Nat.Prime 1647781915921980690468599 :=
  prime_of_lucas 13 [(2, 1), (17, 1), (547, 1), (88599952463812275001, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_88599952463812275001, trivial⟩

theorem prime_10924559 : Nat.Prime 10924559 :=
  prime_of_lucas 7 [(2, 1), (59, 1), (92581, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_3473195323567808068309 : Nat.Prime 3473195323567808068309 :=
  prime_of_lucas 2 [(2, 2), (3, 2), (13, 1), (19, 1), (59, 1), (9227, 1), (65677, 1), (10924559, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_10924559, trivial⟩

theorem prime_144471089338257942164514676806340723 : Nat.Prime 144471089338257942164514676806340723 :=
  prime_of_lucas 11 [(2, 1), (3, 2), (11, 1), (109, 1), (14461, 1), (133279, 1), (3473195323567808068309, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_3473195323567808068309, trivial⟩

theorem prime_10577321 : Nat.Prime 10577321 :=
  prime_of_lucas 17 [(2, 3), (5, 1), (13, 1), (20341, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_101785224689 : Nat.Prime 101785224689 :=
  prime_of_lucas 3 [(2, 4), (7, 1), (131, 1), (6937379, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_43800962361397 : Nat.Prime 43800962361397 :=
  prime_of_lucas 6 [(2, 2), (3, 1), (41, 1), (10861, 1), (8196883, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_19353437 : Nat.Prime 19353437 :=
  prime_of_lucas 2 [(2, 2), (277, 1), (17467, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_60018716061994831 : Nat.Prime 60018716061994831 :=
  prime_of_lucas 7 [(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (777241, 1), (19353437, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_19353437, trivial⟩

theorem prime_4239602065187190872179 : Nat.Prime 4239602065187190872179 :=
  prime_of_lucas 2 [(2, 1), (3, 1), (61, 1), (193, 1), (60018716061994831, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_60018716061994831, trivial⟩

theorem prime_7427946019382605513260578233234962521 : Nat.Prime 7427946019382605513260578233234962521 :=
  prime_of_lucas 3 [(2, 3), (5, 1), (43800962361397, 1), (4239602065187190872179, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, prime_43800962361397, prime_4239602065187190872179, trivial⟩

theorem prime_15994076126984618329123851002118749004583184815459808099 : Nat.Prime 15994076126984618329123851002118749004583184815459808099 :=
  prime_of_lucas 2 [(2, 1), (10577321, 1), (101785224689, 1), (7427946019382605513260578233234962521, 1)]
    (by decide +kernel)
    ⟨by norm_num, prime_10577321, prime_101785224689, prime_7427946019382605513260578233234962521, trivial⟩

theorem prime_3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511 : Nat.Prime 3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511 :=
  prime_of_lucas 19 [(2, 1), (5, 1), (19, 1), (263, 1), (5449, 1), (15601, 1), (370471, 1), (144471089338257942164514676806340723, 1), (15994076126984618329123851002118749004583184815459808099, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_144471089338257942164514676806340723, prime_15994076126984618329123851002118749004583184815459808099, trivial⟩

theorem prime_3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943 : Nat.Prime 3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943 :=
  prime_of_lucas 3 [(2, 1), (3, 2), (11, 1), (31, 1), (161969, 1), (3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511, trivial⟩

theorem prime_n521 : Nat.Prime n521 :=
  prime_of_lucas 3 [(2, 3), (7, 1), (11, 1), (1283, 1), (1458105463, 1), (1647781915921980690468599, 1), (3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_1458105463, prime_1647781915921980690468599, prime_3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943, trivial⟩

end p521Prime

/-- `PRIME_P521`. -/
theorem p521_prime : Nat.Prime p521 := p521Prime.prime_p521

/-- `PRIME_N521`. -/
theorem n521_prime : Nat.Prime n521 := p521Prime.prime_n521

instance : Fact (Nat.Prime p521) := ⟨p521_prime⟩

instance : Fact (3 < p521) := ⟨by simp [p521]⟩

instance : Fact (Nat.Prime n521) := ⟨n521_prime⟩

/-- P-521's curve over `ZMod p521`. -/
abbrev p521Curve := nist.curve p521 b521

theorem b521_ne_two : (b521 + 2) % p521 ≠ 0 ∧ (b521 + (p521 - 2)) % p521 ≠ 0 := by
  simp only [b521, p521]; decide

theorem p521OnCurve_G : p521OnCurve p521G := by
  simp only [p521OnCurve, nist.OnCurve, p521G, p521, b521]; decide

theorem p521_fromM_of_onCurve {x y : Nat} (h : p521OnCurve (some (x, y))) :
    ∃ X : p521Curve.Point, nist.fromM X = some (x, y) :=
  nist.fromM_of_onCurve b521_ne_two.1 b521_ne_two.2 h

theorem p521_exists_fromM (P : nist.Point) (hP : p521OnCurve P) : ∃ X : p521Curve.Point, nist.fromM X = P := by
  match P, hP with
  | none, _ => exact ⟨0, rfl⟩
  | some (x, y), h => exact p521_fromM_of_onCurve h

/-- n·G is infinity: the kernel computes (n - 1)·G and finds -G. -/
theorem n521_nsmul_G (X : p521Curve.Point) (hX : nist.fromM X = p521G) : n521 • X = 0 := by
  obtain ⟨G, hG⟩ : ∃ G, p521G = some G := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, p521Neg p521G = some N := ⟨_, rfl⟩
  rw [hG] at hN
  have hm : nist.mulCheck p521 G 521 (n521 - 1) = some N := by
    simp only [p521Neg, nist.neg, p521G, Option.some.injEq] at hG hN
    subst hG hN
    decide +kernel
  exact nist.nsmul_G (by simp [n521]) hm hN X (hX.trans hG)

theorem p521_fromM_G : ∃ X : p521Curve.Point, nist.fromM X = p521G ∧ X ≠ 0 ∧ n521 • X = 0 := by
  obtain ⟨X, hX⟩ := p521_exists_fromM p521G p521OnCurve_G
  exact ⟨X, hX, by rintro rfl; simp [nist.fromM, p521G] at hX, n521_nsmul_G X hX⟩

/-- A multiple of G by a scalar in [1, n) has order n, as G does. -/
theorem p521_g_mult_order (d : Nat) (hd0 : 0 < d) (hd : d < n521) :
    nist.OrderOf p521 n521 (p521Pow p521G d) := by
  obtain ⟨X, hX, hX0, hn⟩ := p521_fromM_G
  rw [← hX]
  exact nist.mult_order X hX0 hn d hd0 hd

/-- A multiple of G by a scalar in [1, n) is a finite point of the curve. -/
theorem p521_g_mult (k : Nat) (hk0 : 0 < k) (hk : k < n521) :
    ∃ x y, p521Pow p521G k = some (x, y) ∧ p521OnCurve (some (x, y)) := by
  obtain ⟨X, hX, hX0, hn⟩ := p521_fromM_G
  rw [← hX]
  exact nist.mult_finite X hX0 hn k hk0 hk

end rind.spec
