import Rind.NistGroup
import Rind.Pratt

/-!
# P-384's group

P-384's field prime and group order are prime, by Pratt certificates over the
primes HOL Light's `PRIME_P384` and `PRIME_N384` list, and n·G is infinity,
so G and its multiples by [1, n) have order n. `Rind.NistGroup` then gives
`p384Add` as Mathlib's group law.
-/

namespace rind.spec

namespace p384Prime

theorem prime_2862218959 : Nat.Prime 2862218959 :=
  prime_of_lucas 3 [(2, 1), (3, 1), (157, 1), (1373, 1), (2213, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_807145746439 : Nat.Prime 807145746439 :=
  prime_of_lucas 3 [(2, 1), (3, 1), (47, 1), (2862218959, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_2862218959, trivial⟩

theorem prime_513928823 : Nat.Prime 513928823 :=
  prime_of_lucas 5 [(2, 1), (11, 1), (59, 1), (599, 1), (661, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_53448597593 : Nat.Prime 53448597593 :=
  prime_of_lucas 3 [(2, 3), (13, 1), (513928823, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, prime_513928823, trivial⟩

theorem prime_1357291859799823621 : Nat.Prime 1357291859799823621 :=
  prime_of_lucas 2 [(2, 2), (3, 1), (5, 1), (67, 1), (6317, 1), (53448597593, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_53448597593, trivial⟩

theorem prime_105957871 : Nat.Prime 105957871 :=
  prime_of_lucas 3 [(2, 1), (3, 1), (5, 1), (19, 1), (211, 1), (881, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_246608641 : Nat.Prime 246608641 :=
  prime_of_lucas 19 [(2, 8), (3, 2), (5, 1), (21407, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_529709925838459440593 : Nat.Prime 529709925838459440593 :=
  prime_of_lucas 3 [(2, 4), (7, 1), (181, 1), (105957871, 1), (246608641, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_105957871, prime_246608641, trivial⟩

theorem prime_532247449 : Nat.Prime 532247449 :=
  prime_of_lucas 7 [(2, 3), (3, 1), (61, 1), (363557, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_44925942675193 : Nat.Prime 44925942675193 :=
  prime_of_lucas 5 [(2, 3), (3, 1), (3517, 1), (532247449, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_532247449, trivial⟩

theorem prime_35581458644053887931343 : Nat.Prime 35581458644053887931343 :=
  prime_of_lucas 5 [(2, 1), (17, 1), (41, 1), (568151, 1), (44925942675193, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_44925942675193, trivial⟩

theorem prime_23964610537191310276190549303 : Nat.Prime 23964610537191310276190549303 :=
  prime_of_lucas 5 [(2, 1), (336757, 1), (35581458644053887931343, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, prime_35581458644053887931343, trivial⟩

theorem prime_862725979338887169942859774909 : Nat.Prime 862725979338887169942859774909 :=
  prime_of_lucas 2 [(2, 2), (3, 2), (23964610537191310276190549303, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, prime_23964610537191310276190549303, trivial⟩

theorem prime_20705423504133292078628634597817 : Nat.Prime 20705423504133292078628634597817 :=
  prime_of_lucas 5 [(2, 3), (3, 1), (862725979338887169942859774909, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, prime_862725979338887169942859774909, trivial⟩

theorem prime_413244619895455989650825325680172591660047 : Nat.Prime 413244619895455989650825325680172591660047 :=
  prime_of_lucas 5 [(2, 1), (17, 1), (97, 1), (6051631, 1), (20705423504133292078628634597817, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_20705423504133292078628634597817, trivial⟩

theorem prime_12397338596863679689524759770405177749801411 : Nat.Prime 12397338596863679689524759770405177749801411 :=
  prime_of_lucas 2 [(2, 1), (3, 1), (5, 1), (413244619895455989650825325680172591660047, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_413244619895455989650825325680172591660047, trivial⟩

theorem prime_19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 : Nat.Prime 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 :=
  prime_of_lucas 3 [(2, 4), (11, 3), (8389, 1), (38557, 1), (312289, 1), (1357291859799823621, 1), (529709925838459440593, 1), (12397338596863679689524759770405177749801411, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_1357291859799823621, prime_529709925838459440593, prime_12397338596863679689524759770405177749801411, trivial⟩

theorem prime_p384 : Nat.Prime p384 :=
  prime_of_lucas 19 [(2, 1), (19, 1), (67, 1), (807145746439, 1), (19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_807145746439, prime_19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097, trivial⟩

theorem prime_154950581 : Nat.Prime 154950581 :=
  prime_of_lucas 2 [(2, 2), (5, 1), (17, 1), (455737, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_290064143 : Nat.Prime 290064143 :=
  prime_of_lucas 5 [(2, 1), (79, 1), (491, 1), (3739, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_120699720968197491947347 : Nat.Prime 120699720968197491947347 :=
  prime_of_lucas 3 [(2, 1), (3, 1), (13, 1), (34429, 1), (154950581, 1), (290064143, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_154950581, prime_290064143, trivial⟩

theorem prime_1124679999981664229965379347 : Nat.Prime 1124679999981664229965379347 :=
  prime_of_lucas 2 [(2, 1), (3, 1), (1553, 1), (120699720968197491947347, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_120699720968197491947347, trivial⟩

theorem prime_1436833069313 : Nat.Prime 1436833069313 :=
  prime_of_lucas 3 [(2, 8), (16979, 1), (330563, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_37344768852931 : Nat.Prime 37344768852931 :=
  prime_of_lucas 3 [(2, 1), (3, 1), (5, 1), (7, 1), (11, 2), (149, 1), (9863677, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_55942463741690639 : Nat.Prime 55942463741690639 :=
  prime_of_lucas 7 [(2, 1), (7, 1), (107, 1), (37344768852931, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_37344768852931, trivial⟩

theorem prime_272109983 : Nat.Prime 272109983 :=
  prime_of_lucas 5 [(2, 1), (19, 1), (73, 1), (233, 1), (421, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_228572385721 : Nat.Prime 228572385721 :=
  prime_of_lucas 23 [(2, 3), (3, 1), (5, 1), (7, 1), (272109983, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_272109983, trivial⟩

theorem prime_23314383343543 : Nat.Prime 23314383343543 :=
  prime_of_lucas 3 [(2, 1), (3, 1), (17, 1), (228572385721, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_228572385721, trivial⟩

theorem prime_426632512014427833817 : Nat.Prime 426632512014427833817 :=
  prime_of_lucas 11 [(2, 3), (3, 1), (13, 1), (89, 1), (659, 1), (23314383343543, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_23314383343543, trivial⟩

theorem prime_1495199339761412565498084319 : Nat.Prime 1495199339761412565498084319 :=
  prime_of_lucas 6 [(2, 1), (3, 3), (64901, 1), (426632512014427833817, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_426632512014427833817, trivial⟩

theorem prime_17942392077136950785977011829 : Nat.Prime 17942392077136950785977011829 :=
  prime_of_lucas 6 [(2, 2), (3, 1), (1495199339761412565498084319, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, prime_1495199339761412565498084319, trivial⟩

theorem prime_1059392654943455286185473617842338478315215895509773412096307 : Nat.Prime 1059392654943455286185473617842338478315215895509773412096307 :=
  prime_of_lucas 2 [(2, 1), (251, 1), (248431, 1), (8463023, 1), (55942463741690639, 1), (17942392077136950785977011829, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_55942463741690639, prime_17942392077136950785977011829, trivial⟩

theorem prime_3055465788140352002733946906144561090641249606160407884365391979704929268480326390471 : Nat.Prime 3055465788140352002733946906144561090641249606160407884365391979704929268480326390471 :=
  prime_of_lucas 12 [(2, 1), (3, 1), (5, 1), (151, 1), (347, 1), (1276987, 1), (1436833069313, 1), (1059392654943455286185473617842338478315215895509773412096307, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_1436833069313, prime_1059392654943455286185473617842338478315215895509773412096307, trivial⟩

theorem prime_n384 : Nat.Prime n384 :=
  prime_of_lucas 2 [(2, 1), (3, 2), (7, 2), (13, 1), (1124679999981664229965379347, 1), (3055465788140352002733946906144561090641249606160407884365391979704929268480326390471, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_1124679999981664229965379347, prime_3055465788140352002733946906144561090641249606160407884365391979704929268480326390471, trivial⟩

end p384Prime

/-- `PRIME_P384`. -/
theorem p384_prime : Nat.Prime p384 := p384Prime.prime_p384

/-- `PRIME_N384`. -/
theorem n384_prime : Nat.Prime n384 := p384Prime.prime_n384

instance : Fact (Nat.Prime p384) := ⟨p384_prime⟩

instance : Fact (3 < p384) := ⟨by simp [p384]⟩

instance : Fact (Nat.Prime n384) := ⟨n384_prime⟩

/-- P-384's curve over `ZMod p384`. -/
abbrev p384Curve := nist.curve p384 b384

theorem b384_ne_two : (b384 + 2) % p384 ≠ 0 ∧ (b384 + (p384 - 2)) % p384 ≠ 0 := by
  simp only [b384, p384]; decide

theorem p384OnCurve_G : p384OnCurve p384G := by
  simp only [p384OnCurve, nist.OnCurve, p384G, p384, b384]; decide

theorem fromM_of_onCurve {x y : Nat} (h : p384OnCurve (some (x, y))) :
    ∃ X : p384Curve.Point, nist.fromM X = some (x, y) :=
  nist.fromM_of_onCurve b384_ne_two.1 b384_ne_two.2 h

theorem exists_fromM (P : nist.Point) (hP : p384OnCurve P) : ∃ X : p384Curve.Point, nist.fromM X = P := by
  match P, hP with
  | none, _ => exact ⟨0, rfl⟩
  | some (x, y), h => exact fromM_of_onCurve h

/-- n·G is infinity: the kernel computes (n - 1)·G and finds -G. -/
theorem n384_nsmul_G (X : p384Curve.Point) (hX : nist.fromM X = p384G) : n384 • X = 0 := by
  obtain ⟨G, hG⟩ : ∃ G, p384G = some G := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, p384Neg p384G = some N := ⟨_, rfl⟩
  rw [hG] at hN
  have hm : nist.mulCheck p384 G 384 (n384 - 1) = some N := by
    simp only [p384Neg, nist.neg, p384G, Option.some.injEq] at hG hN
    subst hG hN
    decide +kernel
  exact nist.nsmul_G (by simp [n384]) hm hN X (hX.trans hG)

theorem fromM_G : ∃ X : p384Curve.Point, nist.fromM X = p384G ∧ X ≠ 0 ∧ n384 • X = 0 := by
  obtain ⟨X, hX⟩ := exists_fromM p384G p384OnCurve_G
  exact ⟨X, hX, by rintro rfl; simp [nist.fromM, p384G] at hX, n384_nsmul_G X hX⟩

/-- A multiple of G by a scalar in [1, n) has order n, as G does. -/
theorem g_mult_order (d : Nat) (hd0 : 0 < d) (hd : d < n384) :
    nist.OrderOf p384 n384 (p384Pow p384G d) := by
  obtain ⟨X, hX, hX0, hn⟩ := fromM_G
  rw [← hX]
  exact nist.mult_order X hX0 hn d hd0 hd

/-- A multiple of G by a scalar in [1, n) is a finite point of the curve. -/
theorem g_mult (k : Nat) (hk0 : 0 < k) (hk : k < n384) :
    ∃ x y, p384Pow p384G k = some (x, y) ∧ p384OnCurve (some (x, y)) := by
  obtain ⟨X, hX, hX0, hn⟩ := fromM_G
  rw [← hX]
  exact nist.mult_finite X hX0 hn k hk0 hk

end rind.spec
