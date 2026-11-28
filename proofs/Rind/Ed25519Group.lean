import Rind.Ed25519
import Rind.Edwards
import Rind.Pratt
import Rind.SpecTest.Ed25519
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.NormNum.LegendreSymbol
open Aeneas Aeneas.Std rind.spec rind.edwards

/-!
# edwards25519's group law

`edMul` and `edPow`, HOL Light's `group_mul edwards25519_group` and
`group_pow edwards25519_group`, are the addition and multiples of
`Rind.Edwards`'s group of points on the curve over `ZMod p25519`, for `d` the
curve's: `edMul_ofPoint` and `edPow_ofPoint`. So their laws are that group's,
which no axiom states. The group needs `ZMod p25519` to be a field, which
`Rind.SpecTest.Ed25519`'s `p25519_prime` proves, and complete addition needs
`d` to be a non-square, which the kernel checks by its Legendre symbol.

The half-size check of Ed25519 verification, `mid::half_size`, also rests on
the group's orders, which HOL Light proves from the group's size and these
prove by counting: `edPow_8L` and `edPow_B_L`. From them, `half_size_iff`
proves the check's argument, which `mid/half_size.rs`'s module doc gives: for
`u ≡ v k (mod 8L)` with `v` odd and below `L`, `[v S mod L]B - [v]R - [u]A` is
the identity exactly when `R = [S]B - [k]A`.
-/

namespace rind.spec

/-! ## `L` is prime, by a Pratt certificate -/

namespace ed25519

theorem prime_14741173 : Nat.Prime 14741173 :=
  prime_of_lucas 2 [(2, 2), (3, 2), (409477, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_58964693 : Nat.Prime 58964693 :=
  prime_of_lucas 2 [(2, 2), (14741173, 1)] (by decide +kernel)
    ⟨by norm_num, prime_14741173, trivial⟩

theorem prime_3044861653679985063343 : Nat.Prime 3044861653679985063343 :=
  prime_of_lucas 5 [(2, 1), (3, 1), (11, 1), (30703, 1), (82163, 1), (132667, 1), (137849, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_198211423230930754013084525763697 : Nat.Prime 198211423230930754013084525763697 :=
  prime_of_lucas 5 [(2, 4), (3, 1), (23, 1), (58964693, 1), (3044861653679985063343, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_58964693, prime_3044861653679985063343, trivial⟩

theorem prime_292386187 : Nat.Prime 292386187 :=
  prime_of_lucas 2 [(2, 1), (3, 4), (307, 1), (5879, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_213441916511 : Nat.Prime 213441916511 :=
  prime_of_lucas 13 [(2, 1), (5, 1), (73, 1), (292386187, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_292386187, trivial⟩

theorem prime_1224481 : Nat.Prime 1224481 :=
  prime_of_lucas 13 [(2, 5), (3, 1), (5, 1), (2551, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_1257559732178653 : Nat.Prime 1257559732178653 :=
  prime_of_lucas 2 [(2, 2), (3, 1), (7, 1), (23, 1), (531581, 1), (1224481, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_1224481, trivial⟩

theorem prime_4434155615661930479 : Nat.Prime 4434155615661930479 :=
  prime_of_lucas 17 [(2, 1), (41, 1), (43, 1), (1257559732178653, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_1257559732178653, trivial⟩

theorem prime_172054593956031949258510691 : Nat.Prime 172054593956031949258510691 :=
  prime_of_lucas 2 [(2, 1), (5, 1), (1361, 1), (2851, 1), (4434155615661930479, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_4434155615661930479, trivial⟩

theorem prime_19757330305831588566944191468367130476339 :
    Nat.Prime 19757330305831588566944191468367130476339 :=
  prime_of_lucas 2 [(2, 1), (269, 1), (213441916511, 1), (172054593956031949258510691, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, prime_213441916511, prime_172054593956031949258510691, trivial⟩

theorem prime_276602624281642239937218680557139826668747 :
    Nat.Prime 276602624281642239937218680557139826668747 :=
  prime_of_lucas 2 [(2, 1), (7, 1), (19757330305831588566944191468367130476339, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, prime_19757330305831588566944191468367130476339, trivial⟩

end ed25519

open ed25519 in
/-- `PRIME_N25519`, here by a Pratt certificate rather than an axiom. -/
theorem n25519_prime : Nat.Prime n25519 :=
  prime_of_lucas 2 [(2, 2), (3, 1), (11, 1), (198211423230930754013084525763697, 1),
      (276602624281642239937218680557139826668747, 1)] (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_198211423230930754013084525763697,
      prime_276602624281642239937218680557139826668747, trivial⟩

/-! ## The group -/

/-- `edwards_0`, which `EDWARDS25519_GROUP` shows is
`group_id edwards25519_group`. -/
def edId : EdPoint := (0, 1)

theorem edOnCurve_id : edOnCurve edId := by
  simp only [edOnCurve, edId, p25519]; norm_num

/-- `GENERATOR_IN_GROUP_CARRIER_EDWARDS25519`, here by computation. -/
theorem edOnCurve_B : edOnCurve edB := by
  simp only [edOnCurve, edB, p25519, e25519, d25519]; norm_num

/-- The negation of a point of the group is in the group. -/
theorem edOnCurve_neg (P : EdPoint) (h : edOnCurve P) : edOnCurve (edNeg P) := by
  obtain ⟨x, y⟩ := P
  obtain ⟨-, -, hy0, hy1, he⟩ := h
  have hq : (-x) % (p25519 : Int) ≡ -x [ZMOD p25519] := Int.mod_modEq _ _
  have hq2 : ((-x) % (p25519 : Int)) ^ 2 ≡ x ^ 2 [ZMOD p25519] := by
    simpa [neg_sq] using hq.pow 2
  refine ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide), hy0, hy1, ?_⟩
  show e25519 * ((-x) % (p25519 : Int)) ^ 2 + y ^ 2 ≡
    1 + d25519 * ((-x) % (p25519 : Int)) ^ 2 * y ^ 2 [ZMOD p25519]
  calc _ ≡ e25519 * x ^ 2 + y ^ 2 [ZMOD p25519] := (hq2.mul_left _).add_right _
    _ ≡ 1 + d25519 * x ^ 2 * y ^ 2 [ZMOD p25519] := he
    _ ≡ _ [ZMOD p25519] := ((hq2.symm.mul_left _).mul_right _).add_left _

/-! ## The curve's group, from `Rind.Edwards` -/

/-- The curve's `d`, in the field. -/
abbrev dF : ZMod p25519 := d25519

theorem e25519_eq : (e25519 : ZMod p25519) = -1 := by
  rw [show e25519 = p25519 - 1 by norm_num [e25519, p25519], Nat.cast_sub (by norm_num [p25519]),
    ZMod.natCast_self, Nat.cast_one, zero_sub]

/-- `d` is not a square, by its Legendre symbol. -/
theorem dF_not_square : ¬IsSquare dF := by
  apply (legendreSym.eq_neg_one_iff' p25519).mp
  norm_num [dF, d25519, p25519]

instance : Complete dF where
  two_ne_zero := by
    rw [show (2 : ZMod p25519) = ((2 : ℕ) : ZMod p25519) by norm_num, Ne,
      ZMod.natCast_eq_zero_iff]
    decide +kernel
  neg_one_square := ZMod.exists_sq_eq_neg_one_iff.mpr (by unfold p25519; decide)
  not_square := dF_not_square

/-- The point of the group whose coordinates' values are these. -/
def ofPoint (Q : Point dF) : EdPoint := ((Q.1.1.val : Int), (Q.1.2.val : Int))

theorem cast_ofPoint_fst (Q : Point dF) : ((ofPoint Q).1 : ZMod p25519) = Q.1.1 := by
  simp [ofPoint]

theorem cast_ofPoint_snd (Q : Point dF) : ((ofPoint Q).2 : ZMod p25519) = Q.1.2 := by
  simp [ofPoint]

theorem onCurve_iff (P : EdPoint) :
    edOnCurve P ↔ 0 ≤ P.1 ∧ P.1 < p25519 ∧ 0 ≤ P.2 ∧ P.2 < p25519 ∧
      OnCurve dF ((P.1 : ZMod p25519), (P.2 : ZMod p25519)) := by
  unfold edOnCurve OnCurve
  rw [← ZMod.intCast_eq_intCast_iff']
  push_cast
  rw [e25519_eq]
  constructor <;> rintro ⟨h0, h1, h2, h3, h4⟩ <;> exact ⟨h0, h1, h2, h3, by linear_combination h4⟩

theorem edOnCurve_ofPoint (Q : Point dF) : edOnCurve (ofPoint Q) := by
  rw [onCurve_iff, cast_ofPoint_fst, cast_ofPoint_snd]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (ZMod.val_lt Q.1.1), Int.natCast_nonneg _,
    Int.ofNat_lt.mpr (ZMod.val_lt Q.1.2), Q.2⟩

/-- The point of the group a point on the curve names. -/
def toPoint (P : EdPoint) (h : edOnCurve P) : Point dF :=
  ⟨((P.1 : ZMod p25519), (P.2 : ZMod p25519)), ((onCurve_iff P).mp h).2.2.2.2⟩

theorem ofPoint_toPoint (P : EdPoint) (h : edOnCurve P) : ofPoint (toPoint P h) = P := by
  obtain ⟨h0, h1, h2, h3, -⟩ := (onCurve_iff P).mp h
  simp only [ofPoint, toPoint, ZMod.val_intCast, Int.emod_eq_of_lt h0 h1, Int.emod_eq_of_lt h2 h3]

/-- Each point on the curve is one of the group's. -/
theorem exists_ofPoint {P : EdPoint} (h : edOnCurve P) : ∃ Q, ofPoint Q = P :=
  ⟨toPoint P h, ofPoint_toPoint P h⟩

/-- `edMul` is the group's addition. -/
theorem edMul_ofPoint (Q R : Point dF) : edMul (ofPoint Q) (ofPoint R) = ofPoint (Q + R) := by
  simp only [edMul, cast_ofPoint_fst, cast_ofPoint_snd, e25519_eq]
  simp only [ofPoint, Point.val_add, add, div_eq_mul_inv]
  congr 3 <;> ring

/-- `edPow` is the group's multiples. -/
theorem edPow_ofPoint (Q : Point dF) (n : Nat) : edPow (ofPoint Q) n = ofPoint (n • Q) := by
  induction n with
  | zero => simp [edPow, ofPoint, ZMod.val_one]
  | succ n ih => rw [edPow, ih, edMul_ofPoint, succ_nsmul, add_comm]

/-- `edNeg` is the group's negation. -/
theorem edNeg_ofPoint (Q : Point dF) : edNeg (ofPoint Q) = ofPoint (-Q) := by
  simp only [edNeg, ofPoint, Point.val_neg, Prod.mk.injEq, and_true]
  rw [← ZMod.val_intCast]
  push_cast
  simp

theorem edId_ofPoint : edId = ofPoint 0 := by
  simp [edId, ofPoint, ZMod.val_one]

theorem edOnCurve_mul {P Q : EdPoint} (hP : edOnCurve P) (hQ : edOnCurve Q) : edOnCurve (edMul P Q) := by
  obtain ⟨P, rfl⟩ := exists_ofPoint hP
  obtain ⟨Q, rfl⟩ := exists_ofPoint hQ
  rw [edMul_ofPoint]; exact edOnCurve_ofPoint _

theorem edMul_assoc {P Q R : EdPoint} (hP : edOnCurve P) (hQ : edOnCurve Q) (hR : edOnCurve R) :
    edMul P (edMul Q R) = edMul (edMul P Q) R := by
  obtain ⟨P, rfl⟩ := exists_ofPoint hP
  obtain ⟨Q, rfl⟩ := exists_ofPoint hQ
  obtain ⟨R, rfl⟩ := exists_ofPoint hR
  simp only [edMul_ofPoint, add_assoc]

theorem edMul_comm {P Q : EdPoint} (hP : edOnCurve P) (hQ : edOnCurve Q) : edMul P Q = edMul Q P := by
  obtain ⟨P, rfl⟩ := exists_ofPoint hP
  obtain ⟨Q, rfl⟩ := exists_ofPoint hQ
  simp only [edMul_ofPoint, add_comm]

theorem edMul_id {P : EdPoint} (hP : edOnCurve P) : edMul edId P = P := by
  obtain ⟨P, rfl⟩ := exists_ofPoint hP
  rw [edId_ofPoint, edMul_ofPoint, zero_add]

theorem edMul_neg {P : EdPoint} (hP : edOnCurve P) : edMul (edNeg P) P = edId := by
  obtain ⟨P, rfl⟩ := exists_ofPoint hP
  rw [edNeg_ofPoint, edMul_ofPoint, neg_add_cancel, edId_ofPoint]

theorem edPow_zero (P : EdPoint) : edPow P 0 = edId := rfl

theorem edPow_succ (P : EdPoint) (n : Nat) : edPow P (n + 1) = edMul P (edPow P n) := rfl

/-- Two points of the group with one encoding are the same point:
`Rind.SpecTest.Ed25519`'s `encode_inj`, s2n-bignum's
`ED25519_ENCODE_INJECTIVE`. -/
theorem edEncode_inj {P Q : EdPoint} (hP : edOnCurve P) (hQ : edOnCurve Q) (h : edEncode P = edEncode Q) :
    P = Q :=
  encode_inj hP hQ h

/-! ## The group's orders

Mathlib has no Hasse bound, so the count is elementary, as
`Rind.NistOrder`'s:

1. Two points with one y have x² = (y² - 1)/(d y² + 1), so opposite x, and
   with its x's parity a point's y names it: the group has at most 2p points.
2. The kernel checks that `[L]B` and `[8]T₈` are the identity but `[4]T₈` is
   not, for a point `T₈`, so B has order L and T₈ order 8, and by Lagrange 8L
   divides the group's size.
3. 16L > 2p, so the size is 8L, and every point's multiple by 8L is the
   identity.
-/

/-- A point's coordinates as numbers below p. -/
def coords (Q : Point dF) : ℕ × ℕ := (Q.1.1.val, Q.1.2.val)

theorem coords_toPoint (P : EdPoint) (h : edOnCurve P) : coords (toPoint P h) = (P.1.toNat, P.2.toNat) := by
  have e := ofPoint_toPoint P h
  obtain ⟨x, y⟩ := P
  simp only [ofPoint, Prod.mk.injEq] at e
  simp only [coords, Prod.mk.injEq]
  omega

theorem eq_zero_of_coords {Q : Point dF} (h : coords Q = (0, 1)) : Q = 0 := by
  simp only [coords, Prod.mk.injEq] at h
  apply Point.ext
  rw [Point.val_zero, Prod.ext_iff]
  refine ⟨(ZMod.val_eq_zero _).mp h.1, ?_⟩
  rw [← ZMod.natCast_zmod_val Q.1.2, h.2, Nat.cast_one]

/-- `a`'s inverse mod p, by Fermat. `edMulCheck` checks each sum, so nothing
relies on this being right. -/
def invP (a : ℕ) : ℕ := powMod p25519 256 a (p25519 - 2)

/-- `add`'s sum of two points as numbers, so the kernel can evaluate it. -/
def edAddC : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
  | (x1, y1), (x2, y2) =>
    let t := d25519 * x1 * x2 * y1 * y2 % p25519
    ((x1 * y2 + y1 * x2) * invP ((1 + t) % p25519) % p25519,
      (y1 * y2 + x1 * x2) * invP ((1 + p25519 - t) % p25519) % p25519)

/-- Whether `(x3, y3)` is `add`'s sum of `(x1, y1)` and `(x2, y2)`, checked by
multiplying out its denominators rather than inverting them. -/
def edAddOk : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → Bool
  | (x1, y1), (x2, y2), (x3, y3) =>
    let t := d25519 * x1 * x2 * y1 * y2 % p25519
    x3 < p25519 && y3 < p25519 && (1 + t) % p25519 != 0 && (1 + p25519 - t) % p25519 != 0 &&
      x3 * (1 + t) % p25519 == (x1 * y2 + y1 * x2) % p25519 &&
      y3 * (1 + p25519 - t) % p25519 == (y1 * y2 + x1 * x2) % p25519

theorem edAddOk_spec {Q R : Point dF} {S : ℕ × ℕ} (h : edAddOk (coords Q) (coords R) S = true) :
    coords (Q + R) = S := by
  obtain ⟨x3, y3⟩ := S
  simp only [coords, edAddOk, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hx3, hy3⟩, ha⟩, hs⟩, ex⟩, ey⟩ := h
  have htp : d25519 * Q.1.1.val * R.1.1.val * Q.1.2.val * R.1.2.val % p25519 < p25519 :=
    Nat.mod_lt _ (by decide)
  have ha' : ((1 + d25519 * Q.1.1.val * R.1.1.val * Q.1.2.val * R.1.2.val % p25519 : ℕ) : ZMod p25519) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]; exact ha
  have hs' : ((1 + p25519 - d25519 * Q.1.1.val * R.1.1.val * Q.1.2.val * R.1.2.val % p25519 : ℕ) :
      ZMod p25519) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]; exact hs
  have ex' := (ZMod.natCast_eq_natCast_iff' _ _ p25519).mpr ex
  have ey' := (ZMod.natCast_eq_natCast_iff' _ _ p25519).mpr ey
  have hle : d25519 * Q.1.1.val * R.1.1.val * Q.1.2.val * R.1.2.val % p25519 ≤ 1 + p25519 := by omega
  push_cast [Nat.cast_sub hle, ZMod.natCast_mod, ZMod.natCast_zmod_val, ZMod.natCast_self] at ha' hs' ex' ey'
  have hv : ∀ {n : ℕ}, n < p25519 → (n : ZMod p25519).val = n := ZMod.val_natCast_of_lt
  simp only [coords, Point.val_add, add, Prod.mk.injEq]
  constructor
  · rw [← hv hx3]
    congr 1
    exact (div_eq_iff ha').mpr (by linear_combination -ex')
  · rw [← hv hy3]
    congr 1
    rw [add_zero] at hs' ey'
    exact (div_eq_iff hs').mpr (by linear_combination -ey')

/-- `f x`, with `x` evaluated first, which keeps the kernel from carrying an
unevaluated sum up `edMulCheck`'s recursion. -/
def force {α : Type} (x : ℕ) (f : ℕ → α) : α :=
  match x with
  | 0 => f 0
  | n + 1 => f (n + 1)

theorem force_eq {α : Type} (x : ℕ) (f : ℕ → α) : force x f = f x := by
  cases x <;> rfl

/-- `k` times the point `P`, for `k < 2 ^ fuel`, by doubling and adding, or
`none` if `edAddOk` refuses a sum. -/
def edMulCheck (P : ℕ × ℕ) : ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _ => none
  | fuel + 1, k =>
    if k = 0 then some (0, 1)
    else match edMulCheck P fuel (k / 2) with
      | none => none
      | some Q =>
        let D := edAddC Q Q
        if edAddOk Q Q D then
          force D.1 fun x => force D.2 fun y =>
          if k % 2 = 0 then some (x, y)
          else
            let S := edAddC (x, y) P
            if edAddOk (x, y) P S then force S.1 fun a => force S.2 fun b => some (a, b) else none
        else none

theorem edMulCheck_spec (X : Point dF) : ∀ fuel k R, edMulCheck (coords X) fuel k = some R → coords (k • X) = R
  | 0, _, _, h => by simp [edMulCheck] at h
  | fuel + 1, k, R, h => by
    unfold edMulCheck at h
    by_cases h0 : k = 0
    · simp only [h0, ↓reduceIte, Option.some.injEq] at h
      subst h h0
      simp [coords, ZMod.val_one]
    simp only [h0, ↓reduceIte] at h
    rcases hq : edMulCheck (coords X) fuel (k / 2) with _ | Q
    · simp [hq] at h
    have ih := edMulCheck_spec X fuel _ _ hq
    simp only [hq, force_eq] at h
    by_cases hD : edAddOk Q Q (edAddC Q Q) = true
    swap
    · simp [hD] at h
    have hD' : coords ((k / 2) • X + (k / 2) • X) = edAddC Q Q := edAddOk_spec (by rw [ih]; exact hD)
    by_cases h2 : k % 2 = 0
    · simp only [hD, h2, ↓reduceIte, Option.some.injEq] at h
      subst h
      rw [show k = k / 2 + k / 2 by omega, add_nsmul, hD']
    by_cases hS : edAddOk (edAddC Q Q) (coords X) (edAddC (edAddC Q Q) (coords X)) = true
    · simp only [hD, h2, hS, ↓reduceIte, Option.some.injEq] at h
      subst h
      rw [show k = k / 2 + k / 2 + 1 by omega, add_nsmul, add_nsmul, one_nsmul]
      exact edAddOk_spec (by rw [hD']; exact hS)
    · simp [hD, h2, hS] at h

/-- A point of order 8. -/
def edT8 : EdPoint :=
  (14399317868200118260347934320527232580618823971194345261214217575416788799818,
    55188659117513257062467267217118295137698188065244968500265048394206261417927)

theorem edOnCurve_T8 : edOnCurve edT8 := by
  simp only [edOnCurve, edT8, p25519, e25519, d25519]; norm_num

theorem mulCheck_B : edMulCheck (edB.1.toNat, edB.2.toNat) 256 n25519 = some (0, 1) := by
  decide +kernel

theorem mulCheck_T8_4 : edMulCheck (edT8.1.toNat, edT8.2.toNat) 256 4 = some (0, p25519 - 1) := by
  decide +kernel

theorem mulCheck_T8_8 : edMulCheck (edT8.1.toNat, edT8.2.toNat) 256 8 = some (0, 1) := by
  decide +kernel

/-- A point's y and its x's parity, which name it. -/
def yParity (Q : Point dF) : ZMod p25519 × Bool := (Q.1.2, decide (Q.1.1.val % 2 = 0))

theorem yParity_injective : Function.Injective yParity := by
  intro Q R h
  simp only [yParity, Prod.mk.injEq, decide_eq_decide] at h
  obtain ⟨hy, hpar⟩ := h
  have hQ := x_sq Q.2
  have hR := x_sq R.2
  rw [hy] at hQ
  have hx : (Q.1.1.val : ZMod p25519) ^ 2 = (R.1.1.val : ZMod p25519) ^ 2 := by
    simp only [ZMod.natCast_zmod_val]; rw [hQ, hR]
  have := eq_of_sq (ZMod.val_lt _) (ZMod.val_lt _) hx (by omega)
  exact Point.ext (Prod.ext ((ZMod.val_injective _) this) hy)

instance : Finite (Point dF) := Finite.of_injective _ yParity_injective

theorem card_le : Nat.card (Point dF) ≤ 2 * p25519 := by
  refine (Nat.card_le_card_of_injective _ yParity_injective).trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]

instance : Fact (Nat.Prime n25519) := ⟨n25519_prime⟩

theorem card_eq : Nat.card (Point dF) = 8 * n25519 := by
  have hB := edMulCheck_spec (toPoint edB edOnCurve_B) 256 _ _ (coords_toPoint edB edOnCurve_B ▸ mulCheck_B)
  have hT4 := edMulCheck_spec (toPoint edT8 edOnCurve_T8) 256 _ _
    (coords_toPoint edT8 edOnCurve_T8 ▸ mulCheck_T8_4)
  have hT8 := edMulCheck_spec (toPoint edT8 edOnCurve_T8) 256 _ _
    (coords_toPoint edT8 edOnCurve_T8 ▸ mulCheck_T8_8)
  have oB : addOrderOf (toPoint edB edOnCurve_B) = n25519 := by
    refine addOrderOf_eq_prime (eq_zero_of_coords hB) fun h0 => ?_
    have := congrArg coords h0
    rw [coords_toPoint] at this
    simp [coords, edB, ZMod.val_one] at this
  have oT : addOrderOf (toPoint edT8 edOnCurve_T8) = 2 ^ 3 := by
    refine addOrderOf_eq_prime_pow (fun h0 => ?_) (eq_zero_of_coords (by simpa using hT8))
    have := congrArg coords h0
    rw [show 2 ^ 2 = 4 by rfl, hT4] at this
    norm_num [coords, ZMod.val_zero, ZMod.val_one, p25519] at this
  have d1 := oB ▸ addOrderOf_dvd_natCard (toPoint edB edOnCurve_B)
  have d2 := oT ▸ addOrderOf_dvd_natCard (toPoint edT8 edOnCurve_T8)
  have d : 8 * n25519 ∣ Nat.card (Point dF) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) d2 d1
  obtain ⟨c, hc⟩ := d
  have hle := card_le
  have hpos : 0 < Nat.card (Point dF) := Nat.card_pos
  have hp : 2 * p25519 < 16 * n25519 := by decide
  have hc1 : c = 1 := by
    rcases c with _ | _ | c
    · omega
    · rfl
    · have : 8 * n25519 * 2 ≤ Nat.card (Point dF) := hc ▸ Nat.mul_le_mul_left _ (by omega)
      omega
  rw [hc, hc1, mul_one]

/-- Every point's multiple by 8L is the identity, by `card_eq` and Lagrange:
`SIZE_EDWARDS25519_GROUP` in HOL Light. -/
theorem edPow_8L {P : EdPoint} (h : edOnCurve P) : edPow P (8 * n25519) = edId := by
  obtain ⟨Q, rfl⟩ := exists_ofPoint h
  rw [edPow_ofPoint, ← card_eq, card_nsmul_eq_zero', edId_ofPoint]

/-- The base point has order L: `GROUP_ELEMENT_ORDER_EDWARDS25519_E25519` in
HOL Light. -/
theorem edPow_B_L : edPow edB n25519 = edId := by
  have hB := edMulCheck_spec (toPoint edB edOnCurve_B) 256 _ _ (coords_toPoint edB edOnCurve_B ▸ mulCheck_B)
  rw [← ofPoint_toPoint edB edOnCurve_B, edPow_ofPoint, eq_zero_of_coords hB, edId_ofPoint]

/-- `edwards25519_group` as a Lean group. -/
abbrev EdG := {P : EdPoint // edOnCurve P}

noncomputable instance : CommGroup EdG where
  mul a b := ⟨edMul a.1 b.1, edOnCurve_mul a.2 b.2⟩
  mul_assoc a b c := Subtype.ext (edMul_assoc a.2 b.2 c.2).symm
  one := ⟨edId, edOnCurve_id⟩
  one_mul a := Subtype.ext (edMul_id a.2)
  mul_one a := Subtype.ext ((edMul_comm a.2 edOnCurve_id).trans (edMul_id a.2))
  inv a := ⟨edNeg a.1, edOnCurve_neg _ a.2⟩
  inv_mul_cancel a := Subtype.ext (edMul_neg a.2)
  mul_comm a b := Subtype.ext (edMul_comm a.2 b.2)

@[simp] theorem EdG.mul_val (a b : EdG) : (a * b).1 = edMul a.1 b.1 := rfl
@[simp] theorem EdG.one_val : (1 : EdG).1 = edId := rfl
@[simp] theorem EdG.inv_val (a : EdG) : a⁻¹.1 = edNeg a.1 := rfl

theorem EdG.pow_val (a : EdG) (n : Nat) : (a ^ n).1 = edPow a.1 n := by
  induction n with
  | zero => rw [pow_zero, edPow_zero]; rfl
  | succ n ih => rw [pow_succ', edPow_succ, EdG.mul_val, ih]

/-- The group's power stays in the group. -/
theorem edOnCurve_pow {P : EdPoint} (h : edOnCurve P) (n : Nat) : edOnCurve (edPow P n) := by
  rw [← EdG.pow_val ⟨P, h⟩ n]; exact (⟨P, h⟩ ^ n : EdG).2

theorem EdG.pow_exponent (a : EdG) : a ^ (8 * n25519) = 1 :=
  Subtype.ext (by rw [EdG.pow_val]; exact edPow_8L a.2)

/-- Raising to a power prime to `8L` keeps every point but the identity off
the identity. -/
theorem EdG.pow_eq_one_iff (x : EdG) {v : Nat} (hv : Nat.Coprime v (8 * n25519)) :
    x ^ v = 1 ↔ x = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  have h1 : orderOf x ∣ v := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf x ∣ 8 * n25519 := orderOf_dvd_of_pow_eq_one x.pow_exponent
  have : orderOf x = 1 := Nat.eq_one_of_dvd_one (hv ▸ Nat.dvd_gcd h1 h2)
  exact orderOf_eq_one_iff.mp this

theorem coprime_8n (v : Nat) (hv : v % 2 = 1) (h0 : 0 < v) (hvL : v < n25519) :
    Nat.Coprime v (8 * n25519) := by
  refine Nat.Coprime.mul_right ?_ ?_
  · rw [show (8 : Nat) = 2 ^ 3 from rfl]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega))))
  · exact Nat.Coprime.symm ((n25519_prime.coprime_iff_not_dvd).mpr (fun hd => by
      have := Nat.le_of_dvd h0 hd; omega))

/-- `half_size_iff`'s `[|u|]` of `A` or of its negation, as a power of `A`
by `-u`. -/
theorem EdG.signed_pow (a : EdG) (neg : Bool) (m : Nat) :
    (if neg then a else a⁻¹) ^ m = a ^ (-(if neg then -(m : Int) else m)) := by
  cases neg <;> simp [zpow_neg, inv_pow]

/-- The half-size check's argument: for `u ≡ v k (mod 8L)`, `u` given by its
sign and magnitude, with `v` odd and below `L`, the multiple
`[v S mod L]B + [v](-R) + [|u|]A'`, with `A'` either `A`, for `u` negative, or
`-A`, is the identity exactly when `R = [S]B - [k]A`, whatever torsion `A`
and `R` carry. -/
theorem half_size_iff (A R : EdPoint) (hA : edOnCurve A) (hR : edOnCurve R) (S k v m : Nat)
    (neg : Bool) (hu : (if neg then -(m : Int) else m) ≡ v * k [ZMOD 8 * n25519])
    (hv : v % 2 = 1) (hvL : v < n25519) :
    edMul (edMul (edPow edB (v * S % n25519)) (edPow (edNeg R) v)) (edPow (if neg then A else edNeg A) m) = edId ↔
      R = edMul (edPow (edNeg A) k) (edPow edB S) := by
  set a : EdG := ⟨A, hA⟩
  set r : EdG := ⟨R, hR⟩
  set b : EdG := ⟨edB, edOnCurve_B⟩
  have hb : b ^ n25519 = 1 := Subtype.ext (by rw [EdG.pow_val]; exact edPow_B_L)
  have hA' : (if neg then A else edNeg A) = (if neg then a else a⁻¹).1 := by cases neg <;> rfl
  have hlhs : edMul (edMul (edPow edB (v * S % n25519)) (edPow (edNeg R) v))
      (edPow (if neg then A else edNeg A) m) =
      (b ^ (v * S % n25519) * r⁻¹ ^ v * (if neg then a else a⁻¹) ^ m).1 := by
    rw [hA', EdG.mul_val, EdG.mul_val, EdG.pow_val, EdG.pow_val, EdG.pow_val]; rfl
  have hrhs : edMul (edPow (edNeg A) k) (edPow edB S) = (a⁻¹ ^ k * b ^ S).1 := by
    rw [EdG.mul_val, EdG.pow_val, EdG.pow_val]; rfl
  -- [v S mod L]B = [v S]B, as B has order L.
  have hbS : b ^ (v * S % n25519) = b ^ (v * S) := by
    conv_rhs => rw [← Nat.mod_add_div (v * S) n25519, pow_add, pow_mul, hb, one_pow, mul_one]
  -- [-u]A = [-v k]A, as every point has order dividing 8L.
  have hau : (if neg then a else a⁻¹) ^ m = a ^ (-((v * k : Nat) : Int)) := by
    rw [EdG.signed_pow, zpow_eq_zpow_iff_modEq]
    have hd : (orderOf a : Int) ∣ 8 * n25519 := by
      exact_mod_cast orderOf_dvd_of_pow_eq_one a.pow_exponent
    exact (Int.ModEq.neg (hu.trans (by push_cast; rfl))).of_dvd hd
  have hx : b ^ (v * S % n25519) * r⁻¹ ^ v * (if neg then a else a⁻¹) ^ m =
      (b ^ S * (a⁻¹ ^ k) * r⁻¹) ^ v := by
    rw [hbS, hau, zpow_neg, zpow_natCast]
    simp only [mul_pow, inv_pow, ← pow_mul]
    rw [mul_comm S v, mul_comm k v, mul_right_comm]
  have hco := coprime_8n v hv (by omega) hvL
  rw [hlhs, hrhs, hx, ← EdG.one_val]
  constructor
  · intro h
    have h1 := (EdG.pow_eq_one_iff _ hco).mp (Subtype.ext h)
    have : r = a⁻¹ ^ k * b ^ S := by
      rw [mul_comm (a⁻¹ ^ k)]; exact (mul_inv_eq_one.mp h1).symm
    exact congrArg Subtype.val this
  · intro h
    have hr : r = a⁻¹ ^ k * b ^ S := Subtype.ext h
    rw [hr, mul_comm (a⁻¹ ^ k), mul_inv_cancel, one_pow]

end rind.spec
