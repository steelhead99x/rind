import Rind.Ed25519Group
import ForHumans.Specs.Edwards
import Proofs.Curve25519.Edwards.Basepoint
import Proofs.Curve25519.Edwards.Encoding
import Proofs.Curve25519.Bytes
open Aeneas Aeneas.Std rind.edwards

/-!
# Beneficial AI Foundation's edwards25519, as rind's Ed25519 spec reads it

Beneficial AI Foundation's (BAIF's) curve25519-dalek theorems state dalek's
Ed25519 arithmetic in its EllipticCurve library's group of points of
`curve25519.edwards` over `ZMod curve25519.p`, with RFC 8032's encoding
`curve25519.encodeNat`. `Rind.Ed25519` states rind's Ed25519 in HOL Light's
terms: integer pairs, `edMul`, `edPow`, `edEncode`. `ofDalek` reads a point
of BAIF's group as such a pair, through `Rind.Ed25519Group`'s group `Point
dF`, and the group's sum, multiples, negation, base point, and encoding are
`edMul`, `edPow`, `edNeg`, `edB`, and `edEncode` of it. BAIF's base point
has order L, by its own certificate, so a multiple of it reduced mod L is the
same point. Nothing here needs an axiom beyond Lean's.
-/

namespace rind.spec

open curve25519 (basepoint encodeNat decodeLenientNat)

theorem p_eq : curve25519.p = p25519 := by
  rw [curve25519.p_def]
  rfl

theorem L_eq : curve25519.L = n25519 := by
  rw [curve25519.L_def]
  rfl

/-- BAIF's field is rind's: both are the integers mod 2²⁵⁵ - 19. -/
def toRind : ZMod curve25519.p ≃+* ZMod p25519 := ZMod.ringEquivCongr p_eq

theorem toRind_val (x : ZMod curve25519.p) : (toRind x).val = x.val :=
  ZMod.ringEquivCongr_val p_eq x

theorem toRind_natCast (n : Nat) : toRind (n : ZMod curve25519.p) = n := map_natCast toRind n

theorem toRind_d : toRind curve25519.edwards.d = dF := by
  rw [curve25519.edwards_d, curve25519.d_eq_natCast, toRind_natCast]
  rfl

theorem toRind_a : toRind curve25519.edwards.a = -1 := by
  rw [curve25519.edwards_a_eq_neg_one, map_neg, map_one]

/-- A point of BAIF's group, in `Rind.Ed25519Group`'s. -/
def toPointDF (P : curve25519.edwards.Point) : Point dF :=
  ⟨(toRind P.x, toRind P.y), by
    have h := congrArg toRind P.equation
    simp only [map_add, map_mul, map_pow, map_one, toRind_a,
      toRind_d] at h
    unfold OnCurve
    linear_combination h⟩

theorem toPointDF_zero : toPointDF 0 = 0 := by
  apply Point.ext
  simp [toPointDF, TwistedEdwardsModel.zero_x, TwistedEdwardsModel.zero_y]

theorem toPointDF_add (P Q : curve25519.edwards.Point) : toPointDF (P + Q) = toPointDF P + toPointDF Q := by
  apply Point.ext
  simp only [toPointDF, TwistedEdwardsModel.add_x, TwistedEdwardsModel.add_y,
    TwistedEdwardsModel.addX, TwistedEdwardsModel.addY, TwistedEdwardsModel.addDen₁,
    TwistedEdwardsModel.addDen₂, map_div₀, map_add, map_sub, map_mul, map_one, toRind_a, toRind_d]
  congr 1 <;> ring

/-- `toPointDF`, as a map of groups. -/
def toPointHom : curve25519.edwards.Point →+ Point dF where
  toFun := toPointDF
  map_zero' := toPointDF_zero
  map_add' := toPointDF_add

theorem toPointDF_neg (P : curve25519.edwards.Point) : toPointDF (-P) = -toPointDF P :=
  map_neg toPointHom P

theorem toPointDF_nsmul (n : Nat) (P : curve25519.edwards.Point) : toPointDF (n • P) = n • toPointDF P :=
  map_nsmul toPointHom n P

/-- A point of BAIF's group as `Rind.Ed25519` writes one: its coordinates, as
integers below p. -/
def ofDalek (P : curve25519.edwards.Point) : EdPoint := ((P.x.val : Int), (P.y.val : Int))

theorem ofDalek_eq (P : curve25519.edwards.Point) : ofDalek P = ofPoint (toPointDF P) := by
  simp [ofDalek, ofPoint, toPointDF, toRind_val]

theorem edOnCurve_ofDalek (P : curve25519.edwards.Point) : edOnCurve (ofDalek P) := by
  rw [ofDalek_eq]
  exact edOnCurve_ofPoint _

theorem ofDalek_add (P Q : curve25519.edwards.Point) : ofDalek (P + Q) = edMul (ofDalek P) (ofDalek Q) := by
  rw [ofDalek_eq, ofDalek_eq, ofDalek_eq, edMul_ofPoint, toPointDF_add]

theorem ofDalek_nsmul (n : Nat) (P : curve25519.edwards.Point) : ofDalek (n • P) = edPow (ofDalek P) n := by
  rw [ofDalek_eq, ofDalek_eq, edPow_ofPoint, toPointDF_nsmul]

theorem ofDalek_neg (P : curve25519.edwards.Point) : ofDalek (-P) = edNeg (ofDalek P) := by
  rw [ofDalek_eq, ofDalek_eq, edNeg_ofPoint, toPointDF_neg]

theorem ofDalek_basepoint : ofDalek basepoint = edB := by
  simp only [ofDalek, curve25519.basepoint_x_eq, curve25519.basepoint_y_eq, edB]
  rw [← Nat.cast_ofNat (R := ZMod curve25519.p), ← Nat.cast_ofNat (R := ZMod curve25519.p),
    ZMod.val_natCast, ZMod.val_natCast, p_eq]
  norm_num [p25519]

/-- Each point on the curve is one of BAIF's group's. -/
theorem exists_ofDalek {P : EdPoint} (h : edOnCurve P) : ∃ Q, ofDalek Q = P := by
  obtain ⟨R, rfl⟩ := exists_ofPoint h
  refine ⟨⟨toRind.symm R.1.1, toRind.symm R.1.2, ?_⟩, ?_⟩
  · have h := congrArg toRind.symm R.2
    unfold OnCurve at h
    simp only [map_add, map_mul, map_pow, map_one, map_neg] at h
    unfold TwistedEdwardsModel.Equation
    rw [curve25519.edwards_a_eq_neg_one, show curve25519.edwards.d = toRind.symm dF by
      rw [← toRind_d, RingEquiv.symm_apply_apply]]
    linear_combination h
  · simp [ofDalek, ofPoint, ← toRind_val]

/-- A multiple of BAIF's base point is the base point's in rind's spec, the
multiple reduced mod L or not, since the base point has order L. -/
theorem ofDalek_nsmul_basepoint (n : Nat) : ofDalek ((n % curve25519.L) • basepoint) = edPow edB n := by
  have h : n • basepoint = (n % curve25519.L) • basepoint := by
    conv_lhs => rw [← Nat.mod_add_div n curve25519.L]
    rw [add_nsmul, mul_nsmul, curve25519.L_nsmul_basepoint, nsmul_zero, add_zero]
  rw [← h, ofDalek_nsmul, ofDalek_basepoint]

/-! ## Encodings -/

theorem edModEncode_val (x : ZMod curve25519.p) : edModEncode (x.val : Int) = x.val := by
  have hx : x.val < p25519 := p_eq ▸ ZMod.val_lt x
  unfold edModEncode
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hx)]
  omega

/-- RFC 8032's encoding of a point, as `edEncode` and BAIF's `encodeNat` write it. -/
theorem edEncode_ofDalek (P : curve25519.edwards.Point) : edEncode (ofDalek P) = encodeNat P := by
  rw [curve25519.encodeNat_eq, edEncode, ofDalek, edModEncode_val, edModEncode_val]
  by_cases h : P.x.IsNeg
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), show P.x.val % 2 = 1 from h]
    ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), show P.x.val % 2 = 0 by unfold ZMod.IsNeg at h; omega]
    ring

/-- A 256-bit number whose y, its low 255 bits, is below p and that is not
`x = 0` with the sign bit set: BAIF's lenient decoding, dalek's `decompress`,
finds a point exactly when it encodes one, which is then `edDecode`'s. -/
theorem decodeLenientNat_canonical (n : Nat) (hn : n < 2 ^ 256) (hy : n % 2 ^ 255 < p25519)
    (hs : ¬((n % 2 ^ 255 = 1 ∨ n % 2 ^ 255 = p25519 - 1) ∧ n / 2 ^ 255 = 1)) :
    (∀ P, decodeLenientNat n = some P → edValidEncode n ∧ edDecode n = ofDalek P) ∧
      (decodeLenientNat n = none → ¬edValidEncode n) := by
  have hyp : n % 2 ^ 255 < curve25519.p := p_eq ▸ hy
  constructor
  · intro P hP
    have hx : ¬(P.x = 0 ∧ n / 2 ^ 255 = 1) := by
      rintro ⟨hx0, hs1⟩
      have hy1 := TwistedEdwardsModel.y_eq_one_or_eq_neg_one_of_x_eq_zero P.equation hx0
      rw [curve25519.decodeLenientNat_y hP] at hy1
      apply hs
      refine ⟨?_, hs1⟩
      rcases hy1 with h1 | h1
      · left
        have := congrArg ZMod.val h1
        rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hyp, ZMod.val_one] at this
      · right
        have := congrArg ZMod.val h1
        rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hyp, ZMod.neg_val, ite_eq_right_of_eq_false _ _ (eq_false (one_ne_zero (α := ZMod curve25519.p))),
          ZMod.val_one,
          p_eq] at this
    have he : encodeNat P = n := curve25519.encodeNat_of_decodeLenientNat hP hn hyp hx
    have hv : edValidEncode n := ⟨ofDalek P, edOnCurve_ofDalek P, by rw [edEncode_ofDalek, he]⟩
    refine ⟨hv, ?_⟩
    obtain ⟨hd1, hd2⟩ : edOnCurve (edDecode n) ∧ edEncode (edDecode n) = n :=
      Classical.epsilon_spec hv
    exact edEncode_inj hd1 (edOnCurve_ofDalek P) (by rw [hd2, edEncode_ofDalek, he])
  · intro hnone ⟨Q, hQ, hQe⟩
    obtain ⟨P, rfl⟩ := exists_ofDalek hQ
    rw [edEncode_ofDalek] at hQe
    rw [← hQe, curve25519.decodeLenientNat_encodeNat] at hnone
    simp at hnone

/-- An encoding of a point is 256 bits, its y, the low 255 bits, is below p,
and its sign bit is clear when y is 1 or p - 1, where x is 0. -/
theorem edValidEncode_canonical {n : Nat} (h : edValidEncode n) :
    n < 2 ^ 256 ∧ n % 2 ^ 255 < p25519 ∧
      ¬((n % 2 ^ 255 = 1 ∨ n % 2 ^ 255 = p25519 - 1) ∧ n / 2 ^ 255 = 1) := by
  obtain ⟨Q, hQ, rfl⟩ := h
  obtain ⟨P, rfl⟩ := exists_ofDalek hQ
  rw [edEncode_ofDalek]
  refine ⟨curve25519.encodeNat_lt_two_pow_256 P, ?_, ?_⟩
  · rw [curve25519.encodeNat_mod_two_pow_255, ← p_eq]
    exact ZMod.val_lt _
  · rintro ⟨hy, hs⟩
    have hnone : curve25519.decodeNat (encodeNat P) = none := by
      rw [curve25519.decodeNat_eq_none_iff]
      refine Or.inr (Or.inr (Or.inr ⟨?_, hs⟩))
      rcases hy with h1 | h1 <;> rw [h1]
      · simp
      · rw [← p_eq, Nat.cast_sub (by rw [p_eq]; norm_num [p25519]), ZMod.natCast_self, zero_sub,
          Nat.cast_one, neg_one_sq]
    rw [curve25519.decodeNat_encodeNat] at hnone
    simp at hnone

/-- BAIF's 32 bytes of a point's encoding, read back as a number: the
encoding. -/
theorem decodeLittleEndian_encode (P : curve25519.edwards.Point) :
    curve25519.decodeLittleEndian (curve25519.encode P) = encodeNat P := by
  rw [curve25519.encode, curve25519.decodeLittleEndian_encodeLittleEndian,
    Nat.mod_eq_of_lt (by simpa using curve25519.encodeNat_lt_two_pow_256 P)]

end rind.spec
