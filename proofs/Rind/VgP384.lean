import Rind.P384Multiples
import Rind.Bytes
import Rind.VgOutcome
import VerifiedGarbage.Spec.EcKey
import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Spec.Ecdsa.Verify.P384
import VerifiedGarbage.Spec.Ecdsa.Verify
import VerifiedGarbage.Spec.P384
open Aeneas Aeneas.Std rind.spec VG.Spec.Weierstrass

set_option exponentiation.threshold 400

/-!
# pyca/verified-garbage's P-384 spec is rind's

VG's contracts for its P-384 routines state their results over its own
transcription of SEC 1 and FIPS 186-5 (`VG.Spec.Weierstrass`,
`VG.Spec.EcKey`, and `VG.Spec.Ecdsa`, on the curve `VG.Spec.P384.curve`), which
`admin/import-vg-models` vendors. This proves
that, on P-384, they are what rind's theorems state over HOL Light's
(`Rind/Spec.lean`): VG's points, read as `ofVg`, add as `p384Add` and
multiply as `p384Pow`, through Mathlib's group of points (`Rind.NistGroup`);
its key validation is `p384OnCurve`; its octet strings are `beNat`'s; and
its ECDSA verification is `ecdsaP384Verifies`.
-/

namespace rind.spec.vgP384

/-- VG's P-384. -/
abbrev C : Curve := VG.Spec.P384.curve

theorem p_eq : C.p = p384 := by
  show VG.Spec.P384.p = p384
  decide +kernel

theorem n_eq : C.n = n384 := by
  show VG.Spec.P384.n = n384
  decide +kernel

/-! ## VG's field elements in `ZMod p384` -/

/-- A field element of VG's spec in `ZMod p384`. -/
def fe (a : Fin C.p) : ZMod p384 := (a.val : ZMod p384)

theorem natCast_mod_p (k : Nat) : ((k % C.p : Nat) : ZMod p384) = k := by
  rw [p_eq, ZMod.natCast_mod]

theorem natCast_p : ((C.p : Nat) : ZMod p384) = 0 := by
  rw [p_eq]; exact ZMod.natCast_self _

/-- Fermat's little theorem, as VG's spec takes inverses. -/
theorem pow_sub_two_eq_inv {q : Nat} [Fact q.Prime] (hq : 2 < q) (a : ZMod q) : a ^ (q - 2) = a⁻¹ := by
  by_cases ha : a = 0
  · subst ha; rw [zero_pow (by omega), inv_zero]
  · apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show q - 2 + 1 = q - 1 by omega, ZMod.pow_card_sub_one_eq_one ha]

theorem fe_val (a : Fin C.p) : (fe a).val = a.val := by
  unfold fe
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_eq a.isLt p_eq)]

theorem fe_inj {a b : Fin C.p} : fe a = fe b ↔ a = b := by
  constructor
  · intro h
    exact Fin.ext (by rw [← fe_val a, ← fe_val b, h])
  · rintro rfl; rfl

theorem fe_add (a b : Fin C.p) : fe (a + b) = fe a + fe b := by
  simp only [fe, Fin.val_add, natCast_mod_p, Nat.cast_add]

theorem fe_mul (a b : Fin C.p) : fe (a * b) = fe a * fe b := by
  simp only [fe, Fin.val_mul, natCast_mod_p, Nat.cast_mul]

theorem fe_neg (a : Fin C.p) : fe (-a) = -fe a := by
  have hl : a.val ≤ C.p := a.isLt.le
  simp only [fe, Fin.coe_neg, natCast_mod_p]
  rw [Nat.cast_sub hl, natCast_p, zero_sub]

theorem fe_sub (a b : Fin C.p) : fe (a - b) = fe a - fe b := by
  rw [sub_eq_add_neg a b, fe_add, fe_neg, sub_eq_add_neg]

theorem fe_ofNat (k : Nat) : fe (Fin.ofNat C.p k) = k := by
  simp only [fe, Fin.val_ofNat, natCast_mod_p]

theorem fe_two : fe (2 : Fe C) = 2 := by
  show fe (Fin.ofNat C.p 2) = 2
  rw [fe_ofNat]; norm_num

theorem fe_three : fe (3 : Fe C) = 3 := by
  show fe (Fin.ofNat C.p 3) = 3
  rw [fe_ofNat]; norm_num

theorem fe_one : fe (1 : Fin C.p) = 1 := by
  show fe (Fin.ofNat C.p 1) = 1
  rw [fe_ofNat, Nat.cast_one]

theorem fe_pow (a : Fin C.p) (e : Nat) : fe (pow a e) = fe a ^ e := by
  induction e using Nat.strong_induction_on generalizing a with
  | _ e ih =>
    rw [pow]
    split_ifs with h0 h2
    · subst h0; rw [fe_one, _root_.pow_zero]
    · rw [ih _ (by omega), fe_mul, ← sq, ← pow_mul]
      congr 1; omega
    · rw [fe_mul, ih _ (by omega), fe_mul, ← sq, ← pow_mul, ← pow_succ']
      congr 1; omega

theorem fe_inv (a : Fin C.p) : fe (inv a) = (fe a)⁻¹ := by
  unfold inv
  rw [fe_pow, p_eq, pow_sub_two_eq_inv (by simp [p384])]

theorem fe_a : fe (Fin.ofNat C.p C.a) = -3 := by
  rw [fe_ofNat]
  have h3 : 3 ≤ p384 := by simp [p384]
  show (((VG.Spec.P384.p - 3 : Nat)) : ZMod p384) = -3
  rw [show VG.Spec.P384.p = p384 from p_eq, Nat.cast_sub h3, ZMod.natCast_self]
  simp

theorem fe_b : fe (Fin.ofNat C.p C.b) = (b384 : ZMod p384) := by
  rw [fe_ofNat]; rfl

/-! ## Points -/

/-- A point of VG's spec as `Rind/Spec.lean` writes it. -/
def ofVg : Point C → nist.Point
  | .infinity => none
  | .affine x y => some (x.val, y.val)

/-- A point of VG's spec with the field element of `ofVg`'s coordinates. -/
theorem ofVg_affine (x y : Fin C.p) : ofVg (.affine x y) = some ((fe x).val, (fe y).val) := by
  simp only [ofVg, fe_val]

/-- VG's curve equation is rind's. -/
theorem onCurve_iff (x y : Fin C.p) : onCurve C (.affine x y) = true ↔ p384OnCurve (ofVg (.affine x y)) := by
  have hx : x.val < p384 := lt_of_lt_of_eq x.isLt p_eq
  have hy : y.val < p384 := lt_of_lt_of_eq y.isLt p_eq
  simp only [onCurve, decide_eq_true_eq, ofVg, p384OnCurve, nist.OnCurve, hx, hy, true_and]
  rw [← fe_inj, ← ZMod.natCast_eq_natCast_iff']
  simp only [fe_add, fe_mul, fe_a, fe_b, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub (show 3 ≤ p384 by simp [p384]), ZMod.natCast_self]
  unfold fe
  constructor <;> intro h <;> linear_combination h

/-- VG's addition is the group's, for points of it. -/
theorem ofVg_add {P Q : Point C} {X Y : p384Curve.Point} (hP : ofVg P = nist.fromM X)
    (hQ : ofVg Q = nist.fromM Y) : ofVg (add P Q) = nist.fromM (X + Y) := by
  rw [← nist.fromM_add, ← hP, ← hQ]
  rcases P with _ | ⟨x1, y1⟩ <;> rcases Q with _ | ⟨x2, y2⟩
  · rfl
  · simp [add, ofVg, nist.add]
  · simp [add, ofVg, nist.add]
  rcases X with _ | ⟨u1, v1, h1⟩
  · simp [ofVg, nist.fromM] at hP
  rcases Y with _ | ⟨u2, v2, h2⟩
  · simp [ofVg, nist.fromM] at hQ
  simp only [ofVg_affine, nist.fromM, Option.some.injEq, Prod.mk.injEq] at hP hQ
  obtain ⟨hu1, hv1⟩ := hP
  obtain ⟨hu2, hv2⟩ := hQ
  rw [ZMod.val_injective _ |>.eq_iff] at hu1 hv1 hu2 hv2
  subst hu1 hv1 hu2 hv2
  rw [ofVg_affine, ofVg_affine, nist.add_val]
  unfold add
  by_cases hx : x1 = x2
  · subst hx
    by_cases hy : y2 = -y1
    · have hf : fe y2 = -fe y1 := by rw [hy, fe_neg]
      simp only [hy, and_self, ↓reduceIte, ofVg, nist.addF]
      rw [if_neg]
      rintro ⟨he, h0⟩
      apply h0
      have : 2 * fe y1 = 0 := by rw [fe_neg] at he; linear_combination he
      exact (mul_eq_zero.mp this).resolve_left nist.two_ne_zero'
    · have hyy : fe y1 = fe y2 := by
        rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h1.1 h2.1 rfl with h | h
        · exact h
        · exfalso; apply hy
          rw [nist.negY_eq] at h
          rw [← fe_inj, fe_neg, h, neg_neg]
      have hy0 : fe y1 ≠ 0 := by
        intro h0; apply hy
        rw [← fe_inj, fe_neg, ← hyy, h0, neg_zero]
      have hyy' : y1 = y2 := fe_inj.mp hyy
      subst hyy'
      simp only [hy, and_false, ↓reduceIte, ne_eq, not_true_eq_false, ofVg_affine, nist.addF,
        hy0, not_false_eq_true, and_self]
      simp only [fe_sub, fe_mul, fe_add, fe_inv, fe_a, fe_two, fe_three]
      rw [show 3 * fe x1 * fe x1 = 3 * fe x1 ^ 2 by ring, ← sq]
  · have hfx : fe x1 ≠ fe x2 := fun h => hx (fe_inj.mp h)
    simp only [hx, false_and, ↓reduceIte, ne_eq, not_false_eq_true, ofVg_affine, nist.addF, hfx]
    simp only [fe_sub, fe_mul, fe_inv]
    congr 3 <;> ring

/-- VG's multiplication is the group's, for points of it. -/
theorem ofVg_mul {P : Point C} {X : p384Curve.Point} (hP : ofVg P = nist.fromM X) (k : Nat) :
    ofVg (mul k P) = nist.fromM (k • X) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [mul]
    split_ifs with h0 h2
    · subst h0; rw [zero_nsmul]; rfl
    · rw [ofVg_add (ih _ (by omega)) (ih _ (by omega)), ← add_nsmul]
      congr 2; omega
    · rw [ofVg_add (ofVg_add (ih _ (by omega)) (ih _ (by omega))) hP, ← add_nsmul, ← succ_nsmul]
      congr 2; omega

theorem ofVg_G : ofVg (G C) = p384G := by
  simp only [G, ofVg, C, VG.Spec.P384.curve, p384G]
  rfl

/-- VG's multiples are rind's, of a point on the curve. -/
theorem ofVg_mul_pow {P : Point C} (hP : p384OnCurve (ofVg P)) (k : Nat) :
    ofVg (mul k P) = p384Pow (ofVg P) k := by
  obtain ⟨X, hX⟩ := p384_exists_fromM _ hP
  rw [ofVg_mul hX.symm, ← hX]
  exact (nist.pow_fromM X k).symm

theorem onCurve_ofVg_mul {P : Point C} (hP : p384OnCurve (ofVg P)) (k : Nat) :
    p384OnCurve (ofVg (mul k P)) := by
  obtain ⟨X, hX⟩ := p384_exists_fromM _ hP
  rw [ofVg_mul hX.symm]
  exact nist.onCurve_fromM _

/-- rind's multiples of a point on the curve are on it. -/
theorem pow_onCurve (P : nist.Point) (hP : p384OnCurve P) (k : Nat) : p384OnCurve (p384Pow P k) := by
  obtain ⟨X, hX⟩ := p384_exists_fromM _ hP
  rw [← hX]
  show p384OnCurve (nist.pow p384 (nist.fromM X) k)
  rw [nist.pow_fromM]
  exact nist.onCurve_fromM _

theorem ofVg_G_onCurve : p384OnCurve (ofVg (G C)) := ofVg_G ▸ p384OnCurve_G

theorem ofVg_mul_G (k : Nat) : ofVg (mul k (G C)) = p384Pow p384G k := by
  rw [ofVg_mul_pow ofVg_G_onCurve, ofVg_G]

/-! ## Octet strings -/

theorem foldl_ofBytes (l : List VG.Byte) (a : Nat) :
    l.foldl (fun acc b => 256 * acc + b.toNat) a =
      a * 256 ^ l.length + l.foldl (fun acc b => 256 * acc + b.toNat) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (256 * 0 + b.toNat), List.length_cons]
    ring

theorem ofBytes_cons (b : VG.Byte) (l : List VG.Byte) :
    ofBytes (b :: l) = b.toNat * 256 ^ l.length + ofBytes l := by
  simp only [ofBytes, List.foldl_cons]
  rw [foldl_ofBytes]
  ring

/-- VG's octet strings read as `beNat` reads rind's. -/
theorem ofBytes_bv (l : List U8) : ofBytes (l.map (·.bv)) = beNat l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : beNat [b] = b.val := by simp [beNat, leNat, Nat.ofDigits]
    rw [List.map_cons, ofBytes_cons, ih, List.length_map,
      show b :: l = [b] ++ l from rfl, beNat_append, hb]
    rfl

theorem length_toBytes (len x : Nat) : (toBytes len x).length = len := by
  simp [toBytes]

theorem toBytes_succ (len x : Nat) :
    toBytes (len + 1) x = BitVec.ofNat 8 (x >>> (8 * len)) :: toBytes len x := by
  simp [toBytes, List.range_succ]

theorem ofBytes_toBytes (len x : Nat) : ofBytes (toBytes len x) = x % 256 ^ len := by
  induction len with
  | zero => simp [toBytes, ofBytes, Nat.mod_one]
  | succ len ih =>
    have h8 : (2 : Nat) ^ (8 * len) = 256 ^ len := by rw [pow_mul]; norm_num
    rw [toBytes_succ, ofBytes_cons, length_toBytes, ih, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, h8, show (2 : Nat) ^ 8 = 256 by norm_num, Nat.mod_pow_succ]
    ring

theorem ofBytes_toBytes_lt (len x : Nat) (h : x < 256 ^ len) : ofBytes (toBytes len x) = x := by
  rw [ofBytes_toBytes, Nat.mod_eq_of_lt h]

theorem lt_256_48 (a : Fin C.p) : a.val < 256 ^ 48 :=
  lt_trans (lt_of_lt_of_eq a.isLt p_eq) (by simp [p384])

theorem bv_inj {a b : U8} (h : a.bv = b.bv) : a = b := by
  cases a; cases b; simp_all

theorem slice_map {α β : Type _} (f : α → β) (l : List α) (a b : Nat) :
    (l.map f).slice a b = (l.slice a b).map f := by
  simp [List.slice, List.map_take, List.map_drop]

/-- VG's encoding of a point, as rind's spec reads it. -/
theorem encode_affine (x y : Fin C.p) (out : List U8)
    (h : out.map (·.bv) = VG.Spec.EcKey.encodePoint (.affine x y)) :
    out.head? = some 4#u8 ∧ beNat (out.slice 1 49) = x.val ∧ beNat (out.slice 49 97) = y.val := by
  simp only [VG.Spec.EcKey.encodePoint] at h
  have hx := length_toBytes 48 x.val
  have hy := length_toBytes 48 y.val
  refine ⟨?_, ?_, ?_⟩
  · cases out with
    | nil => simp at h
    | cons o rest =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.head?_cons, Option.some.injEq]
      exact bv_inj h.1
  · rw [← ofBytes_bv, ← slice_map, h]
    have : (4 :: (toBytes C.len x.val ++ toBytes C.len y.val)).slice 1 49 = toBytes 48 x.val := by
      simp only [List.slice, List.drop_succ_cons, List.drop_zero]
      exact List.take_left' hx
    rw [this, ofBytes_toBytes_lt _ _ (lt_256_48 x)]
  · rw [← ofBytes_bv, ← slice_map, h]
    have : (4 :: (toBytes C.len x.val ++ toBytes C.len y.val)).slice 49 97 = toBytes 48 y.val := by
      simp only [List.slice, List.drop_succ_cons]
      rw [show C.len = 48 from rfl, List.drop_left' hx, List.take_of_length_le (by simp [hy])]
    rw [this, ofBytes_toBytes_lt _ _ (lt_256_48 y)]

/-- The coordinates rind reads from an encoded point. -/
def coords (b : List U8) : Nat × Nat := (beNat (b.slice 1 49), beNat (b.slice 49 97))

/-- VG's validation of a public key is rind's. -/
theorem decode_bv (b : List U8) (hl : b.length = 97) (h4 : b.head? = some 4#u8) :
    match VG.Spec.EcKey.decodePublicKey C (b.map (·.bv)) with
    | some Q => p384OnCurve (some (coords b)) ∧ ofVg Q = some (coords b)
    | none => ¬ p384OnCurve (some (coords b)) := by
  have hd1 : ofBytes (((b.map (·.bv)).drop 1).take C.len) = (coords b).1 := by
    rw [coords, ← ofBytes_bv, ← slice_map]; rfl
  have hd2 : ofBytes ((b.map (·.bv)).drop (C.len + 1)) = (coords b).2 := by
    have h1 : b.slice 49 97 = b.drop 49 := by simp [List.slice, List.take_of_length_le, hl]
    have h2 : ofBytes ((b.map (·.bv)).drop (C.len + 1)) = ofBytes ((b.drop 49).map (·.bv)) := by
      rw [List.map_drop]; rfl
    rw [h2, ofBytes_bv, coords, h1]
  have hhead : (b.map (·.bv)).head? = some 4 := by
    rw [List.head?_map, h4]; rfl
  unfold VG.Spec.EcKey.decodePublicKey
  rw [if_pos ⟨by simp only [List.length_map, hl]; rfl, hhead⟩]
  simp only [hd1, hd2]
  split_ifs with hlt hc
  · have := (onCurve_iff _ _).mp hc
    exact ⟨this, rfl⟩
  · intro hon
    exact hc ((onCurve_iff ⟨_, hlt.1⟩ ⟨_, hlt.2⟩).mpr hon)
  · rintro ⟨hx, hy, -⟩
    exact hlt ⟨p_eq ▸ hx, p_eq ▸ hy⟩

/-! ## The operations -/

/-- VG's public key of a scalar in [1, n). -/
theorem publicKey_eq (d : Nat) (hd0 : 0 < d) (hd : d < n384) :
    ∃ x y : Fin C.p, VG.Spec.EcKey.publicKey C d = some (.affine x y) ∧
      p384Pow p384G d = some (x.val, y.val) := by
  have hm := ofVg_mul_G d
  obtain ⟨x, y, hq, -⟩ := p384_g_mult d hd0 hd
  unfold VG.Spec.EcKey.publicKey
  rw [if_pos ⟨hd0, n_eq ▸ hd⟩]
  rcases hP : mul d (G C) with _ | ⟨x', y'⟩
  · rw [hP, hq] at hm; cases hm
  · rw [hP] at hm
    exact ⟨x', y', rfl, by rw [← ofVg_mul_G, hP]; rfl⟩

theorem nBits_eq : VG.Spec.Ecdsa.nBits C = 384 := by
  unfold VG.Spec.Ecdsa.nBits
  rw [Nat.log2_eq_iff (by simp [C, VG.Spec.P384.curve, VG.Spec.P384.n]) |>.mpr]
  simp only [C, VG.Spec.P384.curve, VG.Spec.P384.n]
  constructor <;> decide +kernel

/-- VG's integer of a 48-byte hash is its bytes'. -/
theorem hashToInt_48 (b : List U8) (hl : b.length = 48) :
    VG.Spec.Ecdsa.hashToInt C (b.map (·.bv)) = beNat b := by
  unfold VG.Spec.Ecdsa.hashToInt
  rw [nBits_eq, if_pos (by simp [hl]), ofBytes_bv]

/-- A scalar of VG's spec in `ZMod n384`. -/
def sc (a : Fin C.n) : ZMod n384 := (a.val : ZMod n384)

theorem natCast_mod_n (k : Nat) : ((k % C.n : Nat) : ZMod n384) = k := by
  rw [n_eq, ZMod.natCast_mod]

theorem sc_val (a : Fin C.n) : (sc a).val = a.val := by
  unfold sc
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (n_eq ▸ a.isLt)]

theorem sc_mul (a b : Fin C.n) : sc (a * b) = sc a * sc b := by
  simp only [sc, Fin.val_mul, natCast_mod_n, Nat.cast_mul]

theorem sc_ofNat (k : Nat) : sc (Fin.ofNat C.n k) = k := by
  simp only [sc, Fin.val_ofNat, natCast_mod_n]

theorem sc_one : sc (1 : Fin C.n) = 1 := by
  show sc (Fin.ofNat C.n 1) = 1
  rw [sc_ofNat, Nat.cast_one]

theorem sc_pow (a : Fin C.n) (e : Nat) : sc (pow a e) = sc a ^ e := by
  induction e using Nat.strong_induction_on generalizing a with
  | _ e ih =>
    rw [pow]
    split_ifs with h0 h2
    · subst h0; rw [sc_one, _root_.pow_zero]
    · rw [ih _ (by omega), sc_mul, ← sq, ← pow_mul]
      congr 1; omega
    · rw [sc_mul, ih _ (by omega), sc_mul, ← sq, ← pow_mul, ← pow_succ']
      congr 1; omega

/-- VG's ECDSA verification is FIPS 186-5's, as rind's spec states it, for a
point on the curve. -/
theorem verifyWith_iff (Q : Point C) (hQ : p384OnCurve (ofVg Q)) (e r s : Nat) :
    VG.Spec.Ecdsa.verifyWith C Q e r s = true ↔ ecdsaP384Verifies (ofVg Q) e r s := by
  unfold VG.Spec.Ecdsa.verifyWith
  simp only [ecdsaP384Verifies, nist.ecdsaVerifies]
  by_cases hr : 1 ≤ r ∧ r < C.n ∧ 1 ≤ s ∧ s < C.n
  · rw [if_pos hr]
    obtain ⟨hr1, hrn, hs1, hsn⟩ := hr
    rw [n_eq] at hrn hsn
    have hw : sc (pow (Fin.ofNat C.n s) (C.n - 2)) = (s : ZMod n384)⁻¹ := by
      rw [sc_pow, sc_ofNat, n_eq, pow_sub_two_eq_inv (by simp [n384])]
    have hu : (Fin.ofNat C.n e * pow (Fin.ofNat C.n s) (C.n - 2)).val =
        ((e : ZMod n384) * (s : ZMod n384)⁻¹).val := by
      rw [← sc_val, sc_mul, sc_ofNat, hw]
    have hv : (Fin.ofNat C.n r * pow (Fin.ofNat C.n s) (C.n - 2)).val =
        ((r : ZMod n384) * (s : ZMod n384)⁻¹).val := by
      rw [← sc_val, sc_mul, sc_ofNat, hw]
    obtain ⟨XG, hXG⟩ := p384_exists_fromM _ ofVg_G_onCurve
    obtain ⟨XQ, hXQ⟩ := p384_exists_fromM _ hQ
    have hadd := ofVg_add (ofVg_mul hXG.symm (Fin.ofNat C.n e * pow (Fin.ofNat C.n s) (C.n - 2)).val)
      (ofVg_mul hXQ.symm (Fin.ofNat C.n r * pow (Fin.ofNat C.n s) (C.n - 2)).val)
    rw [← nist.fromM_add, ← nist.pow_fromM, ← nist.pow_fromM, hXG, hXQ, ofVg_G, hu, hv] at hadd
    simp only [show (0 < r) = (1 ≤ r) from rfl, show (0 < s) = (1 ≤ s) from rfl, hr1, hrn, hs1, hsn,
      true_and]
    rw [hu, hv, ← hadd]
    generalize add (mul ((e : ZMod n384) * (s : ZMod n384)⁻¹).val (G C))
      (mul ((r : ZMod n384) * (s : ZMod n384)⁻¹).val Q) = R
    rcases R with _ | ⟨x, y⟩
    · simp [ofVg]
    · simp [ofVg, n_eq]
  · rw [if_neg hr]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨h1, h2, h3, h4, -⟩
    exact hr ⟨h1, n_eq ▸ h2, h3, n_eq ▸ h4⟩

end rind.spec.vgP384
