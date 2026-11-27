import Rind.NistGroup
import Mathlib.FieldTheory.Finite.Basic
import Rind.Bytes
import VerifiedGarbage.Spec.EcKey
import VerifiedGarbage.Spec.Ecdsa.Verify
open Aeneas Aeneas.Std rind.spec VG.Spec.Weierstrass

/-!
# pyca/verified-garbage's NIST curves are rind's

VG's contracts for its P-256 and P-384 routines state their results over its
own transcription of SEC 1 and FIPS 186-5 (`VG.Spec.Weierstrass`,
`VG.Spec.EcKey`, and `VG.Spec.Ecdsa`), which `admin/import-vg-models`
vendors. This proves that, for a VG curve that `Matches` one of rind's NIST
curves, they are what rind's theorems state over HOL Light's
(`Rind/Spec.lean`): VG's points, read as `ofVg`, add as `nist.add` and
multiply as `nist.pow`, through Mathlib's group of points (`Rind.NistGroup`);
its key validation is `nist.OnCurve`; its octet strings are `beNat`'s; and
its ECDSA verification is `nist.ecdsaVerifies`. `Rind/VgP256.lean` and
`Rind/VgP384.lean` prove each curve matches.
-/

namespace rind.spec.vgNist

/-- Fermat's little theorem, as VG's spec takes inverses. -/
theorem pow_sub_two_eq_inv {q : Nat} [Fact q.Prime] (hq : 2 < q) (a : ZMod q) : a ^ (q - 2) = a⁻¹ := by
  by_cases ha : a = 0
  · subst ha; rw [zero_pow (by omega), inv_zero]
  · apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show q - 2 + 1 = q - 1 by omega, ZMod.pow_card_sub_one_eq_one ha]

/-- A point of VG's spec as `Rind/Spec.lean` writes it. -/
def ofVg {C : Curve} : Point C → nist.Point
  | .infinity => none
  | .affine x y => some (x.val, y.val)

/-- VG's curve `C` is rind's y² = x³ - 3x + b over the prime `p`, with the
generator `g` on it, whose multiples by [1, n) are finite points of it, and its
encodings' `C.len` bytes hold a field element and a hash's leftmost bits. -/
structure Matches (C : Curve) (p n b : Nat) (g : nist.Point) : Prop where
  p_eq : C.p = p
  n_eq : C.n = n
  a_eq : C.a = p - 3
  b_eq : C.b = b
  g_eq : ofVg (G C) = g
  g_on : nist.OnCurve p b g
  b_ne : (b + 2) % p ≠ 0 ∧ (b + (p - 2)) % p ≠ 0
  p_le : p ≤ 256 ^ C.len
  hash_bits : 8 * C.len ≤ VG.Spec.Ecdsa.nBits C
  g_mult : ∀ k, 0 < k → k < n → ∃ x y, nist.pow p g k = some (x, y) ∧ nist.OnCurve p b (some (x, y))

/-- A field element of VG's spec in `ZMod p`. -/
def fe {C : Curve} (p : Nat) (a : Fin C.p) : ZMod p := (a.val : ZMod p)

/-- A scalar of VG's spec in `ZMod n`. -/
def sc {C : Curve} (n : Nat) (a : Fin C.n) : ZMod n := (a.val : ZMod n)

/-- The coordinates rind reads from an encoded point of `C`. -/
def coords (C : Curve) (bs : List U8) : Nat × Nat :=
  (beNat (bs.slice 1 (C.len + 1)), beNat (bs.slice (C.len + 1) (2 * C.len + 1)))

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
    have hb : beNat [b] = b.val := by simp [beNat, leNat]
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

theorem bv_inj {a b : U8} (h : a.bv = b.bv) : a = b := by
  cases a; cases b; simp_all

theorem slice_map {α β : Type _} (f : α → β) (l : List α) (a b : Nat) :
    (l.map f).slice a b = (l.slice a b).map f := by
  simp [List.slice, List.map_take, List.map_drop]

section

variable {C : Curve} {p n b : Nat} {g : nist.Point} (hM : Matches C p n b g)
include hM

/-! ## VG's field elements in `ZMod p` -/

theorem natCast_mod_p (k : Nat) : ((k % C.p : Nat) : ZMod p) = k := by
  rw [hM.p_eq, ZMod.natCast_mod]

theorem natCast_p : ((C.p : Nat) : ZMod p) = 0 := by
  rw [hM.p_eq]; exact ZMod.natCast_self _

theorem fe_val (a : Fin C.p) : (fe p a).val = a.val := by
  unfold fe
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_eq a.isLt hM.p_eq)]

theorem fe_inj {a c : Fin C.p} : fe p a = fe p c ↔ a = c := by
  constructor
  · intro h
    exact Fin.ext (by rw [← fe_val hM a, ← fe_val hM c, h])
  · rintro rfl; rfl

theorem fe_add (a c : Fin C.p) : fe p (a + c) = fe p a + fe p c := by
  simp only [fe, Fin.val_add, natCast_mod_p hM, Nat.cast_add]

theorem fe_mul (a c : Fin C.p) : fe p (a * c) = fe p a * fe p c := by
  simp only [fe, Fin.val_mul, natCast_mod_p hM, Nat.cast_mul]

theorem fe_neg (a : Fin C.p) : fe p (-a) = -fe p a := by
  have hl : a.val ≤ C.p := a.isLt.le
  simp only [fe, Fin.val_neg', natCast_mod_p hM]
  rw [Nat.cast_sub hl, natCast_p hM, zero_sub]

theorem fe_sub (a c : Fin C.p) : fe p (a - c) = fe p a - fe p c := by
  rw [sub_eq_add_neg a c, fe_add hM, fe_neg hM, sub_eq_add_neg]

theorem fe_ofNat (k : Nat) : fe p (Fin.ofNat C.p k) = k := by
  simp only [fe, Fin.val_ofNat, natCast_mod_p hM]

theorem fe_two : fe p (2 : Fe C) = 2 := by
  show fe p (Fin.ofNat C.p 2) = 2
  rw [fe_ofNat hM]; norm_num

theorem fe_three : fe p (3 : Fe C) = 3 := by
  show fe p (Fin.ofNat C.p 3) = 3
  rw [fe_ofNat hM]; norm_num

theorem fe_one : fe p (1 : Fin C.p) = 1 := by
  show fe p (Fin.ofNat C.p 1) = 1
  rw [fe_ofNat hM, Nat.cast_one]

theorem fe_pow (a : Fin C.p) (e : Nat) : fe p (pow a e) = fe p a ^ e := by
  induction e using Nat.strong_induction_on generalizing a with
  | _ e ih =>
    rw [pow]
    split_ifs with h0 h2
    · subst h0; rw [fe_one hM, _root_.pow_zero]
    · rw [ih _ (by omega), fe_mul hM, ← sq, ← pow_mul]
      congr 1; omega
    · rw [fe_mul hM, ih _ (by omega), fe_mul hM, ← sq, ← pow_mul, ← pow_succ']
      congr 1; omega

theorem fe_inv [Fact p.Prime] [Fact (3 < p)] (a : Fin C.p) : fe p (inv a) = (fe p a)⁻¹ := by
  have h3 : 3 < p := Fact.out
  unfold inv
  rw [fe_pow hM, show C.p - 2 = p - 2 by rw [hM.p_eq], pow_sub_two_eq_inv (by omega)]

theorem fe_a [Fact (3 < p)] : fe p (Fin.ofNat C.p C.a) = -3 := by
  have h3 : 3 ≤ p := (Fact.out : 3 < p).le
  rw [fe_ofNat hM, hM.a_eq, Nat.cast_sub h3, ZMod.natCast_self]
  simp

theorem fe_b : fe p (Fin.ofNat C.p C.b) = (b : ZMod p) := by
  rw [fe_ofNat hM, hM.b_eq]

/-! ## Points -/

/-- A point of VG's spec with the field element of `ofVg`'s coordinates. -/
theorem ofVg_affine (x y : Fin C.p) : ofVg (.affine x y) = some ((fe p x).val, (fe p y).val) := by
  simp only [ofVg, fe_val hM]

/-- VG's curve equation is rind's. -/
theorem onCurve_iff [Fact (3 < p)] (x y : Fin C.p) : onCurve C (.affine x y) = true ↔ nist.OnCurve p b (ofVg (.affine x y)) := by
  have hx : x.val < p := lt_of_lt_of_eq x.isLt hM.p_eq
  have hy : y.val < p := lt_of_lt_of_eq y.isLt hM.p_eq
  have h3 : 3 ≤ p := (Fact.out : 3 < p).le
  simp only [onCurve, decide_eq_true_eq, ofVg, nist.OnCurve, hx, hy, true_and]
  rw [← fe_inj hM, ← ZMod.natCast_eq_natCast_iff']
  simp only [fe_add hM, fe_mul hM, fe_a hM, fe_b hM, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub h3, ZMod.natCast_self]
  unfold fe
  constructor <;> intro h <;> linear_combination h

/-- VG's addition is the group's, for points of it. -/
theorem ofVg_add [Fact p.Prime] [Fact (3 < p)] {P Q : Point C} {X Y : (nist.curve p b).Point} (hP : ofVg P = nist.fromM X)
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
  simp only [ofVg_affine hM, nist.fromM, Option.some.injEq, Prod.mk.injEq] at hP hQ
  obtain ⟨hu1, hv1⟩ := hP
  obtain ⟨hu2, hv2⟩ := hQ
  rw [ZMod.val_injective _ |>.eq_iff] at hu1 hv1 hu2 hv2
  subst hu1 hv1 hu2 hv2
  rw [ofVg_affine hM, ofVg_affine hM, nist.add_val]
  unfold add
  by_cases hx : x1 = x2
  · subst hx
    by_cases hy : y2 = -y1
    · have hf : fe p y2 = -fe p y1 := by rw [hy, fe_neg hM]
      simp only [hy, and_self, ↓reduceIte, ofVg, nist.addF]
      rw [if_neg]
      rintro ⟨he, h0⟩
      apply h0
      have : 2 * fe p y1 = 0 := by rw [fe_neg hM] at he; linear_combination he
      exact (mul_eq_zero.mp this).resolve_left nist.two_ne_zero'
    · have hyy : fe p y1 = fe p y2 := by
        rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h1.1 h2.1 rfl with h | h
        · exact h
        · exfalso; apply hy
          rw [nist.negY_eq] at h
          rw [← fe_inj hM, fe_neg hM, h, neg_neg]
      have hy0 : fe p y1 ≠ 0 := by
        intro h0; apply hy
        rw [← fe_inj hM, fe_neg hM, ← hyy, h0, neg_zero]
      have hyy' : y1 = y2 := (fe_inj hM).mp hyy
      subst hyy'
      simp only [hy, and_false, ↓reduceIte, ne_eq, not_true_eq_false, ofVg_affine hM, nist.addF,
        hy0, not_false_eq_true, and_self]
      simp only [fe_sub hM, fe_mul hM, fe_add hM, fe_inv hM, fe_a hM, fe_two hM, fe_three hM]
      rw [show 3 * fe p x1 * fe p x1 = 3 * fe p x1 ^ 2 by ring, ← sq]
  · have hfx : fe p x1 ≠ fe p x2 := fun h => hx ((fe_inj hM).mp h)
    simp only [hx, false_and, ↓reduceIte, ne_eq, not_false_eq_true, ofVg_affine hM, nist.addF, hfx]
    simp only [fe_sub hM, fe_mul hM, fe_inv hM]
    congr 3 <;> ring

/-- VG's multiplication is the group's, for points of it. -/
theorem ofVg_mul [Fact p.Prime] [Fact (3 < p)] {P : Point C} {X : (nist.curve p b).Point} (hP : ofVg P = nist.fromM X) (k : Nat) :
    ofVg (mul k P) = nist.fromM (k • X) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [mul]
    split_ifs with h0 h2
    · subst h0; rw [zero_nsmul]; rfl
    · rw [ofVg_add hM (ih _ (by omega)) (ih _ (by omega)), ← add_nsmul]
      congr 2; omega
    · rw [ofVg_add hM (ofVg_add hM (ih _ (by omega)) (ih _ (by omega))) hP, ← add_nsmul, ← succ_nsmul]
      congr 2; omega

/-- Every point on rind's curve is a point of Mathlib's group. -/
theorem exists_fromM [Fact p.Prime] [Fact (3 < p)] (P : nist.Point) (hP : nist.OnCurve p b P) :
    ∃ X : (nist.curve p b).Point, nist.fromM X = P := by
  match P, hP with
  | none, _ => exact ⟨0, rfl⟩
  | some (x, y), h => exact nist.fromM_of_onCurve hM.b_ne.1 hM.b_ne.2 h

/-- VG's multiples are rind's, of a point on the curve. -/
theorem ofVg_mul_pow [Fact p.Prime] [Fact (3 < p)] {P : Point C} (hP : nist.OnCurve p b (ofVg P)) (k : Nat) :
    ofVg (mul k P) = nist.pow p (ofVg P) k := by
  obtain ⟨X, hX⟩ := exists_fromM hM _ hP
  rw [ofVg_mul hM hX.symm, ← hX]
  exact (nist.pow_fromM X k).symm

/-- rind's multiples of a point on the curve are on it. -/
theorem pow_onCurve [Fact p.Prime] [Fact (3 < p)] (P : nist.Point) (hP : nist.OnCurve p b P) (k : Nat) : nist.OnCurve p b (nist.pow p P k) := by
  obtain ⟨X, hX⟩ := exists_fromM hM _ hP
  rw [← hX, nist.pow_fromM]
  exact nist.onCurve_fromM _

theorem g_onCurve : nist.OnCurve p b (ofVg (G C)) := hM.g_eq ▸ hM.g_on

theorem ofVg_mul_G [Fact p.Prime] [Fact (3 < p)] (k : Nat) : ofVg (mul k (G C)) = nist.pow p g k := by
  rw [ofVg_mul_pow hM (g_onCurve hM), hM.g_eq]

/-! ## Octet strings of `C` -/

theorem lt_256 (a : Fin C.p) : a.val < 256 ^ C.len :=
  lt_of_lt_of_le (lt_of_lt_of_eq a.isLt hM.p_eq) hM.p_le

/-- VG's encoding of a point, as rind's spec reads it. -/
theorem encode_affine (x y : Fin C.p) (out : List U8)
    (h : out.map (·.bv) = VG.Spec.EcKey.encodePoint (.affine x y)) :
    out.head? = some 4#u8 ∧ (coords C out).1 = x.val ∧ (coords C out).2 = y.val := by
  simp only [VG.Spec.EcKey.encodePoint] at h
  have hx := length_toBytes C.len x.val
  have hy := length_toBytes C.len y.val
  refine ⟨?_, ?_, ?_⟩
  · cases out with
    | nil => simp at h
    | cons o rest =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.head?_cons, Option.some.injEq]
      exact bv_inj h.1
  · show beNat (out.slice 1 (C.len + 1)) = x.val
    rw [← ofBytes_bv, ← slice_map, h]
    have : (4 :: (toBytes C.len x.val ++ toBytes C.len y.val)).slice 1 (C.len + 1) = toBytes C.len x.val := by
      simp only [List.slice, List.drop_succ_cons, List.drop_zero, Nat.add_sub_cancel]
      exact List.take_left' hx
    rw [this, ofBytes_toBytes_lt _ _ (lt_256 hM x)]
  · show beNat (out.slice (C.len + 1) (2 * C.len + 1)) = y.val
    rw [← ofBytes_bv, ← slice_map, h]
    have : (4 :: (toBytes C.len x.val ++ toBytes C.len y.val)).slice (C.len + 1) (2 * C.len + 1) =
        toBytes C.len y.val := by
      simp only [List.slice, List.drop_succ_cons]
      rw [List.drop_left' hx, List.take_of_length_le (by rw [hy]; omega)]
    rw [this, ofBytes_toBytes_lt _ _ (lt_256 hM y)]

/-- VG's validation of a public key is rind's. -/
theorem decode_bv [Fact (3 < p)] (bs : List U8) (hl : bs.length = 2 * C.len + 1) (h4 : bs.head? = some 4#u8) :
    match VG.Spec.EcKey.decodePublicKey C (bs.map (·.bv)) with
    | some Q => nist.OnCurve p b (some (coords C bs)) ∧ ofVg Q = some (coords C bs)
    | none => ¬ nist.OnCurve p b (some (coords C bs)) := by
  have hd1 : ofBytes (((bs.map (·.bv)).drop 1).take C.len) = (coords C bs).1 := by
    rw [coords, ← ofBytes_bv, ← slice_map]
    simp only [List.slice, Nat.add_sub_cancel]
  have hd2 : ofBytes ((bs.map (·.bv)).drop (C.len + 1)) = (coords C bs).2 := by
    have h1 : bs.slice (C.len + 1) (2 * C.len + 1) = bs.drop (C.len + 1) := by
      simp only [List.slice]
      exact List.take_of_length_le (by simp only [List.length_drop, hl]; omega)
    show _ = beNat (bs.slice (C.len + 1) (2 * C.len + 1))
    rw [h1, ← ofBytes_bv, List.map_drop]
  have hhead : (bs.map (·.bv)).head? = some 4 := by
    rw [List.head?_map, h4]; rfl
  unfold VG.Spec.EcKey.decodePublicKey
  rw [if_pos ⟨by simp only [List.length_map, hl], hhead⟩]
  simp only [hd1, hd2]
  split_ifs with hlt hc
  · have := (onCurve_iff hM _ _).mp hc
    exact ⟨this, rfl⟩
  · intro hon
    exact hc ((onCurve_iff hM ⟨_, hlt.1⟩ ⟨_, hlt.2⟩).mpr hon)
  · rintro ⟨hx, hy, -⟩
    exact hlt ⟨hM.p_eq ▸ hx, hM.p_eq ▸ hy⟩

/-! ## The operations -/

/-- VG's public key of a scalar in [1, n). -/
theorem publicKey_eq [Fact p.Prime] [Fact (3 < p)] (d : Nat) (hd0 : 0 < d) (hd : d < n) :
    ∃ x y : Fin C.p, VG.Spec.EcKey.publicKey C d = some (.affine x y) ∧
      nist.pow p g d = some (x.val, y.val) := by
  have hm := ofVg_mul_G hM d
  obtain ⟨x, y, hq, -⟩ := hM.g_mult d hd0 hd
  unfold VG.Spec.EcKey.publicKey
  rw [if_pos ⟨hd0, hM.n_eq ▸ hd⟩]
  rcases hP : mul d (G C) with _ | ⟨x', y'⟩
  · rw [hP, hq] at hm; cases hm
  · rw [hP] at hm
    exact ⟨x', y', rfl, by rw [← ofVg_mul_G hM, hP]; rfl⟩

/-- VG's integer of a hash of `C.len` bytes is its bytes'. -/
theorem hashToInt_len (bs : List U8) (hl : bs.length = C.len) :
    VG.Spec.Ecdsa.hashToInt C (bs.map (·.bv)) = beNat bs := by
  unfold VG.Spec.Ecdsa.hashToInt
  rw [if_pos (by simp only [List.length_map, hl]; exact hM.hash_bits), ofBytes_bv]

end

section

variable {C : Curve} {p n b : Nat} {g : nist.Point} (hM : Matches C p n b g)
include hM

theorem natCast_mod_n (k : Nat) : ((k % C.n : Nat) : ZMod n) = k := by
  rw [hM.n_eq, ZMod.natCast_mod]

theorem sc_val (a : Fin C.n) : (sc n a).val = a.val := by
  unfold sc
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hM.n_eq ▸ a.isLt)]

theorem sc_mul (a c : Fin C.n) : sc n (a * c) = sc n a * sc n c := by
  simp only [sc, Fin.val_mul, natCast_mod_n hM, Nat.cast_mul]

theorem sc_ofNat (k : Nat) : sc n (Fin.ofNat C.n k) = k := by
  simp only [sc, Fin.val_ofNat, natCast_mod_n hM]

theorem sc_one : sc n (1 : Fin C.n) = 1 := by
  show sc n (Fin.ofNat C.n 1) = 1
  rw [sc_ofNat hM, Nat.cast_one]

theorem sc_pow (a : Fin C.n) (e : Nat) : sc n (pow a e) = sc n a ^ e := by
  induction e using Nat.strong_induction_on generalizing a with
  | _ e ih =>
    rw [pow]
    split_ifs with h0 h2
    · subst h0; rw [sc_one hM, _root_.pow_zero]
    · rw [ih _ (by omega), sc_mul hM, ← sq, ← pow_mul]
      congr 1; omega
    · rw [sc_mul hM, ih _ (by omega), sc_mul hM, ← sq, ← pow_mul, ← pow_succ']
      congr 1; omega

/-- VG's ECDSA verification is FIPS 186-5's, as rind's spec states it, for a
point on the curve. -/
theorem verifyWith_iff [Fact p.Prime] [Fact (3 < p)] [Fact n.Prime] (hn : 2 < n) (Q : Point C) (hQ : nist.OnCurve p b (ofVg Q)) (e r s : Nat) :
    VG.Spec.Ecdsa.verifyWith C Q e r s = true ↔ nist.ecdsaVerifies p n g (ofVg Q) e r s := by
  unfold VG.Spec.Ecdsa.verifyWith
  simp only [nist.ecdsaVerifies]
  by_cases hr : 1 ≤ r ∧ r < C.n ∧ 1 ≤ s ∧ s < C.n
  · rw [if_pos hr]
    obtain ⟨hr1, hrn, hs1, hsn⟩ := hr
    rw [hM.n_eq] at hrn hsn
    have hw : sc n (pow (Fin.ofNat C.n s) (C.n - 2)) = (s : ZMod n)⁻¹ := by
      rw [sc_pow hM, sc_ofNat hM, show C.n - 2 = n - 2 by rw [hM.n_eq], pow_sub_two_eq_inv hn]
    have hu : (Fin.ofNat C.n e * pow (Fin.ofNat C.n s) (C.n - 2)).val =
        ((e : ZMod n) * (s : ZMod n)⁻¹).val := by
      rw [← sc_val hM, sc_mul hM, sc_ofNat hM, hw]
    have hv : (Fin.ofNat C.n r * pow (Fin.ofNat C.n s) (C.n - 2)).val =
        ((r : ZMod n) * (s : ZMod n)⁻¹).val := by
      rw [← sc_val hM, sc_mul hM, sc_ofNat hM, hw]
    obtain ⟨XG, hXG⟩ := exists_fromM hM _ (g_onCurve hM)
    obtain ⟨XQ, hXQ⟩ := exists_fromM hM _ hQ
    have hadd := ofVg_add hM (ofVg_mul hM hXG.symm (Fin.ofNat C.n e * pow (Fin.ofNat C.n s) (C.n - 2)).val)
      (ofVg_mul hM hXQ.symm (Fin.ofNat C.n r * pow (Fin.ofNat C.n s) (C.n - 2)).val)
    rw [← nist.fromM_add, ← nist.pow_fromM, ← nist.pow_fromM, hXG, hXQ, hM.g_eq, hu, hv] at hadd
    simp only [show (0 < r) = (1 ≤ r) from rfl, show (0 < s) = (1 ≤ s) from rfl, hr1, hrn, hs1, hsn,
      true_and]
    rw [hu, hv, ← hadd]
    generalize add (mul ((e : ZMod n) * (s : ZMod n)⁻¹).val (G C))
      (mul ((r : ZMod n) * (s : ZMod n)⁻¹).val Q) = R
    rcases R with _ | ⟨x, y⟩
    · simp [ofVg]
    · simp [ofVg, hM.n_eq]
  · rw [if_neg hr]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨h1, h2, h3, h4, -⟩
    exact hr ⟨h1, hM.n_eq ▸ h2, h3, hM.n_eq ▸ h4⟩

end

end rind.spec.vgNist
