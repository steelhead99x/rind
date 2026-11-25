import Rind.SpecTest.Upstream
import Mathlib.FieldTheory.Finite.Basic

/-!
# Ed25519's decoding, computed

`edDecode` picks a point by Hilbert's choice. `decodeC` computes RFC 8032
section 5.1.3's decoding: x² = (y² - 1) / (d y² + 1), its square root by the
exponent (p + 3) / 8 and, when that squares to -x², times √-1, and the root of
the encoding's sign. `decodeC_valid` proves it `edDecode` on every valid
encoding, and `decodeC_none` that it refuses every other, from Fermat's
little theorem, for which `p25519_prime` proves p prime by a Pratt
certificate.

The spec's signing and verification take `edPow` and `edMul`, which are
opaque, so `publicKeyWith`, `signWith`, and `verifiesWith` restate them over
any group operations, proven to be them at `edPow` and `edMul`; the spec
tests (`Rind.SpecTest.Server`) run them over `Rind.SpecTest.Upstream`'s.
-/

open Aeneas Aeneas.Std

namespace rind.spec

namespace p25519Prime

theorem prime_1923133 : Nat.Prime 1923133 :=
  prime_of_lucas 2 [(2, 2), (3, 1), (43, 1), (3727, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_31757755568855353 : Nat.Prime 31757755568855353 :=
  prime_of_lucas 10 [(2, 3), (3, 1), (31, 1), (107, 1), (223, 1), (4153, 1), (430751, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_2773320623 : Nat.Prime 2773320623 :=
  prime_of_lucas 5 [(2, 1), (2437, 1), (569003, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_72106336199 : Nat.Prime 72106336199 :=
  prime_of_lucas 7 [(2, 1), (13, 1), (2773320623, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, prime_2773320623, trivial⟩

theorem prime_8574133 : Nat.Prime 8574133 :=
  prime_of_lucas 2 [(2, 2), (3, 1), (7, 1), (103, 1), (991, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, trivial⟩

theorem prime_1919519569386763 : Nat.Prime 1919519569386763 :=
  prime_of_lucas 2 [(2, 1), (3, 1), (7, 1), (19, 1), (47, 2), (127, 1), (8574133, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_8574133, trivial⟩

theorem prime_75445702479781427272750846543864801 : Nat.Prime 75445702479781427272750846543864801 :=
  prime_of_lucas 7 [(2, 5), (3, 2), (5, 2), (75707, 1), (72106336199, 1), (1919519569386763, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_72106336199, prime_1919519569386763, trivial⟩

theorem prime_74058212732561358302231226437062788676166966415465897661863160754340907 : Nat.Prime 74058212732561358302231226437062788676166966415465897661863160754340907 :=
  prime_of_lucas 2 [(2, 1), (3, 1), (353, 1), (57467, 1), (132049, 1), (1923133, 1), (31757755568855353, 1), (75445702479781427272750846543864801, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_1923133, prime_31757755568855353, prime_75445702479781427272750846543864801, trivial⟩

theorem prime_57896044618658097711785492504343953926634992332820282019728792003956564819949 : Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949 :=
  prime_of_lucas 2 [(2, 2), (3, 1), (65147, 1), (74058212732561358302231226437062788676166966415465897661863160754340907, 1)]
    (by decide +kernel)
    ⟨by norm_num, by norm_num, by norm_num, prime_74058212732561358302231226437062788676166966415465897661863160754340907, trivial⟩

end p25519Prime

theorem p25519_prime : Nat.Prime p25519 := by
  rw [show p25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949 by
    simp [p25519]]
  exact p25519Prime.prime_57896044618658097711785492504343953926634992332820282019728792003956564819949

instance : Fact (Nat.Prime p25519) := ⟨p25519_prime⟩

instance : DecidablePred edOnCurve := fun P => by unfold edOnCurve; infer_instance

/-- A square root of -1 mod p: 2^((p - 1) / 4). -/
def sqrtM1 : Nat := 19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- The point RFC 8032 section 5.1.3 decodes `n` to, before its checks. -/
def edCandidate (n : Nat) : EdPoint :=
  let p := p25519
  let y := n % 2 ^ 255
  let u := (y * y + (p - 1)) % p
  let v := (d25519 * (y * y % p) + 1) % p
  let w := u * nist.invC p v % p
  let r := powMod p 256 w ((p + 3) / 8)
  let x0 := if r * r % p = w then r else r * sqrtM1 % p
  let x := if x0 % 2 = n / 2 ^ 255 % 2 then x0 else (p - x0) % p
  ((x : Int), (y : Int))

/-- `edDecode`, computed: the candidate, if it is a point of the group that
encodes as `n`. -/
def decodeC (n : Nat) : Option EdPoint :=
  let P := edCandidate n
  if edOnCurve P ∧ edEncode P = n then some P else none

local notation "Fp" => ZMod p25519

theorem p25519_odd : p25519 % 2 = 1 := by decide

theorem p25519_lt : p25519 < 2 ^ 255 := by decide

theorem cast_eq_of_emod {a b : Int} (h : a % (p25519 : Int) = b % (p25519 : Int)) : (a : Fp) = b :=
  (ZMod.intCast_eq_intCast_iff' a b p25519).mpr h

/-- A point's coordinates satisfy the curve's equation in the field. -/
theorem onCurve_eq {x y : Int} (h : edOnCurve (x, y)) :
    -(x : Fp) ^ 2 + (y : Fp) ^ 2 = 1 + (d25519 : Fp) * (x : Fp) ^ 2 * (y : Fp) ^ 2 := by
  have := cast_eq_of_emod h.2.2.2.2
  push_cast at this
  have he : (e25519 : Fp) = -1 := by
    have h1 : (e25519 : Fp) + 1 = 0 := by
      rw [show (e25519 : Fp) + 1 = ((e25519 + 1 : Nat) : Fp) by push_cast; rfl,
        show e25519 + 1 = p25519 by decide, ZMod.natCast_self]
    linear_combination h1
  rw [he] at this
  linear_combination this

theorem d_ne : (d25519 : Fp) + 1 ≠ 0 := by
  intro h
  have h' : ((d25519 + 1 : Nat) : Fp) = 0 := by push_cast; exact h
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at h'
  exact absurd h' (by decide)

/-- `d y² + 1` is never zero on the curve: it would make `y² = 1`, and `d = -1`. -/
theorem v_ne {x y : Fp} (h : -x ^ 2 + y ^ 2 = 1 + d25519 * x ^ 2 * y ^ 2) : (d25519 : Fp) * y ^ 2 + 1 ≠ 0 := by
  intro hv
  have hy : y ^ 2 = 1 := by linear_combination h + x ^ 2 * hv
  exact d_ne (by rw [hy] at hv; linear_combination hv)

/-- On the curve, x² is (y² - 1) / (d y² + 1). -/
theorem x_sq {x y : Fp} (h : -x ^ 2 + y ^ 2 = 1 + d25519 * x ^ 2 * y ^ 2) :
    x ^ 2 = (y ^ 2 - 1) * ((d25519 : Fp) * y ^ 2 + 1)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq₀ (v_ne h)]
  linear_combination -h

/-- Two field elements with the same square are equal or opposite. -/
theorem sq_eq {a b : Fp} (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b := by
  have : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h
  · left; linear_combination h
  · right; linear_combination h

/-- Numbers below p with equal or opposite residues and the same parity are
equal. -/
theorem eq_of_sq {a b : Nat} (ha : a < p25519) (hb : b < p25519) (hab : (a : Fp) ^ 2 = (b : Fp) ^ 2)
    (hpar : a % 2 = b % 2) : a = b := by
  rcases sq_eq hab with h | h
  · have := (ZMod.natCast_eq_natCast_iff' a b p25519).mp h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · have h0 : ((a + b : Nat) : Fp) = 0 := by push_cast; linear_combination h
    obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).mp h0
    have := p25519_odd
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith

/-- Two points of the group with the same encoding are the same point. -/
theorem encode_inj {P Q : EdPoint} (hP : edOnCurve P) (hQ : edOnCurve Q) (h : edEncode P = edEncode Q) :
    P = Q := by
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  have e1 := onCurve_eq hP
  have e2 := onCurve_eq hQ
  obtain ⟨hx1, hx1', hy1, hy1', -⟩ := hP
  obtain ⟨hx2, hx2', hy2, hy2', -⟩ := hQ
  simp only [edEncode, edModEncode, Int.emod_eq_of_lt hx1 hx1', Int.emod_eq_of_lt hx2 hx2',
    Int.emod_eq_of_lt hy1 hy1', Int.emod_eq_of_lt hy2 hy2'] at h
  have hlt := p25519_lt
  have hy : y1.toNat = y2.toNat := by omega
  have hpar : x1.toNat % 2 = x2.toNat % 2 := by omega
  have hy' : y1 = y2 := by omega
  subst hy'
  have hx : x1.toNat = x2.toNat := by
    apply eq_of_sq (by omega) (by omega) _ hpar
    have c1 : ((x1.toNat : Int) : Fp) = (x1 : Fp) := by rw [Int.toNat_of_nonneg hx1]
    have c2 : ((x2.toNat : Int) : Fp) = (x2 : Fp) := by rw [Int.toNat_of_nonneg hx2]
    push_cast at c1 c2
    rw [c1, c2, x_sq e1, x_sq e2]
  congr 1; omega

theorem decodeC_sound {n : Nat} {P : EdPoint} (h : decodeC n = some P) : edDecode n = P := by
  dsimp only [decodeC] at h
  split_ifs at h with hc
  cases h
  have hs := Classical.epsilon_spec (p := fun P => edOnCurve P ∧ edEncode P = n) ⟨_, hc⟩
  exact encode_inj hs.1 hc.1 (hs.2.trans hc.2.symm)

theorem natCast_mod (a : Nat) : ((a % p25519 : Nat) : Fp) = a := ZMod.natCast_mod a p25519

/-- Some power of x², by Fermat, squares to x⁴ or its opposite. -/
theorem pow_dichotomy (X : Fp) :
    (X ^ 2) ^ ((p25519 + 3) / 8) * (X ^ 2) ^ ((p25519 + 3) / 8) = X ^ 2 ∨
    (X ^ 2) ^ ((p25519 + 3) / 8) * (X ^ 2) ^ ((p25519 + 3) / 8) = -X ^ 2 := by
  by_cases hX : X = 0
  · left; subst hX; rw [zero_pow two_ne_zero, zero_pow (by decide)]; simp
  have hf : X ^ (p25519 - 1) = 1 := ZMod.pow_card_sub_one_eq_one hX
  have hk : (p25519 - 1) = 2 * (4 * ((p25519 + 3) / 8) - 2) := by decide
  have hsq : (X ^ (4 * ((p25519 + 3) / 8) - 2)) ^ 2 = 1 ^ 2 := by rw [← pow_mul, mul_comm, ← hk, hf, one_pow]
  have hsplit : (X ^ 2) ^ ((p25519 + 3) / 8) * (X ^ 2) ^ ((p25519 + 3) / 8) =
      X ^ (4 * ((p25519 + 3) / 8) - 2) * X ^ 2 := by
    rw [← pow_add, ← pow_mul, ← pow_add]; congr 1
  rcases sq_eq hsq with h | h
  · left; rw [hsplit, h, one_mul]
  · right; rw [hsplit, h]; ring

/-- The candidate of a point's encoding is that point. -/
theorem candidate_eq {n : Nat} {P : EdPoint} (hP : edOnCurve P) (hn : edEncode P = n) : edCandidate n = P := by
  obtain ⟨x, y⟩ := P
  have e1 := onCurve_eq hP
  obtain ⟨hx0, hxp, hy0, hyp, -⟩ := hP
  set xn := x.toNat with hxn
  set yn := y.toNat with hyn
  have hlt := p25519_lt
  have hxv : x = (xn : Int) := (Int.toNat_of_nonneg hx0).symm
  have hyv : y = (yn : Int) := (Int.toNat_of_nonneg hy0).symm
  have hxp' : xn < p25519 := by omega
  have hyp' : yn < p25519 := by omega
  simp only [edEncode, edModEncode, Int.emod_eq_of_lt hx0 hxp, Int.emod_eq_of_lt hy0 hyp] at hn
  have hlo : n % 2 ^ 255 = yn := by omega
  have hhi : n / 2 ^ 255 % 2 = xn % 2 := by omega
  rw [hxv, hyv] at e1
  push_cast at e1
  set X : Fp := (xn : Fp)
  set Y : Fp := (yn : Fp)
  unfold edCandidate
  simp only [hlo, hhi]
  -- The numbers the decoding computes, as field elements.
  set v := (d25519 * (yn * yn % p25519) + 1) % p25519 with hv
  have hvF : (v : Fp) = (d25519 : Fp) * Y ^ 2 + 1 := by
    rw [hv]; simp only [natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_one]; ring
  have hvlt : v < p25519 := Nat.mod_lt _ (by decide)
  have hinv : (nist.invC p25519 v : Fp) = (v : Fp)⁻¹ := by
    simp only [nist.invC, hvlt, ↓reduceIte, ZMod.natCast_val, ZMod.cast_id', id_eq]
  set w := (yn * yn + (p25519 - 1)) % p25519 * nist.invC p25519 v % p25519 with hw
  have hwF : (w : Fp) = X ^ 2 := by
    rw [hw]
    simp only [natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show 1 ≤ p25519 by decide),
      ZMod.natCast_self, Nat.cast_one, hinv, hvF, x_sq e1]
    ring
  have hwlt : w < p25519 := Nat.mod_lt _ (by decide)
  set r := powMod p25519 256 w ((p25519 + 3) / 8) with hr
  have hrv : r = w ^ ((p25519 + 3) / 8) % p25519 := powMod_eq _ _ _ _ (by decide)
  have hrF : (r : Fp) = (X ^ 2) ^ ((p25519 + 3) / 8) := by
    rw [hrv]; simp only [natCast_mod, Nat.cast_pow, hwF]
  have hrlt : r < p25519 := by rw [hrv]; exact Nat.mod_lt _ (by decide)
  have hI : (sqrtM1 : Fp) * sqrtM1 = -1 := by
    have : ((sqrtM1 * sqrtM1 + 1 : Nat) : Fp) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]; decide
    push_cast at this; linear_combination this
  clear_value r w v
  -- The root before its sign is fixed squares to x².
  have hx0 : ∃ x0, x0 < p25519 ∧ (x0 : Fp) ^ 2 = X ^ 2 ∧
      x0 = if r * r % p25519 = w then r else r * sqrtM1 % p25519 := by
    by_cases hA : r * r % p25519 = w
    · refine ⟨r, hrlt, ?_, by simp only [hA, ite_true]⟩
      rw [← hwF, ← hA, natCast_mod]; push_cast; ring
    · refine ⟨r * sqrtM1 % p25519, Nat.mod_lt _ (by decide), ?_, by simp only [hA, ite_false]⟩
      have hB : (r : Fp) * r ≠ X ^ 2 := by
        intro h; apply hA
        have : ((r * r : Nat) : Fp) = w := by push_cast; rw [h, hwF]
        rw [ZMod.natCast_eq_natCast_iff'] at this
        rwa [Nat.mod_eq_of_lt hwlt] at this
      rcases pow_dichotomy X with h | h
      · rw [← hrF] at h; exact absurd h hB
      · rw [← hrF] at h
        rw [natCast_mod]; push_cast
        linear_combination (sqrtM1 : Fp) ^ 2 * h - X ^ 2 * hI
  obtain ⟨x0, hx0lt, hx0sq, hx0e⟩ := hx0
  simp only [← hx0e]
  congr 1
  · split_ifs with hpar
    · rw [eq_of_sq hx0lt hxp' hx0sq hpar, hxv]
    · have hpos : 0 < x0 := by
        rcases Nat.eq_zero_or_pos x0 with h | h
        · subst h
          have hX : X = 0 := by simpa using hx0sq.symm
          have : xn = 0 := by
            exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff xn p25519).mp hX) hxp'
          simp [this] at hpar
        · exact h
      have hodd := p25519_odd
      have hlt' : p25519 - x0 < p25519 := by omega
      rw [Nat.mod_eq_of_lt hlt']
      have hneg : ((p25519 - x0 : Nat) : Fp) = -(x0 : Fp) := by
        rw [Nat.cast_sub hx0lt.le, ZMod.natCast_self, zero_sub]
      rw [eq_of_sq hlt' hxp' (by rw [hneg, neg_sq, hx0sq]) (by omega), hxv]
  · rw [hyv]

theorem decodeC_valid {n : Nat} (h : edValidEncode n) : decodeC n = some (edDecode n) := by
  obtain ⟨P, hP, hn⟩ := h
  have hc := candidate_eq hP hn
  have hd : decodeC n = some P := by
    dsimp only [decodeC]; rw [hc]; simp only [hP, hn, and_self, ite_true]
  rw [hd, decodeC_sound hd]

/-- `decodeC` refuses exactly the invalid encodings. -/
theorem decodeC_none {n : Nat} (h : decodeC n = none) : ¬ edValidEncode n := fun hv => by
  rw [decodeC_valid hv] at h; cases h

/-- `decodeC` is `edDecode` on a valid encoding, and refuses the rest. -/
theorem decodeC_spec (n : Nat) :
    (edValidEncode n → decodeC n = some (edDecode n)) ∧ (decodeC n = none ↔ ¬ edValidEncode n) :=
  ⟨decodeC_valid, decodeC_none, fun hn => by
    cases h : decodeC n with
    | none => rfl
    | some P =>
      exact absurd ⟨P, by dsimp only [decodeC] at h; split_ifs at h with hc; cases h; exact hc⟩ hn⟩

/-- `ed25519PublicKey`, over the group power `pow`. -/
def publicKeyWith (pow : EdPoint → Nat → EdPoint) (seed : List U8) : List U8 :=
  leBytesOf 32 (edEncode (pow edB (ed25519Scalar seed)))

theorem publicKey_eq (seed : List U8) : ed25519PublicKey seed = publicKeyWith edPow seed := rfl

/-- `ed25519Sign`, over the group power `pow`. -/
def signWith (pow : EdPoint → Nat → EdPoint) (seed msg : List U8) : List U8 :=
  let r := leNat (sha512 ((sha512 seed).drop 32 ++ msg)) % n25519
  let R := leBytesOf 32 (edEncode (pow edB r))
  let k := leNat (sha512 (R ++ publicKeyWith pow seed ++ msg)) % n25519
  R ++ leBytesOf 32 ((k * ed25519Scalar seed + r) % n25519)

theorem sign_eq (seed msg : List U8) : ed25519Sign seed msg = signWith edPow seed msg := rfl

/-- `ed25519Verifies`, decided, over the group power `pow` and product `mul`. -/
def verifiesWith (pow : EdPoint → Nat → EdPoint) (mul : EdPoint → EdPoint → EdPoint) (A : EdPoint)
    (key msg sig : List U8) : Bool :=
  sig.length == 64 && decide (leNat (sig.drop 32) < n25519) &&
    leNat (sig.take 32) ==
      edEncode (mul (pow (edNeg A) (leNat (sha512 (sig.take 32 ++ key ++ msg)) % n25519))
        (pow edB (leNat (sig.drop 32))))

theorem verifies_iff (A : EdPoint) (key msg sig : List U8) :
    ed25519Verifies A key msg sig ↔ verifiesWith edPow edMul A key msg sig = true := by
  simp [ed25519Verifies, verifiesWith, and_assoc]

end rind.spec
