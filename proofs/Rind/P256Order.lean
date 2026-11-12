import Rind.P256Multiples
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Fintype.EquivFin
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Every finite point of P-256 has order n

`P256Order` is no longer a hypothesis. The group has n points: at most two
affine points share an x-coordinate, so with the point at infinity there are
at most 2p + 1, which is less than 3n, and n divides the order because G has
order n and n is prime. The only other possibility is 2n, which would hold a
point of order 2, a root of x³ − 3x + b. A remainder of xᵖ modulo that cubic,
and Bézout coefficients against it, show the cubic has no root.

The counting steps are stated for any odd prime field and any b, so P-384 and
P-521 apply them with their own no-root certificates.
-/

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace rind.spec

/-! ## y² = x³ − 3x + b -/

/-- The curve y² = x³ − 3x + `b` over `ZMod p`. -/
def nistCurve {p : ℕ} [Fact p.Prime] (b : ZMod p) : WeierstrassCurve.Affine (ZMod p) :=
  ({ a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -3, a₆ := b } : WeierstrassCurve (ZMod p)).toAffine

theorem p256Curve_eq : p256Curve = nistCurve (b256 : ZMod p256) := rfl

variable {p : ℕ} [Fact p.Prime]

theorem y_sq (b : ZMod p) {x y : ZMod p} (h : (nistCurve b).Equation x y) :
    y ^ 2 = x ^ 3 - 3 * x + b := by
  rw [equation_iff] at h
  simp only [nistCurve, toAffine] at h
  linear_combination h

/-- Which half of the field a representative lies in. For an odd prime, `y` and
`-y` lie in different halves whenever they are distinct. -/
def halfBit (y : ZMod p) : Fin 2 :=
  if y.val ≤ (p - 1) / 2 then 0 else 1

theorem halfBit_neg {y : ZMod p} (hp : p ≠ 2) (hy : y ≠ -y) : halfBit y ≠ halfBit (-y) := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (by simp)
  have : NeZero y := ⟨hy0⟩
  have hval : (-y).val = p - y.val := ZMod.val_neg_of_ne_zero y
  have hodd : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd (Fact.out : Nat.Prime p) with h | h
    · exact absurd h hp
    · exact h
  unfold halfBit
  by_cases hyh : y.val ≤ (p - 1) / 2
  · have hgt : ¬p - y.val ≤ (p - 1) / 2 := by
      have hyv : y.val < p := y.val_lt
      omega
    simp [hval, hyh, hgt]
  · have hle : p - y.val ≤ (p - 1) / 2 := by
      have hyv : y.val < p := y.val_lt
      have hpos : 0 < y.val := Nat.pos_of_ne_zero fun h => hy0 ((ZMod.val_eq_zero y).mp h)
      omega
    simp [hval, hyh, hle]

/-- Infinity, or an affine point's x-coordinate and which half its y lies in. -/
def pack (b : ZMod p) : (nistCurve b).Point → Option (ZMod p × Fin 2)
  | .zero => none
  | .some x y _ => some (x, halfBit y)

theorem pack_injective (b : ZMod p) (hp : p ≠ 2) : Function.Injective (pack b) := by
  intro P Q hPQ
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some _ _ _ => simp [pack] at hPQ
  | some x y h =>
    cases Q with
    | zero => simp [pack] at hPQ
    | some x' y' h' =>
      simp only [pack, Option.some.injEq, Prod.mk.injEq] at hPQ
      rcases hPQ with ⟨rfl, hbit⟩
      have hy2 : y ^ 2 = y' ^ 2 := by
        linear_combination y_sq b h.1 - y_sq b h'.1
      have hfac : (y - y') * (y + y') = 0 := by linear_combination hy2
      rcases mul_eq_zero.mp hfac with hsub | hadd
      · have hyy : y = y' := sub_eq_zero.mp hsub
        subst hyy
        congr
      · have hyneg : y = -y' := (eq_neg_iff_add_eq_zero).2 hadd
        by_cases hsame : y = y'
        · subst hsame
          congr
        · have hne : y ≠ -y := by
            intro hyy
            apply hsame
            apply neg_injective
            rw [← hyneg]
            exact hyy.symm
          have : halfBit y = halfBit (-y) := by simpa [hyneg] using hbit
          exact absurd this (halfBit_neg hp hne)

theorem nist_finite (b : ZMod p) (hp : p ≠ 2) : Finite (nistCurve b).Point :=
  Finite.of_injective (pack b) (pack_injective b hp)

theorem nist_card_le (b : ZMod p) (hp : p ≠ 2) : Nat.card (nistCurve b).Point ≤ 2 * p + 1 := by
  have := nist_finite b hp
  have := Fintype.ofFinite (nistCurve b).Point
  rw [Nat.card_eq_fintype_card]
  refine (Fintype.card_le_of_injective (pack b) (pack_injective b hp)).trans ?_
  rw [Fintype.card_option, Fintype.card_prod, ZMod.card, Fintype.card_fin]
  omega

theorem no_two_torsion (b : ZMod p) (hp : p ≠ 2)
    (hnoroot : ∀ x : ZMod p, x ^ 3 - 3 * x + b ≠ 0) (Q : (nistCurve b).Point) :
    addOrderOf Q ≠ 2 := by
  intro hQ
  have h2 : (2 : ℕ) • Q = 0 :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).mp (by simp [hQ])
  have hneg : Q = -Q := eq_neg_of_add_eq_zero_left (by simpa [two_nsmul] using h2)
  cases Q with
  | zero =>
    rw [show Point.zero = (0 : (nistCurve b).Point) from rfl, addOrderOf_zero] at hQ
    omega
  | some x y hns =>
    have hform : -(.some x y hns : (nistCurve b).Point) =
        (.some x ((nistCurve b).negY x y) ((nonsingular_neg x y).mpr hns) : (nistCurve b).Point) :=
      rfl
    have hcoord : y = (nistCurve b).negY x y := by
      have hpts := hneg.trans hform
      injection hpts with _ hy
    have hy0 : y = 0 := by
      have hny : (nistCurve b).negY x y = -y := by simp [negY, nistCurve, toAffine]
      rw [hny] at hcoord
      have : (2 : ZMod p) * y = 0 := by linear_combination hcoord
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h
        have hp2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
        have : p = 2 := by
          have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hp2
          have hge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
          omega
        exact hp this
      exact (mul_eq_zero.mp this).resolve_left h2ne
    have he := y_sq b hns.1
    rw [hy0, zero_pow (by decide)] at he
    exact hnoroot x he.symm

theorem nist_order (b : ZMod p) (n : ℕ) [Fact n.Prime] (hp : p ≠ 2) (hbound : 2 * p + 1 < 3 * n)
    (G : (nistCurve b).Point) (hG : addOrderOf G = n)
    (hnoroot : ∀ x : ZMod p, x ^ 3 - 3 * x + b ≠ 0) (P : (nistCurve b).Point) (hP : P ≠ 0) :
    addOrderOf P = n := by
  have := nist_finite b hp
  have hcard_le := nist_card_le b hp
  have hdvd : n ∣ Nat.card (nistCurve b).Point := by
    rw [← hG]
    exact addOrderOf_dvd_natCard G
  obtain ⟨k, hk⟩ := hdvd
  have hcard_pos : 0 < Nat.card (nistCurve b).Point := by
    have : Nonempty (nistCurve b).Point := ⟨0⟩
    exact Nat.card_pos
  have hk_pos : 0 < k := by
    have : 0 < n * k := by simpa [hk] using hcard_pos
    exact Nat.pos_of_mul_pos_left this
  have hk_lt : k < 3 := by
    have hkn : k * n < 3 * n := by
      have : k * n ≤ 2 * p + 1 := by simpa [hk, Nat.mul_comm] using hcard_le
      exact lt_of_le_of_lt this hbound
    exact Nat.lt_of_mul_lt_mul_right hkn
  have hk_cases : k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl
  · have hdiv : addOrderOf P ∣ n := by simpa [hk, Nat.mul_comm] using addOrderOf_dvd_natCard P
    have h1 : addOrderOf P ≠ 1 := fun h => hP ((AddMonoid.addOrderOf_eq_one_iff).mp h)
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime n)).mp hdiv with h | h
    · exact absurd h h1
    · exact h
  · have h2dvd : 2 ∣ Nat.card (nistCurve b).Point := by
      rw [hk, Nat.mul_comm]
      exact dvd_mul_right 2 n
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨Q, hQo⟩ := exists_prime_addOrderOf_dvd_card' 2 h2dvd
    exact absurd hQo (no_two_torsion b hp hnoroot Q)

/-! ## x³ − 3x + b has no root in P-256's field -/

/-- One product of degree < 3 polynomials, reduced by x³ = 3x − b. -/
def mul3 (a0 a1 a2 b0 b1 b2 : ℕ) : ℕ × ℕ × ℕ :=
  let d0 := a0 * b0
  let d1 := a0 * b1 + a1 * b0
  let d2 := a0 * b2 + a1 * b1 + a2 * b0
  let d3 := a1 * b2 + a2 * b1
  let d4 := a2 * b2
  ((d0 + (p256 - b256) * d3) % p256, (d1 + 3 * d3 + (p256 - b256) * d4) % p256,
    (d2 + 3 * d4) % p256)

/-- x^`e` modulo x³ − 3x + b, for `e < 2 ^ fuel`, as three coefficients. -/
def powX : ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _ => (1, 0, 0)
  | _ + 1, 0 => (1, 0, 0)
  | fuel + 1, e =>
    let r := powX fuel (e / 2)
    let s := mul3 r.1 r.2.1 r.2.2 r.1 r.2.1 r.2.2
    if e % 2 = 0 then s else mul3 s.1 s.2.1 s.2.2 0 1 0

/-- The remainder of x^p. `powX_cert` is the kernel's evaluation of `powX`. -/
def remX : ℕ × ℕ × ℕ :=
  (66434390973925144466073271287821796038003695194169110494110089305650096453661,
    12402202686218762177567235911775779164004716598278868847786114277539554646092,
    24678849118215552148312087830792888746041224110560601850711771001608500700145)

set_option maxHeartbeats 20000000 in
theorem powX_cert : powX 256 p256 = remX := by
  decide +kernel

/-- `c0 + c1 X + c2 X²`. -/
def E (c0 c1 c2 : ℕ) : (ZMod p256)[X] :=
  C (c0 : ZMod p256) + C (c1 : ZMod p256) * X + C (c2 : ZMod p256) * X ^ 2

/-- x³ − 3x + b, monic. -/
def cubic : (ZMod p256)[X] :=
  X ^ 3 + (C (-3) * X + C (b256 : ZMod p256))

theorem cubic_monic : cubic.Monic := by
  unfold cubic
  refine monic_X_pow_add ?_
  refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · exact (degree_C_mul_X_le _).trans_lt (by decide)
  · exact degree_C_le.trans_lt (by decide)

theorem cubic_degree : cubic.degree = 3 := by
  unfold cubic
  have hlt : (C (-3 : ZMod p256) * X + C (b256 : ZMod p256)).degree < (X ^ 3 : (ZMod p256)[X]).degree := by
    rw [degree_X_pow]
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · exact (degree_C_mul_X_le _).trans_lt (by decide)
    · exact degree_C_le.trans_lt (by decide)
  rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
  rfl

theorem degree_E_lt (c0 c1 c2 : ℕ) : (E c0 c1 c2).degree < 3 := by
  unfold E
  refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · exact degree_C_le.trans_lt (by decide)
    · exact (degree_C_mul_X_le _).trans_lt (by decide)
  · exact (degree_C_mul_X_pow_le 2 _).trans_lt (by decide)

theorem cast_mod (n : ℕ) : ((n % p256 : ℕ) : ZMod p256) = n := by
  rw [ZMod.natCast_mod]

theorem cast_pb : ((p256 - b256 : ℕ) : ZMod p256) = -((b256 : ℕ) : ZMod p256) := by
  rw [Nat.cast_sub (by decide : b256 ≤ p256), ZMod.natCast_self]
  simp

theorem E_one : E 1 0 0 = 1 := by
  simp [E]

theorem E_mul (a0 a1 a2 b0 b1 b2 : ℕ) :
    E a0 a1 a2 * E b0 b1 b2 =
      cubic * (C ((a1 * b2 + a2 * b1 : ℕ) : ZMod p256) + C ((a2 * b2 : ℕ) : ZMod p256) * X) +
        E (mul3 a0 a1 a2 b0 b1 b2).1 (mul3 a0 a1 a2 b0 b1 b2).2.1
          (mul3 a0 a1 a2 b0 b1 b2).2.2 := by
  unfold E cubic mul3
  simp only [map_mul, map_add, map_neg, map_ofNat, cast_mod, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, cast_pb]
  ring

theorem E_mod (a0 a1 a2 b0 b1 b2 : ℕ) :
    E (mul3 a0 a1 a2 b0 b1 b2).1 (mul3 a0 a1 a2 b0 b1 b2).2.1 (mul3 a0 a1 a2 b0 b1 b2).2.2 =
      (E a0 a1 a2 * E b0 b1 b2) %ₘ cubic := by
  have h := E_mul a0 a1 a2 b0 b1 b2
  have hdeg := degree_E_lt (mul3 a0 a1 a2 b0 b1 b2).1 (mul3 a0 a1 a2 b0 b1 b2).2.1
    (mul3 a0 a1 a2 b0 b1 b2).2.2
  rw [← cubic_degree] at hdeg
  have hsum :
      E (mul3 a0 a1 a2 b0 b1 b2).1 (mul3 a0 a1 a2 b0 b1 b2).2.1 (mul3 a0 a1 a2 b0 b1 b2).2.2 +
          cubic * (C ((a1 * b2 + a2 * b1 : ℕ) : ZMod p256) + C ((a2 * b2 : ℕ) : ZMod p256) * X) =
        E a0 a1 a2 * E b0 b1 b2 := by
    rw [h]
    ring
  exact (div_modByMonic_unique
      (C ((a1 * b2 + a2 * b1 : ℕ) : ZMod p256) + C ((a2 * b2 : ℕ) : ZMod p256) * X)
      (E (mul3 a0 a1 a2 b0 b1 b2).1 (mul3 a0 a1 a2 b0 b1 b2).2.1 (mul3 a0 a1 a2 b0 b1 b2).2.2)
      cubic_monic ⟨hsum, hdeg⟩).2.symm

theorem powX_spec : ∀ fuel e, e < 2 ^ fuel →
    E (powX fuel e).1 (powX fuel e).2.1 (powX fuel e).2.2 = (X ^ e) %ₘ cubic := by
  intro fuel
  induction fuel with
  | zero =>
    intro e he
    have : e = 0 := by simpa using he
    subst this
    simp only [powX, E_one, pow_zero]
    have hdeg : (1 : (ZMod p256)[X]).degree < cubic.degree := by
      rw [cubic_degree]
      exact (degree_C_le (a := (1 : ZMod p256))).trans_lt (by decide)
    rw [(modByMonic_eq_self_iff cubic_monic).2 hdeg]
  | succ fuel ih =>
    intro e he
    cases e with
    | zero =>
      simp only [powX, E_one, pow_zero]
      have hdeg : (1 : (ZMod p256)[X]).degree < cubic.degree := by
        rw [cubic_degree]
        exact (degree_C_le (a := (1 : ZMod p256))).trans_lt (by decide)
      rw [(modByMonic_eq_self_iff cubic_monic).2 hdeg]
    | succ e =>
      set k := (e + 1) / 2
      set bit := (e + 1) % 2
      have hhalf : k < 2 ^ fuel := by omega
      have spec := ih k hhalf
      have hdiv : k * 2 + bit = e + 1 := by simpa [k, bit, Nat.mul_comm] using Nat.div_add_mod (e + 1) 2
      have hr : powX (fuel + 1) (e + 1) =
          let r := powX fuel k
          let s := mul3 r.1 r.2.1 r.2.2 r.1 r.2.1 r.2.2
          if bit = 0 then s else mul3 s.1 s.2.1 s.2.2 0 1 0 := by
        simp only [powX, k, bit]
      rw [hr]
      have hX : (X : (ZMod p256)[X]) %ₘ cubic = X := by
        rw [(modByMonic_eq_self_iff cubic_monic).2]
        rw [cubic_degree, degree_X]
        decide
      by_cases hbit0 : bit = 0
      · simp only [hbit0, ite_true]
        have hm := E_mod (powX fuel k).1 (powX fuel k).2.1 (powX fuel k).2.2 (powX fuel k).1
          (powX fuel k).2.1 (powX fuel k).2.2
        rw [hm, spec, ← mul_modByMonic, ← pow_add]
        have : k + k = e + 1 := by simp [hbit0] at hdiv; omega
        simp [this]
      · have hbit1 : bit = 1 := by
          have : bit < 2 := Nat.mod_lt (e + 1) (by decide : 0 < 2)
          omega
        rw [hbit1, ite_eq_right (by decide : (1 : ℕ) ≠ 0)]
        set s := mul3 (powX fuel k).1 (powX fuel k).2.1 (powX fuel k).2.2 (powX fuel k).1
          (powX fuel k).2.1 (powX fuel k).2.2
        have hm := E_mod (powX fuel k).1 (powX fuel k).2.1 (powX fuel k).2.2 (powX fuel k).1
          (powX fuel k).2.1 (powX fuel k).2.2
        have hx := E_mod s.1 s.2.1 s.2.2 0 1 0
        have hEX : E 0 1 0 = X := by simp [E]
        rw [hx, hEX, hm, spec]
        have step : ((((X ^ k) %ₘ cubic * ((X ^ k) %ₘ cubic)) %ₘ cubic) * X) %ₘ cubic =
            X ^ (e + 1) %ₘ cubic := by
          rw [← mul_modByMonic, ← pow_add]
          have hmul := mul_modByMonic (X ^ (k + k)) X cubic
          rw [hX] at hmul
          rw [← hmul]
          have hexp : e + 1 = k + k + 1 := by simp [hbit1] at hdiv; omega
          rw [hexp, pow_succ]
        exact step

/-- Bézout coefficients for `(x^p mod cubic − x)` against the cubic. -/
def bezS0 : ℕ :=
  65199464431731064497896050416425136433505252717504720697398575518837415740899
def bezS1 : ℕ :=
  13613227622405416990223372143232386667703210042769555039222612853590004013888
def bezS2 : ℕ :=
  52608018465713852339899995848108786535529536607091291889139954752671423675232
def bezT0 : ℕ :=
  28034875749780233574014042674555906067575508707793895058595262185983639558082
def bezT1 : ℕ :=
  93830914210933607160575563506962808323901052023622248780018007269074241130787
def bezG : ℕ :=
  36531512945503493287457765334184561595323916464521845967847447430701397941132

theorem bezout_expand (s0 s1 s2 r0 r1 r2 t0 t1 : ℕ) :
    E s0 s1 s2 * E r0 r1 r2 + (C (t0 : ZMod p256) + C (t1 : ZMod p256) * X) * cubic =
      (C ((s0 : ZMod p256) * r0 + (t0 : ZMod p256) * b256) +
        C ((s0 : ZMod p256) * r1 + (s1 : ZMod p256) * r0 + -((t0 : ZMod p256) * 3) +
          (t1 : ZMod p256) * b256) * X +
        C ((s0 : ZMod p256) * r2 + (s1 : ZMod p256) * r1 + (s2 : ZMod p256) * r0 +
          -((t1 : ZMod p256) * 3)) * X ^ 2 +
        C ((s1 : ZMod p256) * r2 + (s2 : ZMod p256) * r1 + (t0 : ZMod p256)) * X ^ 3 +
        C ((s2 : ZMod p256) * r2 + (t1 : ZMod p256)) * X ^ 4 : (ZMod p256)[X]) := by
  unfold E cubic
  simp only [map_mul, map_add, map_neg, map_ofNat]
  ring_nf

theorem bezout :
    (C (bezS0 : ZMod p256) + C (bezS1 : ZMod p256) * X + C (bezS2 : ZMod p256) * X ^ 2) *
        (C (remX.1 : ZMod p256) + C ((remX.2.1 - 1 : ℕ) : ZMod p256) * X +
          C (remX.2.2 : ZMod p256) * X ^ 2) +
      (C (bezT0 : ZMod p256) + C (bezT1 : ZMod p256) * X) * cubic =
      C (bezG : ZMod p256) := by
  have h1 : 1 ≤ remX.2.1 := by decide
  have hexp := bezout_expand bezS0 bezS1 bezS2 remX.1 (remX.2.1 - 1) remX.2.2 bezT0 bezT1
  have hc0 : (bezS0 * remX.1 + bezT0 * b256) % p256 = bezG := by decide
  have hc1 : (bezS0 * (remX.2.1 - 1) + bezS1 * remX.1 + bezT0 * (p256 - 3) + bezT1 * b256) % p256 = 0 := by
    decide
  have hc2 : (bezS0 * remX.2.2 + bezS1 * (remX.2.1 - 1) + bezS2 * remX.1 + bezT1 * (p256 - 3)) % p256 = 0 := by
    decide
  have hc3 : (bezS1 * remX.2.2 + bezS2 * (remX.2.1 - 1) + bezT0) % p256 = 0 := by decide
  have hc4 : (bezS2 * remX.2.2 + bezT1) % p256 = 0 := by decide
  have push {n m : ℕ} (h : n % p256 = m) : ((n : ℕ) : ZMod p256) = m := by
    rw [← h]
    simp [ZMod.natCast_mod]
  have cast0 : (bezS0 : ZMod p256) * remX.1 + (bezT0 : ZMod p256) * b256 = bezG := by
    simpa [Nat.cast_add, Nat.cast_mul] using push hc0
  have cast1 : (bezS0 : ZMod p256) * (remX.2.1 - 1) + (bezS1 : ZMod p256) * remX.1 +
      -((bezT0 : ZMod p256) * 3) + (bezT1 : ZMod p256) * b256 = 0 := by
    have h := push hc1
    simpa [Nat.cast_sub h1, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by decide : 3 ≤ p256)] using h
  have cast2 : (bezS0 : ZMod p256) * remX.2.2 + (bezS1 : ZMod p256) * (remX.2.1 - 1) +
      (bezS2 : ZMod p256) * remX.1 + -((bezT1 : ZMod p256) * 3) = 0 := by
    have h := push hc2
    simpa [Nat.cast_sub h1, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by decide : 3 ≤ p256)] using h
  have cast3 : (bezS1 : ZMod p256) * remX.2.2 + (bezS2 : ZMod p256) * (remX.2.1 - 1) +
      (bezT0 : ZMod p256) = 0 := by
    simpa [Nat.cast_sub h1, Nat.cast_add, Nat.cast_mul] using push hc3
  have cast4 : (bezS2 : ZMod p256) * remX.2.2 + (bezT1 : ZMod p256) = 0 := by
    simpa [Nat.cast_add, Nat.cast_mul] using push hc4
  simpa [E, Nat.cast_sub h1, cast0, cast1, cast2, cast3, cast4] using hexp

theorem p256_no_root (x : ZMod p256) : x ^ 3 - 3 * x + (b256 : ZMod p256) ≠ 0 := by
  intro hx
  have hF : cubic.eval x = 0 := by
    simp [cubic]
    linear_combination hx
  have hR : E remX.1 remX.2.1 remX.2.2 = (X ^ p256) %ₘ cubic := by
    simpa [powX_cert, remX] using powX_spec 256 p256 (by decide : p256 < 2 ^ 256)
  have hdiv := modByMonic_add_div (X ^ p256) cubic
  have hReval : (E remX.1 remX.2.1 remX.2.2).eval x = x := by
    rw [hR]
    have := congrArg (fun t : (ZMod p256)[X] => t.eval x) hdiv
    simpa [Polynomial.eval_add, Polynomial.eval_mul, hF, ZMod.pow_card] using this
  have hsub : E remX.1 (remX.2.1 - 1) remX.2.2 = E remX.1 remX.2.1 remX.2.2 - X := by
    have hone : 1 ≤ remX.2.1 := by decide
    simp [E, Nat.cast_sub hone]
    ring
  have hzero : (E remX.1 (remX.2.1 - 1) remX.2.2).eval x = 0 := by
    rw [hsub, Polynomial.eval_sub, hReval, Polynomial.eval_X]
    ring
  have hbez := congrArg (fun t : (ZMod p256)[X] => t.eval x) bezout
  have hrx : (remX.1 : ZMod p256) + ((remX.2.1 - 1 : ℕ) : ZMod p256) * x + (remX.2.2 : ZMod p256) * x ^ 2 = 0 := by
    simpa [E, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X] using hzero
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hF, hrx]
    at hbez
  exact (by decide : (bezG : ZMod p256) ≠ 0) hbez.symm

theorem p256Order_holds : P256Order := by
  intro P hP hne
  obtain ⟨X, hX⟩ := exists_fromM P hP
  have hX0 : X ≠ 0 := by
    intro h
    cases h
    simp [fromM] at hX
    exact hne hX.symm
  obtain ⟨G, hG⟩ : ∃ G, fromM G = p256G := fromM_of_onCurve p256OnCurve_G
  have : Fact n256.Prime := ⟨prime_n256⟩
  have hGord : addOrderOf G = n256 :=
    addOrderOf_eq_prime (n256_nsmul_G G hG) (by
      intro h
      simp [h, fromM, p256G] at hG)
  have hord : addOrderOf X = n256 :=
    nist_order (b256 : ZMod p256) n256 (by decide) (by decide) G hGord p256_no_root X hX0
  simpa [hX] using order_fromM X hord

end rind.spec
