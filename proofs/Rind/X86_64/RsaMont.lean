import Rind.X86_64.S2nBignum
import Rind.RsaLemmas
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# RSA's Montgomery products on x86_64

`low::x86_64::mont`'s `mont_mul` and `mont_sqr` pick a routine by the CPU
and the modulus's width. With BMI2 and ADX at 16 and 32 words they run
s2n-bignum's Karatsuba routines and 8n reduction, which `karatsuba_products`
proves from s2n-bignum's theorems. Every other width and CPU runs aws-lc's
routines, which no proof covers: `AwsLcMont` states what they compute, and
`awslc_products` derives the same from it, so a later proof of those routines
drops the hypothesis.
-/

namespace rind.x86_64

/-- What a Montgomery product of `x` and `y` modulo `m` returns: a value
below `m`, as wide, that times `2^(64k)` is `x·y` modulo `m`. -/
def MontResult (x y m r : List U64) : Prop :=
  r.length = m.length ∧ wordsNat r < wordsNat m ∧
    wordsNat r * 2 ^ (64 * m.length) % wordsNat m = wordsNat x * wordsNat y % wordsNat m

/-- What a Montgomery product takes: `x` and `y` below the odd `m`, all as
wide, of at least two words, and `n0`, which is `-m⁻¹ mod 2^64`. -/
def MontArgs (x y m : List U64) (n0 : U64) : Prop :=
  x.length = m.length ∧ y.length = m.length ∧ 2 ≤ m.length ∧ wordsNat m % 2 = 1 ∧
    (wordsNat m * n0.val + 1) % 2 ^ 64 = 0 ∧ wordsNat x < wordsNat m ∧ wordsNat y < wordsNat m

/-- rind's Montgomery multiplication and squaring at width `k` return their
results. -/
def MontProducts (k : Nat) : Prop :=
  (∀ z x y m : Slice U64, ∀ n0 : U64, m.length = k → z.length = k → MontArgs x.val y.val m.val n0 →
    low.x86_64.mont.mont_mul z x y m n0 ⦃ r => MontResult x.val y.val m.val r.val ⦄) ∧
  (∀ z x m : Slice U64, ∀ n0 : U64, m.length = k → z.length = k → MontArgs x.val x.val m.val n0 →
    low.x86_64.mont.mont_sqr z x m n0 ⦃ r => MontResult x.val x.val m.val r.val ⦄)

/-- aws-lc's Montgomery products return their results, at every width each
takes: `bn_mul_mont_nohw` from two words, `bn_mul4x_mont` and its `mulx`
form for a multiple of four from eight, and `bn_sqr8x_mont` for a multiple
of eight. No proof covers them. -/
def AwsLcMont : Prop :=
  (∀ z x y m : Slice U64, ∀ n0 : U64, z.length = m.length → MontArgs x.val y.val m.val n0 →
    low.x86_64.mont.nohw z x y m n0 ⦃ r => MontResult x.val y.val m.val r.val ⦄) ∧
  (∀ z x y m : Slice U64, ∀ n0 : U64, ∀ adx, z.length = m.length → 8 ≤ m.length →
    m.length % 4 = 0 → MontArgs x.val y.val m.val n0 →
    low.x86_64.mont.mul4x z x y m n0 adx ⦃ r => MontResult x.val y.val m.val r.val ⦄) ∧
  (∀ z x m : Slice U64, ∀ n0 : U64, ∀ adx, z.length = m.length → 8 ≤ m.length →
    m.length % 8 = 0 → MontArgs x.val x.val m.val n0 →
    low.x86_64.mont.sqr8x z x m n0 adx ⦃ r => MontResult x.val x.val m.val r.val ⦄)

/-! ## s2n-bignum's 8n reduction, `redc_8n` -/

theorem redc_8n_spec (z product m : Slice U64) (n0 : U64) (x y : List U64)
    (hargs : MontArgs x y m.val n0) (hz : z.length = m.length)
    (hp : product.length = 2 * m.length) (h8 : m.length % 8 = 0)
    (hprod : wordsNat product.val = wordsNat x * wordsNat y) :
    low.x86_64.mont.redc_8n z product m n0 ⦃ r => MontResult x y m.val r.1.val ⦄ := by
  obtain ⟨hx, hy, hk2, hodd, hn0, hxm, hym⟩ := hargs
  have hmR : wordsNat m.val < 2 ^ (64 * m.length) := wordsNat_lt' m.val
  unfold low.x86_64.mont.redc_8n
  step with bignum_emontredc_8n_spec product m n0 hp h8 as ⟨c, p1, hl1, heq⟩
  have heq := heq hn0
  set k := m.length
  set R := 2 ^ (64 * k)
  set q := wordsNat (p1.val.take k)
  set h := wordsNat (p1.val.drop k)
  have hqR : q < R := by
    have := wordsNat_lt' (p1.val.take k)
    simp only [List.length_take] at this
    calc q < 2 ^ (64 * min k p1.val.length) := this
      _ ≤ R := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hhR : h < R := by
    have := wordsNat_lt' (p1.val.drop k)
    simp only [List.length_drop] at this
    calc h < 2 ^ (64 * (p1.val.length - k)) := this
      _ ≤ R := Nat.pow_le_pow_right (by norm_num) (by simp [Slice.length] at hl1 hp ⊢; omega)
  have hxy : wordsNat x * wordsNat y < wordsNat m.val * wordsNat m.val :=
    Nat.mul_lt_mul'' hxm hym
  have hT : R * c.val + h < 2 * wordsNat m.val := redc_lt hmR hqR (by rw [hprod]; exact hxy) heq
  have hmod : (R * c.val + h) * R % wordsNat m.val = wordsNat x * wordsNat y % wordsNat m.val := by
    rw [redc_mod heq, hprod]
  step*
  · rw [i1_post]; split <;> simp
  have hk : (↑m.len : Nat) = k := by simp [k]
  have hred : wordsNat reduced.val = h := by rw [__post3, hk]
  have hm0 : 0 < wordsNat m.val := by omega
  have hc1 : c.val ≤ 1 := by
    by_contra hc
    have : R * 2 ≤ R * c.val := Nat.mul_le_mul_left _ (by omega)
    omega
  have hge : ge.val = c.val ||| i2.val := by
    simp only [UScalar.val, ge_post1, BitVec.toNat_or]
  have hT2 : ∀ T, wordsNat m.val ≤ T → T < 2 * wordsNat m.val → T % wordsNat m.val = T - wordsNat m.val :=
    fun T h1 h2 => by rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  have hz1 : wordsNat z1.val = (R * c.val + h) % wordsNat m.val := by
    rw [z1_post1, hred, hge, hz]
    rcases (show c.val = 0 ∨ c.val = 1 by omega) with hc | hc
    · rw [hc] at hT ⊢
      simp only [Nat.zero_or, Nat.mul_zero, Nat.zero_add] at hT ⊢
      by_cases hh : h < wordsNat m.val
      · rw [i2_post, i1_post, hred, ite_eq_left hh, ite_eq_left (by simp), Nat.mod_eq_of_lt hh]
      · rw [i2_post, i1_post, hred, ite_eq_right hh, ite_eq_right (by simp), ite_eq_left (by omega), hT2 _ (by omega) hT]
    · rw [hc] at hT ⊢
      have hh : h < wordsNat m.val := by omega
      have hor : (1 ||| i2.val) ≠ 0 := by
        intro h0; rw [Nat.or_eq_zero_iff] at h0; omega
      rw [ite_eq_right hor, ite_eq_right (by omega), hT2 _ (by omega) hT]
      omega
  refine ⟨by simp [z1_post, hz, k], ?_, ?_⟩
  · rw [hz1]; exact Nat.mod_lt _ hm0
  · rw [hz1, Nat.mod_mul_mod, hmod]

/-! ## s2n-bignum's Karatsuba products at 16 and 32 words -/

theorem karatsuba_mul_spec (z x y m : Slice U64) (n0 : U64) (hk : m.length = 16 ∨ m.length = 32)
    (hz : z.length = m.length) (hargs : MontArgs x.val y.val m.val n0) :
    low.x86_64.mont.karatsuba_mul z x y m n0 ⦃ r => MontResult x.val y.val m.val r.val ⦄ := by
  obtain ⟨hx, hy, -⟩ := id hargs
  unfold low.x86_64.mont.karatsuba_mul
  dsimp only
  split <;> rename_i hlen <;> step* <;>
  · have hs2 : s2.val = s1.val := by
      rw [s2_post, to_slice_mut_back_post, Array.from_slice_val _ _ (by simpa using s1_post)]
    step with redc_8n_spec z s2 m n0 x.val y.val hargs hz
      (by simp only [Slice.length, hs2] at s1_post ⊢; scalar_tac) (by scalar_tac)
      (by rw [hs2, s1_post1]) as ⟨z1, _p, hz1⟩
    exact hz1

theorem karatsuba_sqr_spec (z x m : Slice U64) (n0 : U64) (hk : m.length = 16 ∨ m.length = 32)
    (hz : z.length = m.length) (hargs : MontArgs x.val x.val m.val n0) :
    low.x86_64.mont.karatsuba_sqr z x m n0 ⦃ r => MontResult x.val x.val m.val r.val ⦄ := by
  obtain ⟨hx, -⟩ := id hargs
  unfold low.x86_64.mont.karatsuba_sqr
  dsimp only
  split <;> rename_i hlen <;> step* <;>
  · have hs2 : s2.val = s1.val := by
      rw [s2_post, to_slice_mut_back_post, Array.from_slice_val _ _ (by simpa using s1_post)]
    step with redc_8n_spec z s2 m n0 x.val x.val hargs hz
      (by simp only [Slice.length, hs2] at s1_post ⊢; scalar_tac) (by scalar_tac)
      (by rw [hs2, s1_post1, pow_two]) as ⟨z1, _p, hz1⟩
    exact hz1

/-! ## The dispatch -/

/-- A dispatch branch's `is_multiple_of` test, as `AwsLcMont` states it. -/
theorem of_multiple {b : Bool} {k : Usize} {d : Nat} {m : Slice U64} (hk : k.val = m.length)
    (h1 : (b = true) = (k.val % d = 0)) (h2 : b = true) : m.length % d = 0 := by
  rw [← hk, ← h1]; exact h2

/-- Splits `mont_mul`'s or `mont_sqr`'s dispatch, and closes each branch by
the routine it runs, given `hnohw`, `h4x`, and `h8x` from `AwsLcMont`, or
refutes it. -/
local syntax "mont_awslc" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| mont_awslc) => `(tactic| first
    | exact h8x _ _ _ _ _ hz (by scalar_tac) (of_multiple hlen ‹_› ‹_›) hargs
    | exact h4x _ _ _ _ _ _ hz (by scalar_tac) (of_multiple hlen ‹_› ‹_›) hargs
    | exact hnohw _ _ _ _ _ hz hargs
    | (split <;> mont_awslc)
    | (step with core.num.Usize.is_multiple_of.spec; mont_awslc)
    | (exfalso; scalar_tac))

theorem mont_mul_spec (z x y m : Slice U64) (n0 : U64) (o : Option low.x86_64.cpu.HaveBmi2Adx)
    (hcheck : low.x86_64.cpu.HaveBmi2Adx.check = ok o)
    (hroutines : AwsLcMont ∨ o.isSome ∧ (m.length = 16 ∨ m.length = 32))
    (hz : z.length = m.length) (hargs : MontArgs x.val y.val m.val n0) :
    low.x86_64.mont.mont_mul z x y m n0 ⦃ r => MontResult x.val y.val m.val r.val ⦄ := by
  obtain ⟨hx, hy, hk2, -⟩ := id hargs
  unfold low.x86_64.mont.mont_mul
  step*
  rw [hcheck]
  simp only [bind_ok]
  have hlen : m.len.val = m.length := by simp
  rcases hroutines with ⟨hnohw, h4x, -⟩ | ⟨hsome, hk⟩
  · cases o <;> dsimp only
    · mont_awslc
    · split
      · exact karatsuba_mul_spec z x y m n0 (by omega) hz hargs
      · exact karatsuba_mul_spec z x y m n0 (by omega) hz hargs
      · mont_awslc
  · obtain ⟨t, rfl⟩ := Option.isSome_iff_exists.mp hsome
    dsimp only
    rcases hk with hk | hk <;> simp only [hlen, hk] <;>
      exact karatsuba_mul_spec z x y m n0 (by omega) hz hargs

set_option maxHeartbeats 1000000 in
theorem mont_sqr_spec (z x m : Slice U64) (n0 : U64) (o : Option low.x86_64.cpu.HaveBmi2Adx)
    (hcheck : low.x86_64.cpu.HaveBmi2Adx.check = ok o)
    (hroutines : AwsLcMont ∨ o.isSome ∧ (m.length = 16 ∨ m.length = 32))
    (hz : z.length = m.length) (hargs : MontArgs x.val x.val m.val n0) :
    low.x86_64.mont.mont_sqr z x m n0 ⦃ r => MontResult x.val x.val m.val r.val ⦄ := by
  obtain ⟨hx, -, hk2, -⟩ := id hargs
  unfold low.x86_64.mont.mont_sqr
  step*
  rw [hcheck]
  simp only [bind_ok]
  have hlen : m.len.val = m.length := by simp
  rcases hroutines with ⟨hnohw, h4x, h8x⟩ | ⟨hsome, hk⟩
  · cases o <;> dsimp only
    · mont_awslc
    · split
      · exact karatsuba_sqr_spec z x m n0 (by omega) hz hargs
      · exact karatsuba_sqr_spec z x m n0 (by omega) hz hargs
      · mont_awslc
  · obtain ⟨t, rfl⟩ := Option.isSome_iff_exists.mp hsome
    dsimp only
    rcases hk with hk | hk <;> simp only [hlen, hk] <;>
      exact karatsuba_sqr_spec z x m n0 (by omega) hz hargs

/-- With BMI2 and ADX, rind's Montgomery products at 16 and 32 words run
s2n-bignum's routines, whose theorems prove them. Any other width or CPU
runs aws-lc's, which `AwsLcMont` states. -/
theorem mont_products {k : Nat} (o : Option low.x86_64.cpu.HaveBmi2Adx)
    (hcheck : low.x86_64.cpu.HaveBmi2Adx.check = ok o)
    (hroutines : AwsLcMont ∨ o.isSome ∧ (k = 16 ∨ k = 32)) : MontProducts k :=
  ⟨fun z x y m n0 hm hz hargs => mont_mul_spec z x y m n0 o hcheck (by rw [hm]; exact hroutines)
      (by rw [hm, hz]) hargs,
    fun z x m n0 hm hz hargs => mont_sqr_spec z x m n0 o hcheck (by rw [hm]; exact hroutines)
      (by rw [hm, hz]) hargs⟩

end rind.x86_64
