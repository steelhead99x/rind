import Rind.Portable.Bignum
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# RSA's Montgomery products on the portable backend

`low::generic::mont`'s `mont_mul` and `mont_sqr` at every width RSA's keys
take, to `MAX_WORDS`: below `SEPARATE` limbs CIOS, and from there the whole
product, by Karatsuba from `KARATSUBA_MUL` limbs or a square's from
`KARATSUBA_SQR`, reduced by `redc`. `Rind.Portable.Mont` proves each from
its loops, so `mont_products` rests on no axiom beyond Lean's own three,
`propext`, `Classical.choice`, and `Quot.sound`.

The RSA proofs `admin/prove` writes from x86_64's import this as x86_64's
import theirs, and take from here what x86_64's take from s2n-bignum's
axioms: `Runs`, and through `Rind.Portable.Bignum` the word routines' specs.
-/

namespace rind.portable

/-- What a Montgomery product of `x` and `y` modulo `m` returns: a value
below `m`, as wide, that times `2^(64k)` is `x·y` modulo `m`. -/
def MontResult (x y m r : List U64) : Prop :=
  r.length = m.length ∧ wordsNat r < wordsNat m ∧
    wordsNat r * 2 ^ (64 * m.length) % wordsNat m = wordsNat x * wordsNat y % wordsNat m

/-- What a Montgomery product takes: `x` and `y` below the odd `m`, all as
wide, of at least two words and fewer than `2^32`, which RSA's key sizes
keep, and `n0`, which is `-m⁻¹ mod 2^64`. -/
def MontArgs (x y m : List U64) (n0 : U64) : Prop :=
  x.length = m.length ∧ y.length = m.length ∧ 2 ≤ m.length ∧ m.length < 2 ^ 32 ∧
    wordsNat m % 2 = 1 ∧ (wordsNat m * n0.val + 1) % 2 ^ 64 = 0 ∧
    wordsNat x < wordsNat m ∧ wordsNat y < wordsNat m

/-- rind's Montgomery multiplication and squaring at width `k` return their
results. -/
def MontProducts (k : Nat) : Prop :=
  (∀ z x y m : Slice U64, ∀ n0 : U64, m.length = k → z.length = k → MontArgs x.val y.val m.val n0 →
    low.generic.limb64.mont.mont_mul z x y m n0 ⦃ r => MontResult x.val y.val m.val r.val ⦄) ∧
  (∀ z x m : Slice U64, ∀ n0 : U64, m.length = k → z.length = k → MontArgs x.val x.val m.val n0 →
    low.generic.limb64.mont.mont_sqr z x m n0 ⦃ r => MontResult x.val x.val m.val r.val ⦄)

theorem separate_eq : low.generic.limb64.mont.SEPARATE = 16#usize := by
  unfold low.generic.limb64.mont.SEPARATE; rfl

theorem limbs_eq {N : Usize} (x : Slice U64) (buf : Array U64 N) :
    low.generic.limb64.limbs x buf = ok (x, buf) := rfl

/-- `mont_mul`: CIOS below `SEPARATE` limbs, and the whole product reduced
from there. -/
theorem mont_mul_spec (z x y m : Slice U64) (n0 : U64) (hz : z.length = m.length) (hk : m.length ≤ 128)
    (hargs : MontArgs x.val y.val m.val n0) :
    low.generic.limb64.mont.mont_mul z x y m n0 ⦃ r => MontResult x.val y.val m.val r.val ⦄ := by
  obtain ⟨hx, hy, hk2, -, -, hn0, hX, hY⟩ := hargs
  have hmL : m.val.length = m.length := rfl
  have hxL : x.val.length = m.length := hx
  have hyL : y.val.length = m.length := hy
  have hzL : z.val.length = m.length := hz
  have hmlen : (Slice.len m).val = m.length := by simp
  have hn0' : (m.val[0]!.val * n0.val + 1) % 2 ^ 64 = 0 := by
    rw [← wordsNat_mod_limb _ (by omega), Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    exact hn0
  have hMk : wordsNat m.val < 2 ^ (64 * m.length) := by have := wordsNat_lt' m.val; rwa [hmL] at this
  unfold low.generic.limb64.mont.mont_mul
  simp only [limbs_eq, bind_ok]
  step
  step
  step
  step
  rw [separate_eq]
  split
  · rename_i hn
    have hn' : m.length < 16 := by simpa using hn
    step as ⟨i3, hi3⟩
    step as ⟨s, back, hs, hsl, hback⟩
    have hsv : s.val = List.replicate (m.length + 2) 0#u64 := by
      have h130 : (130#usize).val = 130 := by simp
      rw [hs, hi3, Array.repeat_val, List.slice, List.drop_zero, Nat.sub_zero, List.take_replicate, h130, hmlen,
        Nat.min_eq_left (by omega)]
    step with mont_mul_limbs_spec s x y m n0 (by omega) hx hy hsv (by scalar_tac) hY hn0' as ⟨s1, hs1l, hr, hrm⟩
    simp only [lift, bind_ok]
    have hs1L : s1.val.length = m.length + 2 := hs1l
    have hbv : (back s1).to_slice.val.take m.length = s1.val.take m.length := by
      rw [Array.val_to_slice, hback, show m.length = 0 + m.length by simp,
        take_setSlice _ _ _ _ (by rw [hs1L, Array.repeat_val]; simp; omega) (by omega)]
      simp
    step with join_spec (back s1).to_slice z (by
      simp only [Slice.length]; rw [Array.val_to_slice, hback, List.length_setSlice!, Array.repeat_val]; simp; omega)
      as ⟨r, hrv⟩
    rw [hz, hbv] at hrv
    refine ⟨?_, ?_, ?_⟩ <;> rw [hrv]
    · simp; omega
    · exact hr
    · rw [hmL]; exact hrm
  · rename_i hn
    have hn' : 16 ≤ m.length := by simpa using hn
    step as ⟨i3, hi3⟩
    step as ⟨t1, back, ht1, ht1l, hback⟩
    have ht1L : t1.length = 2 * m.length := by rw [ht1l, hi3]; simp
    rw [karatsuba_mul_eq]
    have hT : wordsNat x.val * wordsNat y.val < 2 ^ (64 * (2 * m.length - m.length)) * wordsNat m.val := by
      rw [show 2 * m.length - m.length = m.length by omega]
      calc wordsNat x.val * wordsNat y.val < wordsNat m.val * wordsNat m.val := Nat.mul_lt_mul'' hX hY
        _ ≤ 2 ^ (64 * m.length) * wordsNat m.val := Nat.mul_le_mul_right _ hMk.le
    have tail : ∀ t2 : Slice U64, t2.length = 2 * m.length → wordsNat t2.val = wordsNat x.val * wordsNat y.val →
        (do
          let t3 ← low.generic.limb64.mont.redc t2 m n0
          let s2 ← core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := m.len } t3
          low.generic.limb64.join s2 z) ⦃ r => MontResult x.val y.val m.val r.val ⦄ := by
      intro t2 ht2l ht2
      step with redc_spec t2 m n0 (by omega) (by omega) hn0 (by rw [ht2, ht2l]; exact hT) as ⟨t3, ht3l, hr, hrm⟩
      rw [ht2l, show 2 * m.length - m.length = m.length by omega] at hr hrm
      rw [ht2] at hrm
      step as ⟨s2, hs2, hs2l⟩
      step with join_spec s2 z (by rw [hs2l, ht3l, ht2l, hmlen]; omega) as ⟨r, hrv⟩
      have hs2L : s2.val.length = m.length := by
        rw [show s2.val.length = s2.length from rfl, hs2l, ht3l, ht2l, hmlen]; omega
      rw [hz, ← hs2L, List.take_length, hs2, hmlen] at hrv
      refine ⟨?_, ?_, ?_⟩ <;> rw [hrv]
      · rw [List.length_drop, show t3.val.length = t3.length from rfl, ht3l, ht2l]; omega
      · exact hr
      · rw [hmL]; exact hrm
    split
    · rename_i hn2
      have hn2' : m.length < 32 := by simpa using hn2
      simp only [lift, bind_ok, Array.to_slice_mut]
      have hin : (do
          let (t3, _) ← low.generic.limb64.mont.mul_limbs t1 x y (Std.Array.empty U64).to_slice
          ok t3) ⦃ t2 => t2.length = 2 * m.length ∧ wordsNat t2.val = wordsNat x.val * wordsNat y.val ⦄ := by
        step with mul_limbs_spec m.length t1 x y (Std.Array.empty U64).to_slice hx hy ht1L
          (by rw [mulNeed_small _ hn2']; omega) (by scalar_tac) as ⟨t2, s2, ht2l, _, ht2⟩
        exact ⟨ht2l, ht2⟩
      apply WP.spec_bind hin
      rintro t2 ⟨ht2l, ht2⟩
      exact tail t2 ht2l ht2
    · simp only [lift, bind_ok, Array.to_slice_mut]
      have hin : (do
          let (t3, _) ← low.generic.limb64.mont.mul_limbs t1 x y (Array.repeat 576#usize 0#u64).to_slice
          ok t3) ⦃ t2 => t2.length = 2 * m.length ∧ wordsNat t2.val = wordsNat x.val * wordsNat y.val ⦄ := by
        step with mul_limbs_spec m.length t1 x y (Array.repeat 576#usize 0#u64).to_slice hx hy ht1L (by
          simp only [Slice.length]; rw [Array.val_to_slice, Array.repeat_val, List.length_replicate]
          exact le_trans (mulNeed_le _ hk) (by simp)) (by scalar_tac) as ⟨t2, s2, ht2l, _, ht2⟩
        exact ⟨ht2l, ht2⟩
      apply WP.spec_bind hin
      rintro t2 ⟨ht2l, ht2⟩
      exact tail t2 ht2l ht2

/-- `mont_sqr`: the whole square, reduced. -/
theorem mont_sqr_spec (z x m : Slice U64) (n0 : U64) (hz : z.length = m.length) (hk : m.length ≤ 128)
    (hargs : MontArgs x.val x.val m.val n0) :
    low.generic.limb64.mont.mont_sqr z x m n0 ⦃ r => MontResult x.val x.val m.val r.val ⦄ := by
  obtain ⟨hx, -, hk2, -, -, hn0, hX, -⟩ := hargs
  have hmL : m.val.length = m.length := rfl
  have hzL : z.val.length = m.length := hz
  have hmlen : (Slice.len m).val = m.length := by simp
  unfold low.generic.limb64.mont.mont_sqr
  simp only [limbs_eq, bind_ok]
  step
  step
  step
  step as ⟨i2, hi2⟩
  step as ⟨s, back, hs, hsl, hback⟩
  step with mont_sqr_limbs_spec s x m n0 (by omega) hk hx (by rw [hsl, hi2, hmlen]) hX hn0 as ⟨s1, hs1l, hr, hrm⟩
  have hs1L : s1.val.length = 2 * m.length := hs1l
  have hrep : (Array.repeat 256#usize 0#u64).val.length = 256 := by rw [Array.repeat_val, List.length_replicate]; rfl
  have hbv : (back s1).val = s1.val ++ (Array.repeat 256#usize 0#u64).val.drop (2 * m.length) := by
    rw [hback, setSlice_eq _ _ _ (by rw [hs1L, hrep]; omega)]; simp [hs1L]
  step as ⟨s2, hs2, hs2l⟩
  have hs2v : s2.val = s1.val.drop m.length := by
    rw [hs2, Array.val_to_slice, hbv, hmlen, hi2, hmlen, List.slice, List.drop_append_of_le_length (by omega),
      show 2 * m.length - m.length = m.length by omega, List.take_append_of_le_length (by simp; omega),
      List.take_of_length_le (by simp; omega)]
  step with join_spec s2 z (by simp only [Slice.length]; rw [hs2v, List.length_drop]; omega) as ⟨r, hrv⟩
  rw [hz, hs2v, List.take_of_length_le (by simp; omega)] at hrv
  refine ⟨?_, ?_, ?_⟩ <;> rw [hrv]
  · rw [List.length_drop]; omega
  · exact hr
  · rw [hmL]; exact hrm

/-- rind's portable Montgomery products return their results at every
width to `MAX_WORDS`. -/
theorem mont_products {k : Nat} (hk : k ≤ 128) : MontProducts k :=
  ⟨fun z x y m n0 hm hz hargs => mont_mul_spec z x y m n0 (by rw [hz, hm]) (by omega) hargs,
    fun z x m n0 hm hz hargs => mont_sqr_spec z x m n0 (by rw [hz, hm]) (by omega) hargs⟩

/-- A 2048-bit modulus fills 32 words, whose Montgomery products rind's
portable backend runs on `low::generic::mont`'s routines, proven here. -/
theorem rsa2048_mont_products (N : Nat) (hN : N.size = 2048) : MontProducts ((N.size + 63) / 64) := by
  rw [hN]
  exact mont_products (by norm_num)

/-! ## What the RSA proofs assume of the code below them -/

/-- rind runs: its entry guards pass. The portable backend has no CPU
dispatch on RSA's path, and neither guard reads an input. -/
def Runs : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ (∃ e, low.entry.Entry.new_public = ok e)

@[step]
theorem new_secret_spec (h : Runs) : low.entry.Entry.new_secret ⦃ _ => True ⦄ := by
  obtain ⟨⟨e, he⟩, -⟩ := h
  simp [he]

@[step]
theorem new_public_spec (h : Runs) : low.entry.Entry.new_public ⦃ _ => True ⦄ := by
  obtain ⟨-, ⟨e, he⟩⟩ := h
  simp [he]

/-- `Precompute::check` never gives a token here: pyca/verified-garbage's
routine needs x86_64 or aarch64. -/
theorem precompute_check_spec (_ : Runs) (n : Slice U64) :
    low.generic.rsa_vg.Precompute.check n ⦃ _ => True ⦄ := by
  simp [low.generic.rsa_vg.Precompute.check]

end rind.portable
