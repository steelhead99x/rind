import Rind.X86_64.S2nBignum
import Rind.RsaLemmas
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# RSA's Montgomery products on x86_64

`low::x86_64::mont`'s `mont_mul` and `mont_sqr` pick a routine by the CPU
and the modulus's width. With BMI2 and ADX at 16 and 32 words they run
s2n-bignum's Karatsuba routines and 8n reduction, which `karatsuba_products`
proves from s2n-bignum's theorems. From eight words at a multiple of four
they run aws-lc's `bn_mul4x_mont`, whose Lean proof `mul4x_spec` restates,
or with BMI2 and ADX its `bn_mulx4x_mont`, and squaring at a multiple of
eight its `bn_sqr8x_mont`, which no proof covers: `AwsLcMont` states what
those two compute. Every other width runs aws-lc's `bn_mul_mont_nohw`,
whose HOL Light proof `nohw_spec` restates, so `mont_products` proves those
widths on any CPU, and the rest given `AwsLcMont`.

rind's HOL Light proof `BN_MUL_MONT_NOHW_SUBROUTINE_CORRECT`, in
`proofs/hol-light/x86_64/bn_mul_mont_nohw.ml` at rind's commit, is of the
naked function as rind's Linux release build emits it, which `admin/prove`
checks. Its hypotheses hold for every call `nohw` makes: `z`, `x`, `y`, and
`m` are `k` words, at least two; `z` is a `&mut` slice, so disjoint from the
others, the code, and the frame of up to `8k + 1088` bytes below the stack
pointer that the routine owns, which the stack holds, as Aeneas's model takes
every call's frame to; and `n0` is read through a reference to the word
`nohw` passes, in its caller's frame above the stack pointer. The routine
reads the width as 32 bits (`mov r9d, r9d`), so the theorem needs
`k < 2^32`, which `MontArgs` bounds. The restatement, and that the wrapper
passes the pointers and width the theorem names, are trusted.
-/

namespace rind.x86_64

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
    low.x86_64.mont.mont_mul z x y m n0 ⦃ r => MontResult x.val y.val m.val r.val ⦄) ∧
  (∀ z x m : Slice U64, ∀ n0 : U64, m.length = k → z.length = k → MontArgs x.val x.val m.val n0 →
    low.x86_64.mont.mont_sqr z x m n0 ⦃ r => MontResult x.val x.val m.val r.val ⦄)

/-- aws-lc's unproven 4x and 8x Montgomery products return their results,
at every width each takes: `bn_mulx4x_mont`, the `mulx` form of
`bn_mul4x_mont` that `mul4x` runs given BMI2 and ADX, for a multiple of four
from eight, and `bn_sqr8x_mont` for a multiple of eight. No proof covers
them. -/
def AwsLcMont : Prop :=
  (∀ z x y m : Slice U64, ∀ n0 : U64, ∀ t, z.length = m.length → 8 ≤ m.length →
    m.length % 4 = 0 → MontArgs x.val y.val m.val n0 →
    low.x86_64.mont.mul4x z x y m n0 (some t) ⦃ r => MontResult x.val y.val m.val r.val ⦄) ∧
  (∀ z x m : Slice U64, ∀ n0 : U64, ∀ adx, z.length = m.length → 8 ≤ m.length →
    m.length % 8 = 0 → MontArgs x.val x.val m.val n0 →
    low.x86_64.mont.sqr8x z x m n0 adx ⦃ r => MontResult x.val x.val m.val r.val ⦄)

/-! ## aws-lc's `bn_mul_mont_nohw` -/

/-- `BN_MUL_MONT_NOHW_SUBROUTINE_CORRECT`: for `k`-word `x`, `y`, and `m`,
from two words and fewer than `2^32`, with `n0` the `-m⁻¹ mod 2^64` of `m`,
and `x·y ≤ 2^(64k)·m`, the result is `x·y/2^(64k)` modulo `m`: every `i`
with `2^(64k)·i ≡ 1 (mod m)` gives `i·x·y mod m`,
`proofs/hol-light/x86_64/bn_mul_mont_nohw.ml`. -/
@[step]
axiom nohw_spec (z x y m : Slice U64) (n0 : U64) (hx : x.length = z.length)
    (hy : y.length = z.length) (hm : m.length = z.length) (hk : 2 ≤ z.length)
    (hbig : z.length < 2 ^ 32) (hn0 : (wordsNat m.val * n0.val + 1) % 2 ^ 64 = 0) :
    low.x86_64.mont.nohw z x y m n0 ⦃ r =>
      r.length = z.length ∧
        (wordsNat x.val * wordsNat y.val ≤ 2 ^ (64 * z.length) * wordsNat m.val →
          ∀ i, 2 ^ (64 * z.length) * i % wordsNat m.val = 1 % wordsNat m.val →
            wordsNat r.val = i * wordsNat x.val * wordsNat y.val % wordsNat m.val) ⦄

/-- A result `i·x·y mod m` for every inverse `i` of `2^(64k)`, as
`nohw_spec` and s2n-bignum's `bignum_montmul` state it, is `MontResult`
for the arguments of a Montgomery product. -/
theorem MontResult.of_inverse {x y m r : List U64} {n0 : U64} (hargs : MontArgs x y m n0)
    (hrl : r.length = m.length)
    (hr : wordsNat x * wordsNat y ≤ 2 ^ (64 * m.length) * wordsNat m →
      ∀ i, 2 ^ (64 * m.length) * i % wordsNat m = 1 % wordsNat m →
        wordsNat r = i * wordsNat x * wordsNat y % wordsNat m) :
    MontResult x y m r := by
  obtain ⟨-, -, -, -, hodd, -, hxm, hym⟩ := hargs
  have hmpos : 0 < wordsNat m := by omega
  have hle : wordsNat x * wordsNat y ≤ 2 ^ (64 * m.length) * wordsNat m :=
    calc wordsNat x * wordsNat y ≤ wordsNat m * wordsNat m := Nat.mul_le_mul hxm.le hym.le
      _ ≤ 2 ^ (64 * m.length) * wordsNat m := Nat.mul_le_mul_right _ (wordsNat_lt' m).le
  obtain ⟨i, hi⟩ : ∃ i, 2 ^ (64 * m.length) * i % wordsNat m = 1 % wordsNat m := by
    by_cases h1 : wordsNat m = 1
    · exact ⟨0, by simp [h1]⟩
    · obtain ⟨i, -, hi⟩ :=
        Nat.exists_mul_mod_eq_one_of_coprime (coprime_two_pow_odd hodd _) (by omega)
      exact ⟨i, by rw [hi, Nat.mod_eq_of_lt (by omega)]⟩
  have hrv := hr hle i hi
  refine ⟨hrl, by rw [hrv]; exact Nat.mod_lt _ hmpos, ?_⟩
  rw [hrv]
  show _ ≡ _ [MOD _]
  have h1 : 2 ^ (64 * m.length) * i ≡ 1 [MOD wordsNat m] := hi
  calc i * wordsNat x * wordsNat y % wordsNat m * 2 ^ (64 * m.length)
      ≡ i * wordsNat x * wordsNat y * 2 ^ (64 * m.length) [MOD wordsNat m] :=
        Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
    _ = (2 ^ (64 * m.length) * i) * (wordsNat x * wordsNat y) := by ring
    _ ≡ 1 * (wordsNat x * wordsNat y) [MOD wordsNat m] := Nat.ModEq.mul_right _ h1
    _ = wordsNat x * wordsNat y := one_mul _

/-- `bn_mul_mont_nohw` returns the Montgomery product of its arguments. -/
theorem nohw_result (z x y m : Slice U64) (n0 : U64) (hz : z.length = m.length)
    (hargs : MontArgs x.val y.val m.val n0) :
    low.x86_64.mont.nohw z x y m n0 ⦃ r => MontResult x.val y.val m.val r.val ⦄ := by
  obtain ⟨hx, hy, hk2, hk32, -, hn0, -⟩ := id hargs
  have hm : m.length = z.length := hz.symm
  have hzl : z.length = m.val.length := hz
  apply WP.spec_mono (nohw_spec z x y m n0 (by simp only [Slice.length] at *; omega)
    (by simp only [Slice.length] at *; omega) hm (by omega) (by omega) hn0)
  rintro r ⟨hrl, hr⟩
  rw [hz] at hrl hr
  exact MontResult.of_inverse hargs hrl hr

/-! ## aws-lc's `bn_mul4x_mont` -/

/-- `bn_mul4x_mont_correct`, rind's Lean theorem in
`Rind/X86_64/Mul4xProof.lean`, which the same build checks: the naked
function `bn_mul4x_mont`, as rind's Linux release build emits it, run in
rind's extension of pyca/verified-garbage's x86_64 model, writes to `z` the
Montgomery product of `k`-word `x` and `y` modulo `m`, below `m`, for `k` a
multiple of four from eight and below `2^32`, `n0` the `-m⁻¹ mod 2^64` of
`m`, and `x` below `m`. `mul4x` runs it without BMI2 and ADX.

Its hypotheses hold for every call `mul4x` makes: `z`, `x`, `y`, and `m` are
`k` words; `z` is a `&mut` slice, so disjoint from `m` and from the frame of
up to `8k + 1104` bytes below the stack pointer the routine owns, which the
stack holds, as Aeneas's model takes every call's frame to; `x`, `y`, and
`m` are shared slices outside that frame; and `n0` is read through a
reference to the word `mul4x` passes, in its caller's frame above the
stack pointer. `admin/prove lean` checks that the theorem's program is the
Linux build's object; Apple's build assembles its own copy,
`bn_mul4x_mont.apple.s`, which no check compares. The restatement, and that
the wrapper passes the pointers and width the theorem names, are trusted. -/
@[step]
axiom mul4x_spec (z x y m : Slice U64) (n0 : U64) (hz : z.length = m.length)
    (hx : x.length = m.length) (hy : y.length = m.length) (h8 : 8 ≤ m.length) (h4 : m.length % 4 = 0)
    (hbig : m.length < 2 ^ 32) (hn0 : (wordsNat m.val * n0.val + 1) % 2 ^ 64 = 0)
    (hxm : wordsNat x.val < wordsNat m.val) :
    low.x86_64.mont.mul4x z x y m n0 none ⦃ r => MontResult x.val y.val m.val r.val ⦄

/-- `mul4x` returns the Montgomery product of its arguments: by
`mul4x_spec` without BMI2 and ADX, and given `h4x`, `AwsLcMont`'s
statement of `bn_mulx4x_mont`, with them. -/
theorem mul4x_result (h4x : ∀ z x y m : Slice U64, ∀ n0 : U64, ∀ t, z.length = m.length → 8 ≤ m.length →
      m.length % 4 = 0 → MontArgs x.val y.val m.val n0 →
      low.x86_64.mont.mul4x z x y m n0 (some t) ⦃ r => MontResult x.val y.val m.val r.val ⦄)
    (z x y m : Slice U64) (n0 : U64) (adx : Option low.x86_64.cpu.HaveBmi2Adx) (hz : z.length = m.length)
    (h8 : 8 ≤ m.length) (h4 : m.length % 4 = 0) (hargs : MontArgs x.val y.val m.val n0) :
    low.x86_64.mont.mul4x z x y m n0 adx ⦃ r => MontResult x.val y.val m.val r.val ⦄ := by
  cases adx with
  | none =>
    obtain ⟨hx, hy, -, hbig, -, hn0, hxm, -⟩ := hargs
    exact mul4x_spec z x y m n0 hz hx hy h8 h4 hbig hn0 hxm
  | some t => exact h4x z x y m n0 t hz h8 h4 hargs

/-! ## s2n-bignum's 8n reduction, `redc_8n` -/

theorem redc_8n_spec (z product m : Slice U64) (n0 : U64) (x y : List U64)
    (hargs : MontArgs x y m.val n0) (hz : z.length = m.length)
    (hp : product.length = 2 * m.length) (h8 : m.length % 8 = 0)
    (hprod : wordsNat product.val = wordsNat x * wordsNat y) :
    low.x86_64.mont.redc_8n z product m n0 ⦃ r => MontResult x y m.val r.1.val ⦄ := by
  obtain ⟨hx, hy, hk2, -, hodd, hn0, hxm, hym⟩ := hargs
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
the routine it runs, given `h4x` and `h8x` from `AwsLcMont` for aws-lc's 4x
and 8x routines, or refutes it, as it refutes those routines' branches given
`hnarrow`, a width they do not take. -/
local syntax "mont_awslc" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| mont_awslc) => `(tactic| first
    | exact h8x _ _ _ _ _ hz (by scalar_tac) (of_multiple hlen ‹_› ‹_›) hargs
    | exact mul4x_result h4x _ _ _ _ _ _ hz (by scalar_tac) (of_multiple hlen ‹_› ‹_›) hargs
    | exact nohw_result _ _ _ _ _ hz hargs
    | (split <;> mont_awslc)
    | (step with core.num.Usize.is_multiple_of.spec; mont_awslc)
    | (exfalso; scalar_tac))

set_option maxHeartbeats 1000000 in
theorem mont_mul_spec (z x y m : Slice U64) (n0 : U64) (o : Option low.x86_64.cpu.HaveBmi2Adx)
    (hcheck : low.x86_64.cpu.HaveBmi2Adx.check = ok o)
    (hroutines : AwsLcMont ∨ m.length < 8 ∨ m.length % 4 ≠ 0)
    (hz : z.length = m.length) (hargs : MontArgs x.val y.val m.val n0) :
    low.x86_64.mont.mont_mul z x y m n0 ⦃ r => MontResult x.val y.val m.val r.val ⦄ := by
  obtain ⟨hx, hy, hk2, -⟩ := id hargs
  unfold low.x86_64.mont.mont_mul
  step*
  rw [hcheck]
  simp only [bind_ok]
  have hlen : m.len.val = m.length := by simp
  rcases hroutines with ⟨h4x, -⟩ | hnarrow
  · cases o <;> dsimp only
    · mont_awslc
    · split
      · exact karatsuba_mul_spec z x y m n0 (by omega) hz hargs
      · exact karatsuba_mul_spec z x y m n0 (by omega) hz hargs
      · mont_awslc
  · cases o <;> dsimp only
    · mont_awslc
    · split
      · exact karatsuba_mul_spec z x y m n0 (by omega) hz hargs
      · exact karatsuba_mul_spec z x y m n0 (by omega) hz hargs
      · mont_awslc

set_option maxHeartbeats 1000000 in
theorem mont_sqr_spec (z x m : Slice U64) (n0 : U64) (o : Option low.x86_64.cpu.HaveBmi2Adx)
    (hcheck : low.x86_64.cpu.HaveBmi2Adx.check = ok o)
    (hroutines : AwsLcMont ∨ m.length < 8 ∨ m.length % 4 ≠ 0)
    (hz : z.length = m.length) (hargs : MontArgs x.val x.val m.val n0) :
    low.x86_64.mont.mont_sqr z x m n0 ⦃ r => MontResult x.val x.val m.val r.val ⦄ := by
  obtain ⟨hx, -, hk2, -⟩ := id hargs
  unfold low.x86_64.mont.mont_sqr
  step*
  rw [hcheck]
  simp only [bind_ok]
  have hlen : m.len.val = m.length := by simp
  rcases hroutines with ⟨h4x, h8x⟩ | hnarrow
  · cases o <;> dsimp only
    · mont_awslc
    · split
      · exact karatsuba_sqr_spec z x m n0 (by omega) hz hargs
      · exact karatsuba_sqr_spec z x m n0 (by omega) hz hargs
      · mont_awslc
  · cases o <;> dsimp only
    · mont_awslc
    · split
      · exact karatsuba_sqr_spec z x m n0 (by omega) hz hargs
      · exact karatsuba_sqr_spec z x m n0 (by omega) hz hargs
      · mont_awslc

/-- With BMI2 and ADX, rind's Montgomery products at 16 and 32 words run
s2n-bignum's routines, whose theorems prove them. -/
theorem karatsuba_products {k : Nat} (o : Option low.x86_64.cpu.HaveBmi2Adx)
    (hcheck : low.x86_64.cpu.HaveBmi2Adx.check = ok o) (hsome : o.isSome)
    (hk : k = 16 ∨ k = 32) : MontProducts k := by
  obtain ⟨t, rfl⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨fun z x y m n0 hm hz hargs => ?_, fun z x m n0 hm hz hargs => ?_⟩
  · obtain ⟨hx, hy, hk2, -⟩ := id hargs
    unfold low.x86_64.mont.mont_mul
    step*
    rw [hcheck]
    simp only [bind_ok]
    have hlen : m.len.val = m.length := by simp
    rcases hk with hk | hk <;> simp only [hlen, hm, hk] <;>
      exact karatsuba_mul_spec z x y m n0 (by omega) (by omega) hargs
  · obtain ⟨hx, -, hk2, -⟩ := id hargs
    unfold low.x86_64.mont.mont_sqr
    step*
    rw [hcheck]
    simp only [bind_ok]
    have hlen : m.len.val = m.length := by simp
    rcases hk with hk | hk <;> simp only [hlen, hm, hk] <;>
      exact karatsuba_sqr_spec z x m n0 (by omega) (by omega) hargs

/-- rind's Montgomery products at width `k` return their results: on any
CPU at a width aws-lc's 4x and 8x routines do not take, which runs
`bn_mul_mont_nohw` but for s2n-bignum's Karatsuba routines, with BMI2 and
ADX at 16 and 32 words, and at any other width given `AwsLcMont`. -/
theorem mont_products {k : Nat} (o : Option low.x86_64.cpu.HaveBmi2Adx)
    (hcheck : low.x86_64.cpu.HaveBmi2Adx.check = ok o)
    (hroutines : AwsLcMont ∨ k < 8 ∨ k % 4 ≠ 0 ∨ o.isSome ∧ (k = 16 ∨ k = 32)) :
    MontProducts k := by
  have general (h : AwsLcMont ∨ k < 8 ∨ k % 4 ≠ 0) : MontProducts k :=
    ⟨fun z x y m n0 hm hz hargs => mont_mul_spec z x y m n0 o hcheck (by rw [hm]; exact h)
        (by rw [hm, hz]) hargs,
      fun z x m n0 hm hz hargs => mont_sqr_spec z x m n0 o hcheck (by rw [hm]; exact h)
        (by rw [hm, hz]) hargs⟩
  rcases hroutines with h | h | h | ⟨hsome, hk⟩
  · exact general (Or.inl h)
  · exact general (Or.inr (Or.inl h))
  · exact general (Or.inr (Or.inr h))
  · exact karatsuba_products o hcheck hsome hk

end rind.x86_64
