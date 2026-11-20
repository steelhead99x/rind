import Rind.Aarch64.S2nBignum
import Rind.RsaLemmas
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# RSA's Montgomery products on aarch64

`low::aarch64::mont`'s `mont_mul` and `mont_sqr` run aws-lc's `bn_mul_mont`
from two words, behind the wrapper `mul_mont`, and s2n-bignum's `bignum_montmul`
below. rind's HOL Light proof `BN_MUL_MONT_SUBROUTINE_CORRECT`, in
`proofs/hol-light/aarch64/bn_mul_mont.ml` at rind's commit, joins the proofs
of its three routines, the generic path, `__bn_mul4x_mont`, and
`__bn_sqr8x_mont`, and `admin/prove` checks it against the object code rind's
Linux release build emits. Apple's build lacks the entry's `.align 5`, so no
proof covers its object.

The theorem's hypotheses hold for every call `mul_mont` makes: `z`, `x`, `y`,
and `m` are `k` words, at least two; `z` is a `&mut` slice, so disjoint from
the others, the code, and the stack frame of `16k + 128` bytes below the stack
pointer, which the routine owns; the ABI keeps the stack pointer 16-byte
aligned; and `n0` is read through a reference to the one word `mul_mont`
passes. At a multiple of four the routine adds 32 to `x` and `m`, and the
theorem needs the sums not to wrap. The axiom does not carry that hypothesis,
since the model has no addresses: it is a trusted step, that a slice of at
least 32 bytes does not end at the top of the address space. `k < 2^58` holds for each
width RSA takes, which `MontArgs` bounds below `2^32`. The restatement, and
that the wrapper passes the pointers and width the theorem names, are trusted.
-/

namespace rind.aarch64

/-- `BN_MUL_MONT_SUBROUTINE_CORRECT`: for `k`-word `x`, `y`, and `m`, `m` odd
with `n0` its `-m⁻¹ mod 2^64`, and `x·y ≤ 2^(64k)·m`, the result is `x·y/2^(64k)`
modulo `m`: every `i` with `2^(64k)·i ≡ 1 (mod m)` gives `i·x·y mod m`. -/
@[step]
axiom mul_mont_spec (z x y m : Slice U64) (n0 : U64) (hx : x.length = z.length)
    (hy : y.length = z.length) (hm : m.length = z.length) (hk : 2 ≤ z.length)
    (hbig : z.length < 2 ^ 58) (hn0 : (wordsNat m.val * n0.val + 1) % 2 ^ 64 = 0) :
    low.aarch64.mont.mul_mont z x y m n0 ⦃ r =>
      r.length = z.length ∧
        (wordsNat x.val * wordsNat y.val ≤ 2 ^ (64 * z.length) * wordsNat m.val →
          ∀ i, 2 ^ (64 * z.length) * i % wordsNat m.val = 1 % wordsNat m.val →
            wordsNat r.val = i * wordsNat x.val * wordsNat y.val % wordsNat m.val) ⦄

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
    low.aarch64.mont.mont_mul z x y m n0 ⦃ r => MontResult x.val y.val m.val r.val ⦄) ∧
  (∀ z x m : Slice U64, ∀ n0 : U64, m.length = k → z.length = k → MontArgs x.val x.val m.val n0 →
    low.aarch64.mont.mont_sqr z x m n0 ⦃ r => MontResult x.val x.val m.val r.val ⦄)

/-- What `mul_mont_spec` gives, for the arguments of a Montgomery product, is
`MontResult`. -/
theorem mont_result_of {x y m r : List U64} {n0 : U64} (hargs : MontArgs x y m n0)
    (hrl : r.length = m.length)
    (hr : wordsNat x * wordsNat y ≤ 2 ^ (64 * m.length) * wordsNat m →
      ∀ i, 2 ^ (64 * m.length) * i % wordsNat m = 1 % wordsNat m →
        wordsNat r = i * wordsNat x * wordsNat y % wordsNat m) :
    MontResult x y m r := by
  obtain ⟨hx, hy, hk2, hk32, hodd, hn0, hxm, hym⟩ := hargs
  have hmpos : 0 < wordsNat m := by
    rcases Nat.eq_zero_or_pos (wordsNat m) with h | h
    · simp [h] at hodd
    · exact h
  have hlt : wordsNat x * wordsNat y ≤ 2 ^ (64 * m.length) * wordsNat m :=
    calc wordsNat x * wordsNat y ≤ wordsNat m * wordsNat m := Nat.mul_le_mul hxm.le hym.le
      _ ≤ 2 ^ (64 * m.length) * wordsNat m :=
          Nat.mul_le_mul_right _ (wordsNat_lt' m).le
  have hcop : Nat.Coprime (2 ^ (64 * m.length)) (wordsNat m) := by
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd))
  obtain ⟨i, hi⟩ : ∃ i, 2 ^ (64 * m.length) * i % wordsNat m = 1 % wordsNat m := by
    by_cases h1 : wordsNat m = 1
    · exact ⟨0, by simp [h1]⟩
    · obtain ⟨i, -, hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
      exact ⟨i, by rw [hi, Nat.mod_eq_of_lt (by omega)]⟩
  have hrv := hr hlt i hi
  refine ⟨hrl, ?_, ?_⟩
  · rw [hrv]; exact Nat.mod_lt _ hmpos
  · rw [hrv]
    show _ ≡ _ [MOD _]
    have h1 : 2 ^ (64 * m.length) * i ≡ 1 [MOD wordsNat m] := by unfold Nat.ModEq; rw [hi]
    calc i * wordsNat x * wordsNat y % wordsNat m * 2 ^ (64 * m.length)
        ≡ i * wordsNat x * wordsNat y * 2 ^ (64 * m.length) [MOD wordsNat m] :=
          Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
      _ = (2 ^ (64 * m.length) * i) * (wordsNat x * wordsNat y) := by ring
      _ ≡ 1 * (wordsNat x * wordsNat y) [MOD wordsNat m] := Nat.ModEq.mul_right _ h1
      _ = wordsNat x * wordsNat y := one_mul _

/-- `mont_mul` returns the Montgomery product: `mul_mont` from two words, which
`MontArgs` gives. -/
theorem mont_mul_spec (z x y m : Slice U64) (n0 : U64) (hz : z.length = m.length)
    (hargs : MontArgs x.val y.val m.val n0) :
    low.aarch64.mont.mont_mul z x y m n0 ⦃ r => MontResult x.val y.val m.val r.val ⦄ := by
  obtain ⟨hx, hy, hk2, -⟩ := id hargs
  unfold low.aarch64.mont.mont_mul
  step*
  exact mont_result_of hargs (by simpa [Slice.length, hz] using r_post)
    (by simpa [Slice.length, hz] using r_post1)

/-- `mont_sqr` returns the Montgomery square. -/
theorem mont_sqr_spec (z x m : Slice U64) (n0 : U64) (hz : z.length = m.length)
    (hargs : MontArgs x.val x.val m.val n0) :
    low.aarch64.mont.mont_sqr z x m n0 ⦃ r => MontResult x.val x.val m.val r.val ⦄ := by
  obtain ⟨hx, -, hk2, -⟩ := id hargs
  unfold low.aarch64.mont.mont_sqr
  step*
  exact mont_result_of hargs (by simpa [Slice.length, hz] using r_post)
    (by simpa [Slice.length, hz] using r_post1)

/-- aws-lc's `bn_mul_mont` proves rind's Montgomery multiplication and squaring
at every width from two words, whatever the CPU. -/
theorem mont_products (k : Nat) : MontProducts k :=
  ⟨fun z x y m n0 hm hz hargs => mont_mul_spec z x y m n0 (by rw [hm, hz]) hargs,
    fun z x m n0 hm hz hargs => mont_sqr_spec z x m n0 (by rw [hm, hz]) hargs⟩

end rind.aarch64
