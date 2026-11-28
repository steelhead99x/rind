import Rind.Aarch64.MlKemCoding
open Aeneas Aeneas.Std Result rind.spec Spec Spec.MLKEM rind.spec.mlkem

/-!
# aarch64's ML-KEM 12-bit unpacking in Rust

s2n-bignum has no routine for ML-KEM's 12-bit unpacking on aarch64, so rind
runs `low::generic::mlkem`'s Rust there; x86_64 runs it too without AVX2, and
with AVX2 runs s2n-bignum's instead. Ciphertext compression on aarch64 is
mlkem-native's NEON assembly, which HOL Light proves; `admin/prove bytes`
checks rind's build is the code that proof lists.

* `mlkem_frombytes_spec`: `mlkem_frombytes` unpacks each 12-bit field of its
  bytes as it is, so in `[0, 4096)`; each is congruent modulo `q` to
  `ByteDecode_12`'s coefficient (`Holds 0 4095`), which reduces it, and the
  `mlkem_reduce` that follows in `mid::mlkem` makes it canonical.

It rests on no axiom.
-/

namespace rind.aarch64

namespace MlKemGeneric

open MlKemCoding

/-- An `i16` whose bits, as a number, are below `2^15` holds that number. -/
theorem i16_val_of_lt (x : I16) (h : x.bv.toNat < 2 ^ 15) : x.val = x.bv.toNat := by
  show x.bv.toInt = _
  exact BitVec.toInt_eq_toNat_of_lt (by omega)

/-- A byte, widened to an `i16`, holds its value. -/
theorem hcast_toNat (x : U8) : (UScalar.hcast .I16 x).bv.toNat = x.val := by
  rw [UScalar.hcast_bv_eq, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le x.bv.isLt (by simp [IScalarTy.numBits]))

/-- The `i16` `mlkem_frombytes` writes at coefficient `p`: in `[0, 2^12)`,
its bits those of the bytes from bit `12 * p`. -/
def Unpacked (B : List U8) (p : ℕ) (v : I16) : Prop :=
  0 ≤ v.val ∧ v.val < 4096 ∧
    ∀ j < 12, v.val.toNat.testBit j = (B[(12 * p + j) / 8]!).val.testBit ((12 * p + j) % 8)

theorem frombytes_loop_spec (a : Array U8 384#usize)
    (iter : core.ops.range.Range Usize) (r : Array I16 256#usize) (he : iter.end.val = 128)
    (hs : iter.start.val = 0) :
    low.generic.mlkem.mlkem_frombytes_loop iter r a ⦃ r' => ∀ p < 256, Unpacked a.val p (r'.val[p]!) ⦄ := by
  unfold low.generic.mlkem.mlkem_frombytes_loop
  apply WP.spec_mono (range_loop 128 (fun i (r : Array I16 256#usize) =>
    ∀ p < 2 * i, Unpacked a.val p (r.val[p]!)) _ _ iter r he (by omega) (by rw [hs]; intro p hp; omega))
  · intro r' hr'
    exact hr'
  · intro it r he hs hinv
    simp only
    unfold low.generic.mlkem.mlkem_frombytes_loop.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step*
      have hlen : a.val.length = 384 := a.property
      have hb0 : a.val[3 * it.start.val]! = a0 := by
        rw [a0_post, ← i1_post]; exact getElem!_pos a.val i1.val (by scalar_tac)
      have hb1 : a.val[3 * it.start.val + 1]! = a1 := by
        rw [a1_post, ← i1_post, ← i2_post]; exact getElem!_pos a.val i2.val (by scalar_tac)
      have hb2 : a.val[3 * it.start.val + 2]! = a2 := by
        rw [a2_post, ← i1_post, ← i3_post]; exact getElem!_pos a.val i3.val (by scalar_tac)
      have ha0 : a0.val < 256 := by scalar_tac
      have ha1 : a1.val < 256 := by scalar_tac
      have ha2 : a2.val < 256 := by scalar_tac
      have h15 : a1.val &&& 15 ≤ 15 := Nat.and_le_right
      have hi4 : i4.bv.toNat = a0.val := by rw [i4_post]; exact hcast_toNat a0
      have hi6 : i6.bv.toNat = a1.val &&& 15 := by rw [i6_post, hcast_toNat, i5_post, UScalar.val_and]; rfl
      have hi7 : i7.bv.toNat = (a1.val &&& 15) * 2 ^ 8 := by
        simp only [i7_post1, BitVec.toNat_shiftLeft, hi6, Nat.shiftLeft_eq]
        exact Nat.mod_eq_of_lt (by omega)
      have hi11 : i11.bv.toNat = a1.val >>> 4 := by rw [i11_post, hcast_toNat, i10_post]
      have hi12 : i12.bv.toNat = a2.val := by rw [i12_post]; exact hcast_toNat a2
      have hi13 : i13.bv.toNat = a2.val * 2 ^ 4 := by
        simp only [i13_post1, BitVec.toNat_shiftLeft, hi12, Nat.shiftLeft_eq]
        exact Nat.mod_eq_of_lt (by omega)
      have hn9 : i9.bv.toNat = a0.val ||| (a1.val &&& 15) * 2 ^ 8 := by
        simp only [i9_post1, BitVec.toNat_or, hi4, hi7]
      have hn15 : i15.bv.toNat = (a1.val >>> 4) ||| a2.val * 2 ^ 4 := by
        simp only [i15_post1, BitVec.toNat_or, hi11, hi13]
      have hlt9 : i9.bv.toNat < 2 ^ 12 := by
        rw [hn9]; exact Nat.or_lt_two_pow (by omega) (by omega)
      have hlt15 : i15.bv.toNat < 2 ^ 12 := by
        rw [hn15, Nat.shiftRight_eq_div_pow]; exact Nat.or_lt_two_pow (by omega) (by omega)
      have hv9 := i16_val_of_lt i9 (by omega)
      have hv15 := i16_val_of_lt i15 (by omega)
      have hu9 : Unpacked a.val (2 * it.start.val) i9 := by
        refine ⟨by rw [hv9]; positivity, by rw [hv9]; omega, fun j hj => ?_⟩
        rw [hv9, Int.toNat_natCast, hn9, Nat.testBit_or, Nat.testBit_mul_two_pow, Nat.testBit_and]
        by_cases hj8 : j < 8
        · rw [show (12 * (2 * it.start.val) + j) / 8 = 3 * it.start.val by omega,
            show (12 * (2 * it.start.val) + j) % 8 = j by omega, hb0]
          simp [show ¬ 8 ≤ j by omega]
        · rw [show (12 * (2 * it.start.val) + j) / 8 = 3 * it.start.val + 1 by omega,
            show (12 * (2 * it.start.val) + j) % 8 = j - 8 by omega, hb1,
            Nat.testBit_lt_two_pow (lt_of_lt_of_le ha0 (by
              calc 256 = 2 ^ 8 := by norm_num
                _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)))]
          have h15b : (15 : ℕ).testBit (j - 8) = true := by
            have : j - 8 < 4 := by omega
            interval_cases (j - 8) <;> decide
          simp [show 8 ≤ j by omega, h15b]
      have hu15 : Unpacked a.val (2 * it.start.val + 1) i15 := by
        refine ⟨by rw [hv15]; positivity, by rw [hv15]; omega, fun j hj => ?_⟩
        rw [hv15, Int.toNat_natCast, hn15, Nat.testBit_or, Nat.testBit_mul_two_pow, Nat.testBit_shiftRight]
        by_cases hj4 : j < 4
        · rw [show (12 * (2 * it.start.val + 1) + j) / 8 = 3 * it.start.val + 1 by omega,
            show (12 * (2 * it.start.val + 1) + j) % 8 = 4 + j by omega, hb1]
          simp [show ¬ 4 ≤ j by omega]
        · rw [show (12 * (2 * it.start.val + 1) + j) / 8 = 3 * it.start.val + 2 by omega,
            show (12 * (2 * it.start.val + 1) + j) % 8 = j - 4 by omega, hb2,
            Nat.testBit_lt_two_pow (lt_of_lt_of_le ha1 (by
              calc 256 = 2 ^ 8 := by norm_num
                _ ≤ 2 ^ (4 + j) := Nat.pow_le_pow_right (by norm_num) (by omega)))]
          simp [show 4 ≤ j by omega]
      refine ⟨by rw [he1]; exact he, hst, by omega, fun p hp => ?_⟩
      rw [hst] at hp
      have hidx8 : i8.val = 2 * it.start.val := i8_post
      have hidx14 : i14.val = 2 * it.start.val + 1 := by rw [i14_post, i8_post]
      rw [a3_post, r1_post, Array.set_val_eq, Array.set_val_eq, hidx8, hidx14]
      by_cases hp1 : p = 2 * it.start.val + 1
      · subst hp1
        rw [getElem!_set_self _ _ _ (by simp; omega)]
        exact hu15
      · rw [getElem!_set_ne _ _ _ _ (Ne.symm hp1)]
        by_cases hp0 : p = 2 * it.start.val
        · subst hp0
          rw [getElem!_set_self _ _ _ (by simp; omega)]
          exact hu9
        · rw [getElem!_set_ne _ _ _ _ (Ne.symm hp0)]
          exact hinv p (by omega)
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have : it.start.val = 128 := by omega
      rw [this] at hinv
      exact hinv

/-- `mlkem_frombytes` unpacks each coefficient of FIPS 203's `ByteDecode_12`
as its raw 12-bit field: in `[0, 4096)`, so congruent to the spec's modulo
`q` but not yet reduced, which the `mlkem_reduce` after it does. -/
theorem mlkem_frombytes_spec (r : Array I16 256#usize) (a : Array U8 384#usize) :
    low.generic.mlkem.mlkem_frombytes r a ⦃ r' =>
      Holds 0 4095 256 r'.val (ByteDecode (toVec (32 * 12) a.val a.property) (by omega)) ⦄ := by
  unfold low.generic.mlkem.mlkem_frombytes
  apply WP.spec_mono (frombytes_loop_spec a _ r rfl rfl)
  intro r' hr' p hp
  obtain ⟨h0, h1, hbits⟩ := hr' p hp
  refine ⟨h0, by omega, ?_⟩
  rw [ByteDecode_get _ _ _ hp]
  have hsum : (∑ j : Fin 12, (bit (toVec (32 * 12) a.val a.property) (p * 12 + j)).toNat * 2 ^ j.val) =
      (r'.val[p]!).val.toNat := by
    rw [← Nat.mod_eq_of_lt (show (r'.val[p]!).val.toNat < 2 ^ 12 by omega), mod_two_pow_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bit_toVec, hbits j j.isLt, Nat.mul_comm p]
  rw [hsum, ← Int.toNat_of_nonneg h0]
  simp [m]

end MlKemGeneric

end rind.aarch64
