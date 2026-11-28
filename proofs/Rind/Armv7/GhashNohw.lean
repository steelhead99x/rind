import Rind.Armv7.Funs
import Rind.GcmSpec
open Aeneas Aeneas.Std Result rind.vale rind.simd Polynomial

/-!
# armv7's integer GHASH

`low/generic/ghash_nohw.rs`, aws-lc's `gcm_nohw.c` in Rust, in its 32-bit
configuration. `gcm_mul32_nohw` multiplies carry-less by integer multiplies
of operands masked to every fourth bit, which `bv_decide` checks at every
input (`mul32_bv`); `gcm_mul64_split` and `gcm_polyval_nohw` take the
Karatsuba product of 64-bit and then 128-bit halves; and the reduction folds
by the reflected modulus to the same Montgomery residue as the PCLMULQDQ
code's `mulModel` (`polyval_bv`), so each block's multiply is Vale's
`gf128_mul_rev` by the key, which `NohwTable::new` shifts as `shift_key_1`
does (`table_new_spec`), and `NohwTable::ghash` is GHASH on the blocks'
polynomials (`ghash_spec`).
-/

local notation "P" => Polynomial (ZMod 2)

namespace rind.armv7

open low.portable.ghash_nohw

/-! ## The 32-bit carry-less multiply -/

/-- The carry-less product of `a` and `b`'s low `k` bits. -/
def clmul32Aux (a b : BitVec 32) : Nat → BitVec 64
  | 0 => 0
  | k + 1 => clmul32Aux a b k ^^^ (if b.getLsbD k then a.setWidth 64 <<< k else 0)

/-- The carry-less product of two 32-bit words. -/
def clmul32 (a b : BitVec 32) : BitVec 64 := clmul32Aux a b 32

theorem toPoly_shift32 (a : BitVec 32) (k : ℕ) (hk : k < 32) :
    toPoly (a.setWidth 64 <<< k) = X ^ k * toPoly a := by
  ext j
  simp only [coeff_toPoly, coeff_X_pow_mul', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h1 : k ≤ j
  · simp only [h1, ite_true]
    by_cases h2 : j < 64
    · simp [h2, show ¬ j < k by omega, show j - k < 64 by omega]
    · rw [BitVec.getLsbD_of_ge a (j - k) (by omega)]; simp [h2]
  · simp [h1, show j < k by omega]

theorem toPoly_clmul32Aux (a b : BitVec 32) (k : ℕ) (hk : k ≤ 32) :
    toPoly (clmul32Aux a b k) = toPoly a * ∑ i ∈ Finset.range k, if b.getLsbD i then X ^ i else 0 := by
  induction k with
  | zero => simp [clmul32Aux, toPoly_zero']
  | succ k ih =>
    rw [clmul32Aux, toPoly_xor, ih (by omega), Finset.sum_range_succ, mul_add]
    by_cases hb : b.getLsbD k
    · simp only [hb, ite_true, toPoly_shift32 a k (by omega), mul_comm]
    · simp only [hb, Bool.false_eq_true, ite_false, toPoly_zero, mul_zero]

theorem toPoly_clmul32 (a b : BitVec 32) : toPoly (clmul32 a b) = toPoly a * toPoly b := by
  rw [clmul32, toPoly_clmul32Aux a b 32 le_rfl]
  rfl

/-- `gcm_mul32_nohw`'s masked integer products, on bits. -/
def mul32Masked (a b : BitVec 32) : BitVec 64 :=
  let m := fun x y : BitVec 32 => x.setWidth 64 * y.setWidth 64
  let a0 := a &&& 0x11111111#32
  let a1 := a &&& 0x22222222#32
  let a2 := a &&& 0x44444444#32
  let a3 := a &&& 0x88888888#32
  let b0 := b &&& 0x11111111#32
  let b1 := b &&& 0x22222222#32
  let b2 := b &&& 0x44444444#32
  let b3 := b &&& 0x88888888#32
  let c0 := m a0 b0 ^^^ m a1 b3 ^^^ m a2 b2 ^^^ m a3 b1
  let c1 := m a0 b1 ^^^ m a1 b0 ^^^ m a2 b3 ^^^ m a3 b2
  let c2 := m a0 b2 ^^^ m a1 b1 ^^^ m a2 b0 ^^^ m a3 b3
  let c3 := m a0 b3 ^^^ m a1 b2 ^^^ m a2 b1 ^^^ m a3 b0
  (c0 &&& 0x1111111111111111#64) ||| (c1 &&& 0x2222222222222222#64) |||
    (c2 &&& 0x4444444444444444#64) ||| (c3 &&& 0x8888888888888888#64)

/-- No carry of the masked products reaches a bit `gcm_mul32_nohw` keeps: one
term every four bits sums at most eight ones, below 16. -/
theorem mul32_bv (a b : BitVec 32) : mul32Masked a b = clmul32 a b := by
  simp only [mul32Masked, clmul32, clmul32Aux]
  bv_decide (config := { timeout := 600 })

theorem mul32_call_spec (x y : U32) :
    gcm_mul32_nohw.closure.Insts.CoreOpsFunctionFnPairU32U32U64.call () (x, y) ⦃ r =>
      r.bv = x.bv.setWidth 64 * y.bv.setWidth 64 ⦄ := by
  unfold gcm_mul32_nohw.closure.Insts.CoreOpsFunctionFnPairU32U32U64.call
  simp only [lift, bind_ok]
  have hx := x.hBounds
  have hy := y.hBounds
  have := Nat.mul_lt_mul'' hx hy
  step as ⟨r, hr⟩
  apply BitVec.eq_of_toNat_eq
  simp only [UScalar.bv_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, hr,
    core.convert.num.FromU64U32.from_val_eq]
  simp only [UScalarTy.numBits] at *
  rw [Nat.mod_eq_of_lt (by omega : x.val < 2 ^ 64), Nat.mod_eq_of_lt (by omega : y.val < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]

/-- `gcm_mul32_nohw` is the carry-less product. -/
@[step]
theorem gcm_mul32_nohw_spec (a b : U32) :
    gcm_mul32_nohw a b ⦃ r => toPoly r.bv = toPoly a.bv * toPoly b.bv ⦄ := by
  unfold gcm_mul32_nohw
  simp only [lift, bind_ok]
  step with mul32_call_spec as ⟨p0, h0⟩
  step with mul32_call_spec as ⟨p1, h1⟩
  step with mul32_call_spec as ⟨p2, h2⟩
  step with mul32_call_spec as ⟨p3, h3⟩
  step with mul32_call_spec as ⟨p4, h4⟩
  step with mul32_call_spec as ⟨p5, h5⟩
  step with mul32_call_spec as ⟨p6, h6⟩
  step with mul32_call_spec as ⟨p7, h7⟩
  step with mul32_call_spec as ⟨p8, h8⟩
  step with mul32_call_spec as ⟨p9, h9⟩
  step with mul32_call_spec as ⟨p10, h10⟩
  step with mul32_call_spec as ⟨p11, h11⟩
  step with mul32_call_spec as ⟨p12, h12⟩
  step with mul32_call_spec as ⟨p13, h13⟩
  step with mul32_call_spec as ⟨p14, h14⟩
  step with mul32_call_spec as ⟨p15, h15⟩
  rw [← toPoly_clmul32, ← mul32_bv]
  congr 1
  simp only [UScalar.bv_or, UScalar.bv_and, UScalar.bv_xor, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, mul32Masked]
  rfl

/-! ## The 64-bit and 128-bit Karatsuba products -/

theorem toPoly_split32 (x : BitVec 64) :
    toPoly x = toPoly (x.setWidth 32) + X ^ 32 * toPoly ((x >>> 32).setWidth 32) := by
  ext j
  simp only [coeff_add, coeff_toPoly, coeff_X_pow_mul', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · simp [h, show ¬ 32 ≤ j by omega]
  · simp only [h, decide_false, Bool.false_and, show 32 ≤ j by omega, ite_true, Bool.false_eq_true,
      ite_false, zero_add]
    by_cases h2 : j - 32 < 32
    · simp [h2, show 32 + (j - 32) = j by omega]
    · rw [BitVec.getLsbD_of_ge x j (by omega)]; simp [h2]

theorem toPoly_shift_split (m : BitVec 64) :
    toPoly (m <<< 32) + X ^ 64 * toPoly (m >>> 32) = X ^ 32 * toPoly m := by
  ext j
  simp only [coeff_add, coeff_toPoly, coeff_X_pow_mul', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h32 : j < 32
  · simp [h32, show ¬ 64 ≤ j by omega, show ¬ 32 ≤ j by omega]
  by_cases h64 : j < 64
  · simp only [h64, decide_true, h32, decide_false, Bool.not_false, Bool.true_and, show ¬ 64 ≤ j by omega,
      ite_false, add_zero, show 32 ≤ j by omega, ite_true]
  · simp only [h64, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, zero_add,
      show 64 ≤ j by omega, ite_true, show 32 ≤ j by omega]
    by_cases h96 : j < 96
    · simp [show 32 + (j - 64) = j - 32 by omega, show j - 32 < 64 by omega]
    · rw [BitVec.getLsbD_of_ge m (32 + (j - 64)) (by omega), BitVec.getLsbD_of_ge m (j - 32) (by omega)]

/-- `gcm_mul64_split` is the carry-less product, its low word first. -/
@[step]
theorem gcm_mul64_split_spec (a b : U64) :
    gcm_mul64_split a b ⦃ r => toPoly r.1.bv + X ^ 64 * toPoly r.2.bv = toPoly a.bv * toPoly b.bv ⦄ := by
  unfold gcm_mul64_split
  step*
  have hc : ∀ x : U64, (UScalar.cast UScalarTy.U32 x).bv = x.bv.setWidth 32 := fun x => by
    rw [UScalar.cast_bv_eq]; rfl
  have hA := toPoly_split32 a.bv
  have hB := toPoly_split32 b.bv
  have hs := toPoly_shift_split mid.bv
  rw [← i_post1] at hA
  rw [← i1_post1] at hB
  rw [← hc, ← a0_post, ← hc, ← a1_post] at hA
  rw [← hc, ← b0_post, ← hc, ← b1_post] at hB
  simp only [i7_post1, i9_post1, i6_post1, i8_post1, toPoly_xor]
  rw [hA, hB]
  simp only [mid_post1, i5_post1, toPoly_xor, i4_post, i2_post1, i3_post1, lo_post, hi_post] at hs
  simp only [mid_post1, i5_post1, lo_post, hi_post]
  linear_combination hs + (X ^ 32 * (toPoly a0.bv * toPoly b0.bv + toPoly a1.bv * toPoly b1.bv)) * two_eq_zero_P

/-! ## The reduction -/

theorem clmul_c64 (x : BitVec 64) :
    clmul c64 x = x.setWidth 128 <<< 63 ^^^ x.setWidth 128 <<< 62 ^^^ x.setWidth 128 <<< 57 := by
  apply toPoly_inj
  rw [toPoly_clmul, toPoly_c64, toPoly_xor, toPoly_xor, toPoly_shift x 63 (by omega), toPoly_shift x 62 (by omega),
    toPoly_shift x 57 (by omega)]
  ring

/-- `gcm_polyval_nohw`'s reduction of the product `r3:r2:r1:r0`, the high
word first. -/
def nohwReduce (r0 r1 r2 r3 : BitVec 64) : BitVec 128 :=
  let r1 := r1 ^^^ (r0 <<< 63 ^^^ r0 <<< 62 ^^^ r0 <<< 57)
  let r2 := r2 ^^^ r0 ^^^ r0 >>> 1 ^^^ r1 <<< 63 ^^^ r0 >>> 2 ^^^ r1 <<< 62 ^^^ r0 >>> 7 ^^^ r1 <<< 57
  let r3 := r3 ^^^ r1 ^^^ r1 >>> 1 ^^^ r1 >>> 2 ^^^ r1 >>> 7
  r3 ++ r2

/-- The fold by `x^-1`, `x^-2`, and `x^-7` is the PCLMULQDQ code's fold by
the reflected modulus, of the product's low and high halves. -/
theorem reduce_bv (r0 r1 r2 r3 : BitVec 64) :
    nohwReduce r0 r1 r2 r3 = reduceModel (r1 ++ r0) ((r1 ++ r0) ^^^ (r3 ++ r2)) (r3 ++ r2) := by
  simp only [nohwReduce, reduceModel, clmul_c64, swap, lo, hi]
  bv_decide

/-- The product's halves reduce to its Montgomery residue, `mulModel`'s. -/
theorem reduce_mulModel (r0 r1 r2 r3 : BitVec 64) (a b : BitVec 128)
    (h : toPoly (r1 ++ r0) + X ^ 128 * toPoly (r3 ++ r2) = toPoly a * toPoly b) :
    nohwReduce r0 r1 r2 r3 = mulModel a b := by
  apply toPoly_inj
  rw [reduce_bv]
  have := reduce_sum (r1 ++ r0) ((r1 ++ r0) ^^^ (r3 ++ r2)) (r3 ++ r2) [(a, b)] (by
    simp only [kara, toPoly_xor, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ← h]
    linear_combination (X ^ 64 * (toPoly (r1 ++ r0) + toPoly (r3 ++ r2))) * two_eq_zero_P)
  simpa using this

/-- `gcm_polyval_nohw` multiplies the state by the table's key, both high
word last, as the PCLMULQDQ code's `mulModel` does. -/
@[step]
theorem gcm_polyval_nohw_spec (xi : Std.Array U64 2#usize) (h : NohwTable) :
    gcm_polyval_nohw xi h ⦃ r => r.val[1]!.bv ++ r.val[0]!.bv =
      mulModel (xi.val[1]!.bv ++ xi.val[0]!.bv) (h.hi.bv ++ h.lo.bv) ⦄ := by
  unfold gcm_polyval_nohw
  step*
  have hr : r34.bv ++ r28.bv = nohwReduce r0.bv r11.bv r21.bv r3.bv := by
    simp only [nohwReduce, r34_post1, r33_post1, r32_post1, r31_post1, r12_post1, i10_post1, i8_post1, i6_post1,
      i7_post1, i9_post1, i13_post1, i16_post1, i19_post1, r28_post1, r27_post1, r26_post1, r25_post1, r24_post1,
      r23_post1, r22_post1, i11_post1, i12_post1, i14_post1, i15_post1, i17_post1, i18_post1]
  have hx0 : xi.val[0]! = i := by rw [i_post, getElem!_pos xi.val 0 (by simp)]
  have hx1 : xi.val[1]! = i1 := by rw [i1_post, getElem!_pos xi.val 1 (by simp)]
  simp only [Std.Array.make, Std.Array.from_val, List.getElem!_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some, hx0, hx1]
  rw [hr]
  apply reduce_mulModel
  simp only [toPoly_append, toPoly_xor, r11_post1, mid01_post1, i4_post1, r21_post1, mid11_post1, i5_post1]
  simp only [i2_post1, i3_post1, toPoly_xor] at mid0_post
  linear_combination (1 + X ^ 64) * r0_post + (X ^ 128 + X ^ 64) * r2_post + X ^ 64 * mid0_post +
    X ^ 64 * (toPoly i.bv * toPoly h.lo.bv + toPoly i1.bv * toPoly h.hi.bv) * two_eq_zero_P

/-! ## The key -/

theorem leQuad32ToBytes_leBytesToQuad32' (M : List (BitVec 8)) (h : M.length = 16) :
    leQuad32ToBytes (leBytesToQuad32 M) = M := by
  apply List.ext_getElem (by simp [leQuad32ToBytes, h])
  intro i h1 h2
  have hi : i < 16 := by simpa [leQuad32ToBytes] using h1
  simp only [leQuad32ToBytes, List.getElem_map, List.getElem_range]
  have := byte_leBytesToQuad32 M hi
  rw [byte] at this
  rw [this, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- `u128::from_be_bytes` of a block is the block as GHASH reads it. -/
theorem fromBE_blockBE (a : Std.Array U8 16#usize) :
    (BitVec.fromBEBytes (a.val.map U8.bv)).cast (by simp) = blockBE a.val := by
  rw [blockBE, loadBytes, reverseBytesQuad32, leQuad32ToBytes_leBytesToQuad32' _ (by simp), leBytesToQuad32]
  apply BitVec.eq_of_toNat_eq
  have hb := (BitVec.fromLEBytes ((a.val.map (·.bv)).reverse)).isLt
  simp only [List.length_reverse, List.length_map, Std.Array.property] at hb
  simp only [BitVec.fromBEBytes, BitVec.toNat_setWidth, BitVec.toNat_cast]
  rw [Nat.mod_eq_of_lt (by simpa using hb)]

theorem from_be_blockBE (a : Std.Array U8 16#usize) : (core.num.U128.from_be_bytes a).bv = blockBE a.val :=
  fromBE_blockBE a

/-- A `u128`'s big-endian bytes are the block GHASH reads as it. -/
theorem blockBE_to_be (u : Std.U128) : blockBE (core.num.U128.to_be_bytes u).val = u.bv := by
  have hb : (core.num.U128.to_be_bytes u).val.map (·.bv) = u.bv.toBEBytes := by
    simp only [core.num.U128.to_be_bytes, Std.Array.from_val, List.map_map]
    exact List.map_id _
  have hl : u.bv.toLEBytes.length = 16 := by simp
  rw [blockBE, loadBytes, hb, BitVec.toBEBytes, reverseBytesQuad32,
    leQuad32ToBytes_leBytesToQuad32' _ (by simp [hl]), List.reverse_reverse, leBytesToQuad32,
    BitVec.fromLEBytes_toLEBytes (by decide)]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp [hk]

/-- A table holds the GHASH key `H` shifted as Vale's `shift_key_1` does, its
high word first. -/
def TableFor (H : P) (t : NohwTable) : Prop :=
  toPoly (t.hi.bv ++ t.lo.bv) = shiftKey1 128 gf128ModulusLowTerms H

/-- `mulX_POLYVAL` on the key's 64-bit halves is `skBV`. -/
theorem skBV_halves (x : BitVec 128) :
    let hi := (x >>> 64).setWidth 64
    let lo := x.setWidth 64
    let carry := 0#64 - hi >>> 63
    ((hi <<< 1 ||| lo >>> 63) ^^^ (carry &&& 0xc200000000000000#64)) ++ (lo <<< 1 ^^^ (carry &&& 1#64)) =
      skBV x := by
  simp only [skBV]
  bv_decide

/-- `NohwTable::new` shifts the key, as POLYVAL's `mulX_POLYVAL` does, which
is `skBV`. -/
theorem table_new_spec (h : Std.Array U8 16#usize) :
    NohwTable.new h ⦃ t => TableFor (toPoly (blockBE h.val)) t ⦄ := by
  unfold NohwTable.new
  step*
  have hh : blockBE h.val = h1.bv := by rw [h1_post, fromBE_blockBE]
  have c0 : (0#u64).bv = 0#64 := rfl
  have c1 : (1#u64).bv = 1#64 := rfl
  have c2 : (13979173243358019584#u64).bv = 0xc200000000000000#64 := rfl
  have hb : hi2.bv ++ lo2.bv = skBV h1.bv := by
    simp only [hi2_post1, hi1_post1, i2_post1, i3_post1, i5_post1, lo2_post1, lo1_post1, i4_post1,
      i_post1, i1_post1, carry_post, hi_post, lo_post, UScalar.cast_bv_eq,
      core.num.U64.wrapping_sub_bv_eq, c0, c1, c2, UScalarTy.U64_numBits_eq]
    exact skBV_halves h1.bv
  simp only [TableFor, hb, hh, toPoly_skBV]

/-! ## GHASH -/

/-- The state as GHASH multiplies it: the high word, then the low. -/
def low.portable.ghash_nohw.state (s : Std.Array U64 2#usize) : BitVec 128 := s.val[1]!.bv ++ s.val[0]!.bv

theorem halves_eq (x : BitVec 128) : (x >>> 64).setWidth 64 ++ x.setWidth 64 = x := by bv_decide

theorem xor_halves (s0 s1 : BitVec 64) (b : BitVec 128) :
    (s1 ^^^ (b >>> 64).setWidth 64) ++ (s0 ^^^ b.setWidth 64) = (s1 ++ s0) ^^^ b := by bv_decide

theorem join_halves (s0 s1 : BitVec 64) : s1.setWidth 128 <<< 64 ||| s0.setWidth 128 = s1 ++ s0 := by bv_decide

/-- The blocks from `i` on folded into the state. -/
theorem ghash_loop_spec (H : P) (hH : Small H) (t : NohwTable) (ht : TableFor H t)
    (input : Slice (Std.Array U8 16#usize)) (c : P) (i : Nat) (s : Std.Array U64 2#usize)
    (hi : i ≤ input.length)
    (hs : toPoly (state s) = ghashPoly H c ((input.val.take i).map fun b => toPoly (blockBE b.val))) :
    NohwTable.ghash_loop ⟨input, i⟩ t s ⦃ r =>
      toPoly (state r) = ghashPoly H c (input.val.map fun b => toPoly (blockBE b.val)) ⦄ := by
  unfold NohwTable.ghash_loop
  apply loop.spec_decr_nat (fun x => input.length - x.1.i)
    (fun x => x.1.slice = input ∧ x.1.i ≤ input.length ∧
      toPoly (state x.2) = ghashPoly H c ((input.val.take x.1.i).map fun b => toPoly (blockBE b.val)))
  · rintro ⟨⟨sl, j⟩, st⟩ ⟨hsl, hj, hst⟩
    simp only at hsl hj hst ⊢
    subst hsl
    unfold NohwTable.ghash_loop.body
    simp only [core.slice.iter.IteratorSliceIter.next]
    by_cases hlt : j < sl.length
    · rw [dite_eq_left (by simpa [Slice.len] using hlt)]
      simp only [bind_ok, lift]
      step*
      refine ⟨by omega, ?_, by omega⟩
      have e1 : swapped2.val[1]! = i5 ^^^ UScalar.cast .U64 i3 := by rw [swapped2_post]; simp
      have e0 : swapped2.val[0]! = i1 ^^^ UScalar.cast .U64 (core.num.U128.from_be_bytes sl[j]) := by
        rw [swapped2_post, swapped1_post]; simp; rfl
      have f1 : i5 = st.val[1]! := by rw [i5_post, swapped1_post]; simp
      have f0 : i1 = st.val[0]! := by rw [i1_post]; simp
      have h2 : state swapped2 = state st ^^^ blockBE sl[j].val := by
        rw [← from_be_blockBE, state, state, e1, e0, f1, f0, ← xor_halves]
        simp only [UScalar.bv_xor, UScalar.cast_bv_eq, i3_post1, UScalarTy.U64_numBits_eq]
        rfl
      have h3 : toPoly (state swapped3) = gf128MulRev (toPoly (state swapped2)) H := by
        rw [state, swapped3_post]
        exact mul_data _ _ H hH ht
      have ht' : (sl.val.take (j + 1)) = sl.val.take j ++ [sl[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simpa [Slice.length] using hlt)]
        rfl
      rw [h3, h2, toPoly_xor, hst, ht', List.map_append, ghashPoly_append, List.map_singleton, ghashPoly_cons,
        ghashPoly_nil]
    · rw [dite_eq_right (by simpa [Slice.len] using hlt)]
      rw [show j = sl.length by omega, List.take_of_length_le (by simp [Slice.length])] at hst
      simp only [bind_ok]
      step*
  · exact ⟨rfl, hi, hs⟩

/-- `NohwTable::ghash` folds the blocks into the state, each XORed in and
multiplied by the key, as GHASH does. -/
theorem ghash_spec (H : P) (hH : Small H) (t : NohwTable) (ht : TableFor H t) (xi : Std.Array U8 16#usize)
    (input : Slice (Std.Array U8 16#usize)) :
    t.ghash xi input ⦃ r =>
      toPoly (blockBE r.val) = ghashPoly H (toPoly (blockBE xi.val)) (input.val.map fun b => toPoly (blockBE b.val)) ⦄ := by
  unfold NohwTable.ghash
  simp only [lift, bind_ok, SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
  step*
  have h0 : toPoly (state (Std.Array.make 2#usize [UScalar.cast UScalarTy.U64 (core.num.U128.from_be_bytes xi),
      UScalar.cast UScalarTy.U64 i1] (by simp))) = toPoly (blockBE xi.val) := by
    rw [← from_be_blockBE, ← halves_eq (core.num.U128.from_be_bytes xi).bv, ← i1_post1]
    simp only [state, Std.Array.make, Std.Array.from_val, List.getElem!_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, UScalar.cast_bv_eq, UScalarTy.U64_numBits_eq]
  step with ghash_loop_spec H hH t ht input (toPoly (blockBE xi.val)) 0 _ (by simp) (by
    rw [h0, List.take_zero, List.map_nil, ghashPoly_nil]) as ⟨sw, hsw⟩
  step*
  rw [blockBE_to_be, ← hsw]
  have g1 : sw.val[1]! = i3 := by rw [i3_post, getElem!_pos sw.val 1 (by simp)]
  have g0 : sw.val[0]! = i6 := by rw [i6_post, getElem!_pos sw.val 0 (by simp)]
  have hj : (i5 ||| core.convert.num.FromU128U64.from i6).bv = state sw := by
    rw [state, g1, g0, ← join_halves]
    simp only [UScalar.bv_or, i5_post1, core.convert.num.FromU128U64.from_bv_eq, UScalarTy.U128_numBits_eq]
  exact congrArg toPoly hj

end rind.armv7
