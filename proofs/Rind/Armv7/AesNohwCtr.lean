import Rind.Armv7.AesNohwKey
import Rind.GcmSpec
import Rind.AesModesBytes
open Aeneas Aeneas.Std Result rind.vale rind.simd

/-!
# The bitsliced AES's counter mode

`Schedule::ctr32` XORs GCTR's keystream into its input: SP 800-38D's GCTR,
Vale's `gctr_encrypt_LE`, from the counter block its `ivec` holds, the low
32 bits of each next one incremented with wrapping. The proof goes byte by
byte: byte `j` of GCTR's output is byte `j` of its input XORed with byte
`j % 16` of the cipher of counter block `j / 16`.
-/

namespace rind.armv7

open low.portable.aes_nohw

/-! ## Appending -/

theorem getElem!_append_lt {α : Type _} [Inhabited α] (a b : List α) {j : Nat} (h : j < a.length) :
    (a ++ b)[j]! = a[j]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

theorem getElem!_append_ge {α : Type _} [Inhabited α] (a b : List α) {j : Nat} (h : a.length ≤ j) :
    (a ++ b)[j]! = b[j - a.length]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right h]

/-! ## Counter blocks -/

/-- A word's big-endian bytes, from the most significant. -/
theorem toBEBytes_32 (x : BitVec 32) :
    x.toBEBytes = [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < 4 := by simpa using h2
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hl : x.toLEBytes.length = 4 := by simp
  simp only [BitVec.toBEBytes, List.getElem_reverse]
  rw [BitVec.getElem_toLEBytes_eq_getElem _ _ _ _ hj (by rw [hl]; omega)]
  interval_cases i <;> simp [hl] <;> rw [BitVec.getLsbD_eq_getElem (by omega)]

/-- The block `keystream` builds for counter `lane32 J 0 + n`, from `ivec`
holding counter block `J`, is counter block `inc32 J n`. -/
theorem ctr_blockQ (J : Quad32) (ivec a : Std.Array U8 16#usize) (hiv : blockQ ivec = reverseBytesQuad32 J)
    (n : Nat) (ha : ∀ m < 12, a.val[m]! = ivec.val[m]!)
    (hb : ∀ m < 4, (a.val[12 + m]!).bv = (lane32 J 0 + BitVec.ofNat 32 n).toBEBytes[m]!) :
    blockQ a = reverseBytesQuad32 (inc32 J n) := by
  apply eq_of_byte_eq; intro m hm
  rw [blockQ, byte_ofBytes _ hm, byte_reverseBytes _ hm]
  by_cases h12 : m < 12
  · have hv : ivec.val[m]!.bv = byte (blockQ ivec) m := by rw [blockQ, byte_ofBytes _ hm]
    rw [ha m h12, hv, hiv, byte_reverseBytes _ hm]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [getLsbD_byte _ _ hj, inc32, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    rw [ite_eq_right (by omega)]
    simp [show 8 * (15 - m) + j - 32 < 96 by omega, show 32 + (8 * (15 - m) + j - 32) = 8 * (15 - m) + j by omega]
  · obtain ⟨k, rfl⟩ : ∃ k, m = 12 + k := ⟨m - 12, by omega⟩
    rw [hb k (by omega), inc32_eq, toBEBytes_32]
    generalize lane32 J 0 + BitVec.ofNat 32 n = c
    have hk : k < 4 := by omega
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [getLsbD_byte _ _ hj]
    interval_cases k <;> simp [hj] <;> rw [BitVec.getLsbD_append, ite_eq_left (by omega)]

/-! ## The keystream -/

/-- A schedule holding the round keys of `kw` under `alg` in both lanes. -/
def Keyed (alg : Algorithm) (kw : List (BitVec 32)) (s : Schedule) : Prop :=
  s.rounds.val = nr alg ∧ ∀ q ≤ nr alg, ∀ i < 2, (s.keys.val[q]!).block i = roundKey alg kw q

/-- A keyed schedule encrypts both blocks of a batch with FIPS 197's cipher. -/
theorem encrypt_batch_aes (alg : Algorithm) (kw : List (BitVec 32)) (s : Schedule) (hs : Keyed alg kw s)
    (b : Batch) : s.encrypt_batch b ⦃ r => ∀ i < 2, r.block i = aesEncrypt alg kw (b.block i) ⦄ := by
  have hn : 1 ≤ nr alg ∧ nr alg ≤ 14 := by cases alg <;> decide
  have hr := hs.1
  apply WP.spec_mono (encrypt_batch_spec s b (by omega) (by omega))
  intro r h i hi
  rw [h i hi, aesEncrypt, evalCipher_eq, hs.1]
  apply cipherRounds_congr
  intro q hq
  rw [roundKeys_get s i q (by omega), hs.2 q hq i hi, keyToRoundKeys_eq, getElem!_range_map _ (by omega)]

theorem schedule_keystream_loop_spec (J : Quad32) (ivec : Std.Array U8 16#usize) (hiv : blockQ ivec = reverseBytesQuad32 J)
    (n : Nat) (ctr : U32) (hc : ctr.bv = lane32 J 0 + BitVec.ofNat 32 n)
    (iter : core.ops.range.Range Usize) (ivs : Std.Array (Std.Array U8 16#usize) 2#usize)
    (hs : iter.start.val ≤ 2) (he : iter.end.val = 2)
    (hdone : ∀ k < iter.start.val, blockQ ivs.val[k]! = reverseBytesQuad32 (inc32 J (n + k)))
    (hrest : ∀ k < 2, iter.start.val ≤ k → ivs.val[k]! = ivec) :
    Schedule.keystream_loop iter ctr ivs ⦃ r =>
      ∀ k < 2, blockQ r.val[k]! = reverseBytesQuad32 (inc32 J (n + k)) ⦄ := by
  unfold Schedule.keystream_loop
  apply loop.spec_decr_nat (fun x => 2 - x.1.start.val)
    (fun x => x.1.start.val ≤ 2 ∧ x.1.end.val = 2 ∧
      (∀ k < x.1.start.val, blockQ x.2.val[k]! = reverseBytesQuad32 (inc32 J (n + k))) ∧
      ∀ k < 2, x.1.start.val ≤ k → x.2.val[k]! = ivec)
  · rintro ⟨it, st⟩ ⟨hs, he, hd, hr⟩
    simp only at hs he hd hr ⊢
    unfold Schedule.keystream_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step*
      have hi2 : i2.bv = lane32 J 0 + BitVec.ofNat 32 (n + it.start.val) := by
        have hi1 : i1.bv = BitVec.ofNat 32 it.start.val := by
          apply BitVec.eq_of_toNat_eq
          simp [i1_post]
        rw [i2_post, core.num.U32.wrapping_add_bv_eq, hc, hi1, BitVec.add_assoc, BitVec.ofNat_add]
      have hsti : st.val[it.start.val]! = ivec := hr _ (by omega) le_rfl
      have hfin : (index_mut_back3 a8).val = st.val.set it.start.val a8 := by
        simp [index_mut_back3_post, index_mut_back2_post, index_mut_back1_post, index_mut_back_post]
      have ha8 : a8.val = (((ivec.val.set 12 c0).set 13 c1).set 14 c2).set 15 c3 := by
        rw [getElem!_pos st.val it.start.val (by simp; omega)] at hsti
        simp [a8_post, a7_post, a6_post, a5_post, a4_post, a3_post, a2_post, a1_post, index_mut_back2_post,
          index_mut_back1_post, index_mut_back_post, hsti]
      have hq : blockQ a8 = reverseBytesQuad32 (inc32 J (n + it.start.val)) := by
        apply ctr_blockQ J ivec a8 hiv
        · intro m hm
          rw [ha8]
          simp [List.getElem!_eq_getElem?_getD, show (12 : ℕ) ≠ m by omega,
            show (13 : ℕ) ≠ m by omega, show (14 : ℕ) ≠ m by omega, show (15 : ℕ) ≠ m by omega]
        · intro m hm
          have hab : ∀ m < 4, (a.val[m]!).bv = i2.bv.toBEBytes[m]! := by
            intro m hm
            have hl : m < i2.bv.toBEBytes.length := by simp [BitVec.toBEBytes_length]; omega
            rw [getElem!_pos a.val m (by simp; omega), getElem!_pos _ m hl]
            simp only [a_post, List.getElem_map]
          have e : ∀ m < 4, a8.val[12 + m]! = a.val[m]! := by
            intro m hm; rw [ha8]; interval_cases m <;> simp [c0_post, c1_post, c2_post, c3_post]
          rw [e m hm, hab m hm, hi2]
      refine ⟨by omega, by rw [hen]; omega, ?_, ?_, by omega⟩
      · intro k hk
        rw [hfin]
        by_cases hki : k = it.start.val
        · subst hki
          rw [getElem!_pos _ _ (by simp; omega)]
          simpa using hq
        · rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getElem!_eq_getElem?_getD]
          exact hd k (by omega)
      · intro k hk hk'
        rw [hfin, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getElem!_eq_getElem?_getD]
        exact hr k hk (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro k hk
      exact hd k (by omega)
  · exact ⟨hs, he, hdone, hrest⟩

/-- `keystream` is GCTR's keystream for the first `todo` blocks from counter
block `inc32 J n`, given `ivec` holds `J` and `ctr` its low word plus `n`. -/
theorem schedule_keystream_spec (alg : Algorithm) (kw : List (BitVec 32)) (sch : Schedule) (hs : Keyed alg kw sch)
    (J : Quad32) (ivec : Std.Array U8 16#usize) (hiv : blockQ ivec = reverseBytesQuad32 J)
    (n : Nat) (ctr : U32) (hc : ctr.bv = lane32 J 0 + BitVec.ofNat 32 n) (todo : Usize) (ht : todo.val ≤ 2) :
    sch.keystream ivec ctr todo ⦃ r =>
      ∀ k < todo.val, ∀ m < 16, (r.val[k]!).val[m]!.bv = ksByte alg kw J (16 * (n + k) + m) ⦄ := by
  unfold Schedule.keystream
  simp only [word.BATCH_SIZE]
  step with schedule_keystream_loop_spec J ivec hiv n ctr hc { start := 0#usize, «end» := 2#usize } (Std.Array.repeat 2#usize ivec)
    (by simp) (by simp) (by intro k hk; simp at hk) (by intro k hk _; interval_cases k <;> simp [Std.Array.repeat])
    as ⟨ivs, hivs⟩
  step as ⟨sl, hsl, hsll⟩
  have hsll' : sl.val.length = todo.val := by simpa [Slice.length] using hsll
  step with to_batch_spec sl (by omega) as ⟨b, hb⟩
  step with encrypt_batch_aes alg kw sch hs b as ⟨b1, hb1⟩
  step with Array.index_mut_SliceIndexRangeToUsizeSlice (Std.Array.repeat 2#usize (Std.Array.repeat 16#usize 0#u8))
    { «end» := todo } (by scalar_tac) as ⟨s1, back, hs1, hs1l, hback⟩
  have hs1l' : s1.val.length = todo.val := by simpa [Slice.length] using hs1l
  step with from_batch_spec s1 b1 (by omega) as ⟨s2, hs2l, hs2⟩
  intro k hk m hm
  have hbyte : (s2.val[k]!).val[m]!.bv = byte (blockQ s2.val[k]!) m := by rw [blockQ, byte_ofBytes _ hm]
  have hslk : sl.val[k]! = ivs.val[k]! := by
    rw [hsl, List.getElem!_slice 0 todo.val k _ ⟨by simp; omega, by omega⟩]
    simp [Std.Array.to_slice]
  rw [hback s2, List.getElem!_setSlice!_middle _ _ 0 k ⟨by omega, by omega, by simp; omega⟩, Nat.sub_zero, hbyte,
    hs2 k (by omega), hb1 k (by omega), hb k (by omega), hslk, hivs k (by omega), ksByte,
    show (16 * (n + k) + m) / 16 = n + k by omega, show (16 * (n + k) + m) % 16 = m by omega]

/-! ## `ctr32` -/

theorem fromBE4 (a b c d : BitVec 8) (h : 8 * [a, b, c, d].length = 32) :
    (BitVec.fromBEBytes [a, b, c, d]).cast h = a ++ b ++ c ++ d := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cast, BitVec.fromBEBytes, BitVec.toNat_cast]
  show (BitVec.fromLEBytes [d, c, b, a]).toNat = _
  have e : (BitVec.fromLEBytes [d, c, b, a]).toNat = (BitVec.fromLEBytes [d, c, b, a] : BitVec 32).toNat := rfl
  rw [e, ← BitVec.toNat_eq]
  simp only [BitVec.fromLEBytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
  bv_decide

/-- The counter `ivec`'s last four bytes hold, big-endian, is its block's low word. -/
theorem ivec_ctr (J : Quad32) (ivec : Std.Array U8 16#usize) (hiv : blockQ ivec = reverseBytesQuad32 J) :
    ivec.val[12]!.bv ++ ivec.val[13]!.bv ++ ivec.val[14]!.bv ++ ivec.val[15]!.bv = lane32 J 0 := by
  have hj : J = reverseBytesQuad32 (blockQ ivec) := by rw [hiv, reverseBytesQuad32_involutive]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_lane32, hj, getLsbD_reverseBytesQuad32 _ (by omega), blockQ, getLsbD_ofBytes _ (by omega)]
  simp only [BitVec.getLsbD_append, hk, decide_true, Bool.true_and]
  interval_cases k <;> simp

/-- One 32-byte chunk's bytes from `iter.start` on, XORed with the keystream. -/
theorem ctr32_inner_spec (alg : Algorithm) (kw : List (BitVec 32)) (J : Quad32) (n : Usize)
    (stream : Std.Array (Std.Array U8 16#usize) 2#usize)
    (hst : ∀ k < 2, ∀ m < 16, (stream.val[k]!).val[m]!.bv = ksByte alg kw J (16 * (2 * n.val + k) + m))
    (c0 : Slice (Std.Array U8 32#usize)) (hn : n.val < c0.length)
    (iter : core.ops.range.Range Usize) (chunks : Slice (Std.Array U8 32#usize))
    (hs : iter.start.val ≤ 32) (he : iter.end.val = 32) (hl : chunks.length = c0.length)
    (hother : ∀ q, q ≠ n.val → chunks.val[q]! = c0.val[q]!)
    (hdone : ∀ i < 32, (chunks.val[n.val]!).val[i]!.bv = if i < iter.start.val then
      (c0.val[n.val]!).val[i]!.bv ^^^ ksByte alg kw J (32 * n.val + i) else (c0.val[n.val]!).val[i]!.bv) :
    Schedule.ctr32_loop0_loop0 iter chunks n stream ⦃ r => r.length = c0.length ∧
      (∀ q, q ≠ n.val → r.val[q]! = c0.val[q]!) ∧
      ∀ i < 32, (r.val[n.val]!).val[i]!.bv = (c0.val[n.val]!).val[i]!.bv ^^^ ksByte alg kw J (32 * n.val + i) ⦄ := by
  unfold Schedule.ctr32_loop0_loop0
  apply loop.spec_decr_nat (fun x => 32 - x.1.start.val)
    (fun x => x.1.start.val ≤ 32 ∧ x.1.end.val = 32 ∧ x.2.length = c0.length ∧
      (∀ q, q ≠ n.val → x.2.val[q]! = c0.val[q]!) ∧
      ∀ i < 32, (x.2.val[n.val]!).val[i]!.bv = if i < x.1.start.val then
        (c0.val[n.val]!).val[i]!.bv ^^^ ksByte alg kw J (32 * n.val + i) else (c0.val[n.val]!).val[i]!.bv)
  · rintro ⟨it, ch⟩ ⟨hs, he, hl, ho, hd⟩
    simp only at hs he hl ho hd ⊢
    unfold Schedule.ctr32_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst', hen⟩
      subst ho'
      step*
      have hnl : n.val < ch.val.length := by simp only [Slice.length] at hl hn; omega
      have hfin : (index_mut_back a3).val = ch.val.set n.val a3 := by simp [index_mut_back_post]
      have ha2 : a2 = ch.val[n.val]! := by rw [a2_post, getElem!_pos ch.val n.val hnl]
      have hi4 : i4 = (ch.val[n.val]!).val[it.start.val]! := by
        rw [i4_post, a1_post, getElem!_pos ch.val n.val hnl, getElem!_pos _ it.start.val (by simp; omega)]
      have hi3 : i3.bv = ksByte alg kw J (32 * n.val + it.start.val) := by
        have h1 : i3 = (stream.val[it.start.val / 16]!).val[it.start.val % 16]! := by
          rw [i3_post, a_post, getElem!_pos stream.val (it.start.val / 16) (by simp; omega),
            getElem!_pos _ (it.start.val % 16) (by simp; omega)]
          simp only [i1_post, i2_post]
        rw [h1, hst _ (by omega) _ (by omega)]
        congr 1; omega
      have ha3 : ∀ i < 32, a3.val[i]! = if i = it.start.val then i5 else (ch.val[n.val]!).val[i]! := by
        intro i hi
        rw [a3_post, ha2]
        split
        · rename_i h
          rw [h, Std.Array.set_val_eq, getElem!_pos _ _ (by simp; omega), List.getElem_set_self]
        · simp [Std.Array.set_val_eq, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm ‹_›)]
      refine ⟨by omega, by rw [hen]; omega, by simp [Slice.length, hfin] at hl ⊢; omega, ?_, ?_, by omega⟩
      · intro q hq
        rw [hfin, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hq), ← List.getElem!_eq_getElem?_getD]
        exact ho q hq
      · intro i hi
        rw [hfin, getElem!_pos _ n.val (by simp; omega), List.getElem_set_self, ha3 i hi]
        by_cases hie : i = it.start.val
        · rw [ite_eq_left hie, ite_eq_left (by omega)]
          refine Eq.trans i5_post1 ?_
          have h1 := hd _ hi
          rw [ite_eq_right (by omega)] at h1
          subst hie
          rw [← hi3, ← h1, hi4]
        · rw [ite_eq_right hie, hd i hi]
          by_cases hlt2 : i < it.start.val
          · rw [ite_eq_left hlt2, ite_eq_left (by omega)]
          · rw [ite_eq_right hlt2, ite_eq_right (by omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      simp only [WP.spec_ok]
      refine ⟨hl, ho, fun i hi => ?_⟩
      rw [hd i hi, ite_eq_left (by omega)]
  · exact ⟨hs, he, hl, hother, hdone⟩

/-- Whole 32-byte chunks from `iter.start` on, each XORed with the keystream
of the two counter blocks `keystream` makes for it. -/
theorem ctr32_loop0_spec (alg : Algorithm) (kw : List (BitVec 32)) (sch : Schedule) (hk : Keyed alg kw sch)
    (J : Quad32) (ivec : Std.Array U8 16#usize) (hiv : blockQ ivec = reverseBytesQuad32 J)
    (c0 : Slice (Std.Array U8 32#usize)) (iter : core.ops.range.Range Usize) (ctr : U32)
    (chunks : Slice (Std.Array U8 32#usize))
    (hs : iter.start.val ≤ c0.length) (he : iter.end.val = c0.length) (hl : chunks.length = c0.length)
    (hc : ctr.bv = lane32 J 0 + BitVec.ofNat 32 (2 * iter.start.val))
    (hd : ∀ q < c0.length, ∀ i < 32, (chunks.val[q]!).val[i]!.bv = if q < iter.start.val then
      (c0.val[q]!).val[i]!.bv ^^^ ksByte alg kw J (32 * q + i) else (c0.val[q]!).val[i]!.bv) :
    Schedule.ctr32_loop0 iter sch ivec ctr chunks ⦃ r =>
      r.1.bv = lane32 J 0 + BitVec.ofNat 32 (2 * c0.length) ∧ r.2.length = c0.length ∧
      ∀ q < c0.length, ∀ i < 32,
        (r.2.val[q]!).val[i]!.bv = (c0.val[q]!).val[i]!.bv ^^^ ksByte alg kw J (32 * q + i) ⦄ := by
  unfold Schedule.ctr32_loop0
  apply loop.spec_decr_nat (fun x => c0.length - x.1.start.val)
    (fun x => x.1.start.val ≤ c0.length ∧ x.1.end.val = c0.length ∧ x.2.2.length = c0.length ∧
      x.2.1.bv = lane32 J 0 + BitVec.ofNat 32 (2 * x.1.start.val) ∧
      ∀ q < c0.length, ∀ i < 32, (x.2.2.val[q]!).val[i]!.bv = if q < x.1.start.val then
        (c0.val[q]!).val[i]!.bv ^^^ ksByte alg kw J (32 * q + i) else (c0.val[q]!).val[i]!.bv)
  · rintro ⟨it, ct, ch⟩ ⟨hs, he, hl, hc, hd⟩
    simp only at hs he hl hc hd ⊢
    unfold Schedule.ctr32_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst', hen⟩
      subst ho'
      simp only [word.BATCH_SIZE]
      step with schedule_keystream_spec alg kw sch hk J ivec hiv (2 * it.start.val) ct hc 2#usize (by simp) as ⟨st, hstr⟩
      step as ⟨i, hi⟩
      step with ctr32_inner_spec alg kw J it.start st (fun k hk m hm => by
          rw [hstr k (by simpa using hk) m hm]) ch (by omega) { start := 0#usize, «end» := i } ch
        (by simp) (by simp [hi]) rfl (fun _ _ => rfl) (fun i _ => by simp) as ⟨ch1, hl1, ho1, hd1⟩
      step*
      refine ⟨by omega, by rw [hen]; omega, by omega, ?_, ?_, by omega⟩
      · rw [ctr1_post, core.num.U32.wrapping_add_bv_eq, hc, BitVec.add_assoc, hst']
        congr 1
        rw [show 2 * (it.start.val + 1) = 2 * it.start.val + 2 by omega, BitVec.ofNat_add]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [i1_post]
      · intro q hq m hm
        by_cases hqs : q = it.start.val
        · subst hqs
          rw [hd1 m hm, hd _ hq m hm, ite_eq_right (by omega), ite_eq_left (by omega)]
        · rw [ho1 q hqs, hd q hq m hm]
          by_cases hq2 : q < it.start.val
          · rw [ite_eq_left hq2, ite_eq_left (by omega)]
          · rw [ite_eq_right hq2, ite_eq_right (by omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      simp only [WP.spec_ok]
      refine ⟨by rw [hc, show it.start.val = c0.length by omega], hl, fun q hq i hi => ?_⟩
      rw [hd q hq i hi, ite_eq_left (by omega)]
  · exact ⟨hs, he, hl, hc, hd⟩

/-- The bytes past the last whole chunk, from `iter.start` on, XORed with the
keystream of up to two more counter blocks. -/
theorem ctr32_loop1_spec (alg : Algorithm) (kw : List (BitVec 32)) (J : Quad32)
    (stream : Std.Array (Std.Array U8 16#usize) 2#usize) (base todo : Nat) (htodo : todo ≤ 2)
    (hst : ∀ k < todo, ∀ m < 16, (stream.val[k]!).val[m]!.bv = ksByte alg kw J (16 * (base + k) + m))
    (t0 : Slice U8) (ht : t0.length ≤ 16 * todo) (iter : core.ops.range.Range Usize) (tail : Slice U8)
    (hs : iter.start.val ≤ t0.length) (he : iter.end.val = t0.length) (hl : tail.length = t0.length)
    (hd : ∀ i < t0.length, tail.val[i]!.bv = if i < iter.start.val then
      t0.val[i]!.bv ^^^ ksByte alg kw J (16 * base + i) else t0.val[i]!.bv) :
    Schedule.ctr32_loop1 iter tail stream ⦃ r => r.length = t0.length ∧
      ∀ i < t0.length, r.val[i]!.bv = t0.val[i]!.bv ^^^ ksByte alg kw J (16 * base + i) ⦄ := by
  unfold Schedule.ctr32_loop1
  apply loop.spec_decr_nat (fun x => t0.length - x.1.start.val)
    (fun x => x.1.start.val ≤ t0.length ∧ x.1.end.val = t0.length ∧ x.2.length = t0.length ∧
      ∀ i < t0.length, x.2.val[i]!.bv = if i < x.1.start.val then
        t0.val[i]!.bv ^^^ ksByte alg kw J (16 * base + i) else t0.val[i]!.bv)
  · rintro ⟨it, tl⟩ ⟨hs, he, hl, hd⟩
    simp only at hs he hl hd ⊢
    unfold Schedule.ctr32_loop1.body
    have e0 : t0.length = t0.val.length := rfl
    have e1 : tl.length = tl.val.length := rfl
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst', hen⟩
      subst ho'
      step*
      have hi3 : i3.bv = ksByte alg kw J (16 * base + it.start.val) := by
        have h1 : i3 = (stream.val[it.start.val / 16]!).val[it.start.val % 16]! := by
          rw [i3_post, a_post, getElem!_pos stream.val (it.start.val / 16) (by simp; omega),
            getElem!_pos _ (it.start.val % 16) (by simp; omega)]
          simp only [i1_post, i2_post]
        rw [h1, hst _ (by omega) _ (by omega)]
        congr 1; omega
      have hi4 : i4 = tl.val[it.start.val]! := by
        rw [i4_post, getElem!_pos tl.val it.start.val (by simp [Slice.length] at hl; omega)]
      refine ⟨by omega, by rw [hen]; omega, by simp [s_post, Slice.length] at hl ⊢; omega, ?_, by omega⟩
      intro i hi
      rw [s_post, Slice.set_val_eq]
      by_cases hie : i = it.start.val
      · subst hie
        rw [getElem!_pos _ _ (by simp [Slice.length] at hl ⊢; omega), List.getElem_set_self, ite_eq_left (by omega)]
        refine Eq.trans i5_post1 ?_
        have h1 := hd _ hi
        rw [ite_eq_right (by omega)] at h1
        rw [← hi3, ← h1, hi4]
      · rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hie), ← List.getElem!_eq_getElem?_getD,
          hd i hi]
        by_cases hlt2 : i < it.start.val
        · rw [ite_eq_left hlt2, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt2, ite_eq_right (by omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      simp only [WP.spec_ok]
      refine ⟨hl, fun i hi => ?_⟩
      rw [hd i hi, ite_eq_left (by omega)]
  · exact ⟨hs, he, hl, hd⟩

theorem div_ceil_spec (a b : Usize) (hb : b.val ≠ 0) :
    core.num.Usize.div_ceil a b ⦃ r => r.val = (a.val + b.val - 1) / b.val ⦄ := by
  simp [core.num.Usize.div_ceil, hb]

/-- `ctr32` XORs GCTR's keystream from counter block `J` into `inout`, given
`ivec` holds `J`. -/
theorem ctr32_spec (alg : Algorithm) (kw : List (BitVec 32)) (sch : Schedule) (hk : Keyed alg kw sch)
    (J : Quad32) (ivec : Std.Array U8 16#usize) (hiv : blockQ ivec = reverseBytesQuad32 J) (inout : Slice U8) :
    sch.ctr32 ivec inout ⦃ r => r.length = inout.length ∧
      ∀ j < inout.length, r.val[j]!.bv = inout.val[j]!.bv ^^^ ksByte alg kw J j ⦄ := by
  unfold Schedule.ctr32
  step*
  have hmax := Slice.length_ineq inout
  have hv : c0.bv ++ c1.bv ++ c2.bv ++ c3.bv = lane32 J 0 := by
    rw [← ivec_ctr J ivec hiv, c0_post, c1_post, c2_post, c3_post, getElem!_pos ivec.val 12 (by simp),
      getElem!_pos ivec.val 13 (by simp), getElem!_pos ivec.val 14 (by simp), getElem!_pos ivec.val 15 (by simp)]
  have hctr : ctr.bv = lane32 J 0 + BitVec.ofNat 32 (2 * (0#usize : Usize).val) := by
    rw [show (2 * (0#usize : Usize).val) = 0 from rfl, BitVec.add_zero, ← hv]
    exact ctr_post.trans (fromBE4 _ _ _ _ _)
  step with ctr32_loop0_spec alg kw sch hk J ivec hiv chunks { start := 0#usize, «end» := chunks.len } ctr chunks
    (by simp) (by simp [Slice.len, Slice.length]) rfl hctr (fun q _ i _ => by simp) as ⟨ctr1, chunks1, hc1, hl1, hd1⟩
  have htl : tail.length = inout.length - inout.length / 32 * 32 := by
    rw [Slice.length, chunks_post2]; simp [Slice.length]
  have hlen : ∀ t : Slice U8, t.length = tail.length →
      (chunks1.val.flatMap (·.val) ++ t.val).length ≤ Usize.max := by
    intro t ht
    have h1 := length_flatMapN chunks1.val
    simp only [List.length_append, h1, show (32#usize : Usize).val = 32 from rfl]
    simp only [Slice.length] at ht hl1 chunks_post htl ⊢
    omega
  step as ⟨b, hb⟩
  split
  · rename_i hbt
    have h0 : tail.length = 0 := by simpa [hbt] using hb
    simp only [WP.spec_ok]
    exact chunks_assemble (by decide) (ksByte alg kw J) inout chunks chunks1 tail tail chunks_post chunks_post1 chunks_post2 hl1 hd1 rfl
      (fun i hi => absurd hi (by omega)) _ (chunks_post3 _ _ (hlen tail rfl))
  · rename_i hbt
    have hne : tail.length ≠ 0 := by simpa [hb] using hbt
    have h32 : tail.length < 32 := by omega
    step with div_ceil_spec tail.len 16#usize (by decide) as ⟨i2, hi2⟩
    have hi2' : i2.val = (tail.length + 15) / 16 := by rw [hi2]; simp [Slice.length]
    step with schedule_keystream_spec alg kw sch hk J ivec hiv (2 * chunks.length) ctr1 hc1 i2 (by omega) as ⟨st, hst⟩
    step with ctr32_loop1_spec alg kw J st (2 * chunks.length) i2.val (by omega) hst tail (by omega)
      { start := 0#usize, «end» := tail.len } tail (by simp) (by simp [Slice.length]) rfl (fun i _ => by simp)
      as ⟨t1, ht1l, ht1⟩
    exact chunks_assemble (by decide) (ksByte alg kw J) inout chunks chunks1 tail t1 chunks_post chunks_post1 chunks_post2 hl1 hd1 ht1l
      (fun i hi => by rw [ht1 i hi, show 16 * (2 * chunks.length) + i = 32 * chunks.length + i by omega]; rfl) _
      (chunks_post3 _ _ (hlen t1 ht1l))

/-! ## `AesKey` -/

/-- `AesKey::new` holds the round keys of a key of a length AES takes. -/
theorem aes_key_new_spec (alg : Algorithm) (key : Slice U8) (h : KeyLen alg key.length) :
    low.portable.aes.AesKey.new key ⦃ k => Keyed alg (seqNat8ToSeqNat32LE (key.val.map (·.bv))) k ⦄ := by
  unfold low.portable.aes.AesKey.new
  have hn : nr alg ≤ 14 := by cases alg <;> decide
  step with new_spec alg key h as ⟨k, hk, hkq⟩
  step with schedule_spec k (by omega) as ⟨s, hs, hsq⟩
  refine ⟨by rw [hs, hk], fun q hq i hi => ?_⟩
  rw [hsq q (by omega) i hi, hkq q hq]

/-- `AesKey::encrypt_block` is FIPS 197's cipher. -/
theorem aes_key_encrypt_block_spec (alg : Algorithm) (kw : List (BitVec 32)) (k : low.portable.aes.AesKey)
    (hk : Keyed alg kw k) (block : Std.Array U8 16#usize) :
    low.portable.aes.AesKey.encrypt_block k block ⦃ r => blockQ r = aesEncrypt alg kw (blockQ block) ⦄ :=
  schedule_encrypt_block alg kw k hk.1 (fun q hq => hk.2 q hq 0 (by omega)) block

/-- `AesKey::ctr32` is GCTR from the counter block `ivec` holds. -/
theorem aes_key_ctr32_spec (alg : Algorithm) (kw : List (BitVec 32)) (k : low.portable.aes.AesKey)
    (hk : Keyed alg kw k) (J : Quad32) (ivec : Std.Array U8 16#usize) (hiv : blockQ ivec = reverseBytesQuad32 J)
    (inout : Slice U8) :
    low.portable.aes.AesKey.ctr32 k ivec inout ⦃ r =>
      r.length = inout.length ∧ r.val.map (·.bv) = gctrEncrypt J (inout.val.map (·.bv)) alg kw ⦄ := by
  unfold low.portable.aes.AesKey.ctr32
  apply WP.spec_mono (ctr32_spec alg kw k hk J ivec hiv inout)
  rintro r ⟨hl, hr⟩
  refine ⟨hl, eq_gctr _ _ _ _ _ (by simpa [Slice.length] using hl) fun j hj => ?_⟩
  have e0 : r.length = r.val.length := rfl
  have e1 : inout.length = inout.val.length := rfl
  simp only [List.length_map] at hj
  have hj' : j < inout.length := by omega
  have hjr : j < r.val.length := by omega
  rw [getElem!_pos _ j (by simpa using hjr), getElem!_pos _ j (by simpa using hj), List.getElem_map, List.getElem_map,
    ← getElem!_pos r.val j hjr, ← getElem!_pos inout.val j hj, hr j hj']

end rind.armv7
