import Rind.Armv7.AesNohwCipher
open Aeneas Aeneas.Std Result rind.vale

/-!
# The bitsliced AES on blocks

`to_batch` and `from_batch` move blocks in and out of a batch, and
`Schedule::encrypt_block` is the cipher on one.
-/

namespace rind.armv7

open low.portable.aes_nohw

private theorem getElem!_set_self {α : Type _} [Inhabited α] (l : List α) (i : ℕ) (x : α) (h : i < l.length) :
    (l.set i x)[i]! = x := by
  simp [h]

private theorem getElem!_set_ne {α : Type _} [Inhabited α] (l : List α) (i j : ℕ) (x : α) (h : i ≠ j) :
    (l.set i x)[j]! = l[j]! := by
  simp [List.getElem!_eq_getElem?_getD, h]

/-- Words `iter.start` to 3 of block `i`, into a batch holding its first `iter.start`. -/
theorem set_loop_spec (b0 : Batch) (block : Std.Array U32 4#usize) (i : Usize) (hi : i.val < 2)
    (iter : core.ops.range.Range Usize) (b : Batch)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (hb : ∀ j < 8, b.w.val[j]! = if j % 2 = i.val ∧ j / 2 < iter.start.val then block.val[j / 2]! else b0.w.val[j]!) :
    Batch.set_loop iter b block i ⦃ r =>
      ∀ j < 8, r.w.val[j]! = if j % 2 = i.val then block.val[j / 2]! else b0.w.val[j]! ⦄ := by
  unfold Batch.set_loop
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧
      ∀ j < 8, x.2.w.val[j]! =
        if j % 2 = i.val ∧ j / 2 < x.1.start.val then block.val[j / 2]! else b0.w.val[j]!)
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold Batch.set_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step with Array.index_usize_spec block it.start (by simp; omega) as ⟨x, hx⟩
      simp only [word.BATCH_SIZE]
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step with Array.update_spec as ⟨a, ha⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro j hj
      simp only [ha, Array.set_val_eq]
      by_cases hji : j = i3.val
      · subst hji
        rw [getElem!_set_self _ _ _ (by simp; scalar_tac)]
        have h1 : i3.val % 2 = i.val := by scalar_tac
        have h2 : i3.val / 2 = it.start.val := by scalar_tac
        rw [ite_eq_left ⟨h1, by omega⟩, h2, hx, getElem!_pos _ _ (by simp; omega)]
      · rw [getElem!_set_ne _ _ _ _ (by omega), hst j hj]
        have h3 : (j % 2 = i.val ∧ j / 2 < it'.start.val) ↔ (j % 2 = i.val ∧ j / 2 < it.start.val) := by
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, by scalar_tac⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
        simp only [h3]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro j hj
      rw [hst j hj]
      have h4 : j / 2 < it.start.val := by omega
      simp [h4]
  · exact ⟨hs, he, hb⟩

/-- `Batch::set` writes a block's four words to every other word, from word `i`. -/
theorem set_spec (b : Batch) (block : Std.Array U32 4#usize) (i : Usize) (hi : i.val < 2) :
    b.set block i ⦃ r =>
      ∀ j < 8, r.w.val[j]! = if j % 2 = i.val then block.val[j / 2]! else b.w.val[j]! ⦄ := by
  unfold Batch.set
  exact set_loop_spec b block i hi _ b (by simp) (by simp [word.BLOCK_WORDS]) (by intro j hj; simp)

/-- Words `iter.start` to 3 of block `i`, out of a batch. -/
theorem get_loop_spec (b : Batch) (i : Usize) (hi : i.val < 2)
    (iter : core.ops.range.Range Usize) (blk : Std.Array U32 4#usize)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (hb : ∀ k < iter.start.val, blk.val[k]! = b.w.val[2 * k + i.val]!) :
    Batch.get_loop iter b i blk ⦃ r => ∀ k < 4, r.val[k]! = b.w.val[2 * k + i.val]! ⦄ := by
  unfold Batch.get_loop
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧
      ∀ k < x.1.start.val, x.2.val[k]! = b.w.val[2 * k + i.val]!)
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold Batch.get_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      simp only [word.BATCH_SIZE]
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step with Array.index_usize_spec b.w i2 (by simp; scalar_tac) as ⟨x, hx⟩
      step with Array.update_spec as ⟨a, ha⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro k hk
      simp only [ha, Array.set_val_eq]
      by_cases hki : k = it.start.val
      · subst hki
        rw [getElem!_set_self _ _ _ (by simp; scalar_tac), hx,
          show 2 * it.start.val + i.val = i2.val by scalar_tac, getElem!_pos _ _ (by simp; scalar_tac)]
      · rw [getElem!_set_ne _ _ _ _ (by omega), hst k (by omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro k hk
      exact hst k (by omega)
  · exact ⟨hs, he, hb⟩

/-- `Batch::get` reads a block's four words from every other word, from word `i`. -/
theorem get_spec (b : Batch) (i : Usize) (hi : i.val < 2) :
    b.get i ⦃ r => ∀ k < 4, r.val[k]! = b.w.val[2 * k + i.val]! ⦄ := by
  unfold Batch.get
  exact get_loop_spec b i hi _ _ (by simp) (by simp [word.BLOCK_WORDS]) (by intro k hk; simp at hk)

/-- Byte `m` of block `i` of a batch of compact blocks. -/
def low.portable.aes_nohw.Batch.cblock (b : Batch) (i m : Nat) : BitVec 8 :=
  cByte (b.bv i) (b.bv (2 + i)) (b.bv (4 + i)) (b.bv (6 + i)) m

/-- `transpose_spec`, by block. -/
theorem transpose_block (b : Batch) :
    transpose b ⦃ r => ∀ i < 2, ∀ m < 16, r.byte (2 * m + i) = b.cblock i m ∧ r.cblock i m = b.byte (2 * m + i) ⦄ := by
  apply WP.spec_mono (transpose_spec b)
  rintro r ⟨h0, h1, h2, h3⟩ i hi m hm
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · exact ⟨h0 m hm, h2 m hm⟩
  · exact ⟨h1 m hm, h3 m hm⟩

/-- Blocks `iter.start` on, into a batch holding the first `iter.start`. -/
theorem to_batch_loop_spec (input : Slice (Std.Array U8 16#usize)) (hn : input.val.length ≤ 2)
    (iter : core.ops.range.Range Usize) (b : Batch)
    (hs : iter.start.val ≤ input.val.length) (he : iter.end.val = input.val.length)
    (hb : ∀ i < iter.start.val, ∀ m < 16, b.cblock i m = input.val[i]!.val[m]!.bv) :
    to_batch_loop iter input b ⦃ r =>
      ∀ i < input.val.length, ∀ m < 16, r.cblock i m = input.val[i]!.val[m]!.bv ⦄ := by
  unfold to_batch_loop
  apply loop.spec_decr_nat (fun x => input.val.length - x.1.start.val)
    (fun x => x.1.start.val ≤ input.val.length ∧ x.1.end.val = input.val.length ∧
      ∀ i < x.1.start.val, ∀ m < 16, x.2.cblock i m = input.val[i]!.val[m]!.bv)
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold to_batch_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step with Slice.index_usize_spec input it.start (by scalar_tac) as ⟨a, ha⟩
      step with compact_block_spec a as ⟨c, hc⟩
      step with set_spec st c it.start (by omega) as ⟨o1, ho1⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro i hi m hm
      have e0 := ho1 0 (by omega)
      have e1 := ho1 1 (by omega)
      have e2 := ho1 2 (by omega)
      have e3 := ho1 3 (by omega)
      have e4 := ho1 4 (by omega)
      have e5 := ho1 5 (by omega)
      have e6 := ho1 6 (by omega)
      have e7 := ho1 7 (by omega)
      simp only [Nat.reduceMod, Nat.reduceDiv] at e0 e1 e2 e3 e4 e5 e6 e7
      have hold := hst i
      have hcm := hc m hm
      rw [ha, ← getElem!_pos input.val it.start.val (by omega)] at hcm
      rcases (show it.start.val = 0 ∨ it.start.val = 1 by omega) with h | h <;>
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
        simp only [h] at e0 e1 e2 e3 e4 e5 e6 e7 hold hcm <;>
        simp_all [Batch.cblock, Batch.bv]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro i hi
      exact hst i (by omega)
  · exact ⟨hs, he, hb⟩

/-- A block's bytes as Vale's `quad32`. -/
def blockQ (a : Std.Array U8 16#usize) : Quad32 := ofBytes fun m => a.val[m]!.bv

/-- `to_batch` bitslices up to two blocks. -/
theorem to_batch_spec (input : Slice (Std.Array U8 16#usize)) (hn : input.val.length ≤ 2) :
    to_batch input ⦃ r => ∀ i < input.val.length, r.block i = blockQ input.val[i]! ⦄ := by
  unfold to_batch
  simp only [word.BATCH_SIZE]
  step*
  step with to_batch_loop_spec input hn { start := 0#usize, «end» := input.len } EMPTY (by simp)
    (by simp) (by intro i hi; simp at hi) as ⟨out, hout⟩
  apply WP.spec_mono (transpose_block out)
  intro r hr i hi
  apply eq_of_byte_eq; intro m hm
  rw [byte_block _ _ hm, blockQ, byte_ofBytes _ hm, (hr i (by omega) m hm).1, hout i hi m hm]

/-- Blocks `iter.start` on, out of a batch of compact blocks. -/
theorem from_batch_loop_spec (copy : Batch) (n : Nat) (hn : n ≤ 2)
    (iter : core.ops.range.Range Usize) (out : Slice (Std.Array U8 16#usize))
    (hs : iter.start.val ≤ n) (he : iter.end.val = n) (hl : out.val.length = n)
    (hb : ∀ i < iter.start.val, ∀ m < 16, out.val[i]!.val[m]!.bv = copy.cblock i m) :
    from_batch_loop iter out copy ⦃ r =>
      r.val.length = n ∧ ∀ i < n, ∀ m < 16, r.val[i]!.val[m]!.bv = copy.cblock i m ⦄ := by
  unfold from_batch_loop
  apply loop.spec_decr_nat (fun x => n - x.1.start.val)
    (fun x => x.1.start.val ≤ n ∧ x.1.end.val = n ∧ x.2.val.length = n ∧
      ∀ i < x.1.start.val, ∀ m < 16, x.2.val[i]!.val[m]!.bv = copy.cblock i m)
  · rintro ⟨it, st⟩ ⟨hs, he, hl, hst⟩
    simp only at hs he hl hst ⊢
    unfold from_batch_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step with Slice.index_mut_usize_spec st it.start (by scalar_tac) as ⟨a, back, ha, hback⟩
      step with get_spec copy it.start (by omega) as ⟨c, hc⟩
      step with uncompact_block_spec a c as ⟨a2, ha2⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, by simp [hback, hl], ?_, by omega⟩
      intro i hi m hm
      simp only [hback, Slice.set_val_eq]
      by_cases hii : i = it.start.val
      · subst hii
        rw [getElem!_set_self _ _ _ (by omega), ha2 m hm, Batch.cblock, Batch.bv, Batch.bv, Batch.bv, Batch.bv,
          hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega)]
        simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.reduceMul]
      · rw [getElem!_set_ne _ _ _ _ (by omega), hst i (by omega) m hm]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      refine ⟨hl, ?_⟩
      intro i hi
      exact hst i (by omega)
  · exact ⟨hs, he, hl, hb⟩

/-- `from_batch` writes out up to two blocks of a batch. -/
theorem from_batch_spec (out : Slice (Std.Array U8 16#usize)) (b : Batch) (hn : out.val.length ≤ 2) :
    from_batch out b ⦃ r =>
      r.val.length = out.val.length ∧ ∀ i < out.val.length, blockQ r.val[i]! = b.block i ⦄ := by
  unfold from_batch
  simp only [word.BATCH_SIZE]
  step*
  step with transpose_block b as ⟨t, ht⟩
  apply WP.spec_mono (from_batch_loop_spec t out.val.length hn { start := 0#usize, «end» := out.len } out
    (by simp) (by simp) rfl (by intro i hi; simp at hi))
  rintro r ⟨hl, hr⟩
  refine ⟨hl, ?_⟩
  intro i hi
  apply eq_of_byte_eq; intro m hm
  rw [byte_block _ _ hm, blockQ, byte_ofBytes _ hm, hr i hi m hm, (ht i (by omega) m hm).2]

/-- `encrypt_block` is the cipher on one block, under the schedule's round keys. -/
theorem encrypt_block_spec (s : Schedule) (block : Std.Array U8 16#usize)
    (h1 : 1 ≤ s.rounds.val) (hr : s.rounds.val ≤ 14) :
    s.encrypt_block block ⦃ r => blockQ r = cipherRounds s.rounds.val (blockQ block) (s.roundKeys 0) ⦄ := by
  unfold Schedule.encrypt_block
  simp only [lift, bind_ok]
  step with to_batch_spec as ⟨b, hb⟩
  have hb0 : b.block 0 = blockQ block := by
    simpa [Array.to_slice, Array.make] using hb 0 (by simp [Array.to_slice, Array.make])
  step with encrypt_batch_spec s b h1 hr as ⟨b1, hb1⟩
  simp only [Array.to_slice_mut]
  step with from_batch_spec as ⟨o, hol, ho⟩
  have hl1 : o.val.length = 1 := by simpa [Array.to_slice, Array.make] using hol
  have ho0 : blockQ o.val[0]! = b1.block 0 := ho 0 (by simp [Array.to_slice, Array.make])
  step with Array.index_usize_spec as ⟨r, hr'⟩
  have hfs : (Std.Array.from_slice (Std.Array.make 1#usize [block]) o).val = o.val := by
    simp [Std.Array.from_slice, hl1]
  have : r = o.val[0]! := by
    rw [hr']; simp only [hfs]; rw [getElem!_pos o.val 0 (by omega)]
  rw [this, ho0, hb1 0 (by omega), hb0]

end rind.armv7
