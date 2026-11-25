import Rind.Armv7.AesNohwRound
open Aeneas Aeneas.Std Result rind.vale

/-!
# The bitsliced AES's block representations

A block's bytes, its compact form of four words, and the batch of two that the
round steps run on.
-/

namespace rind.armv7

open low.portable.aes_nohw

/-- Byte `m` of the block four compact words hold: word `k` holds its bits
`2k` and `2k + 1`, at bits `2m` and `2m + 1`. -/
def cByte (c0 c1 c2 c3 : BitVec 32) (m : Nat) : BitVec 8 :=
  BitVec.ofBool (c3.getLsbD (2 * m + 1)) ++ BitVec.ofBool (c3.getLsbD (2 * m)) ++
    BitVec.ofBool (c2.getLsbD (2 * m + 1)) ++ BitVec.ofBool (c2.getLsbD (2 * m)) ++
    BitVec.ofBool (c1.getLsbD (2 * m + 1)) ++ BitVec.ofBool (c1.getLsbD (2 * m)) ++
    BitVec.ofBool (c0.getLsbD (2 * m + 1)) ++ BitVec.ofBool (c0.getLsbD (2 * m))

/-- The block a compact form holds. -/
def compactQ (c : Std.Array U32 4#usize) : Quad32 :=
  ofBytes fun m => cByte c.val[0]!.bv c.val[1]!.bv c.val[2]!.bv c.val[3]!.bv m

@[step]
theorem delta_swap_spec (a mask shift : U32) (h : shift.val < 32) :
    word.delta_swap a mask shift ⦃ r =>
      r.bv = a.bv ^^^ ((a.bv ^^^ a.bv >>> shift.val) &&& mask.bv) ^^^
        (((a.bv ^^^ a.bv >>> shift.val) &&& mask.bv) <<< shift.val) ⦄ := by
  unfold word.delta_swap
  step*

/-- `compact_word` on a word's bits. -/
def compactWord (a : BitVec 32) : BitVec 32 :=
  let a := a ^^^ ((a ^^^ a >>> 6) &&& 0x00cc00cc#32) ^^^ (((a ^^^ a >>> 6) &&& 0x00cc00cc#32) <<< 6)
  a ^^^ ((a ^^^ a >>> 12) &&& 0x0000f0f0#32) ^^^ (((a ^^^ a >>> 12) &&& 0x0000f0f0#32) <<< 12)

/-- `uncompact_word` on a word's bits. -/
def uncompactWord (a : BitVec 32) : BitVec 32 :=
  let a := a ^^^ ((a ^^^ a >>> 12) &&& 0x0000f0f0#32) ^^^ (((a ^^^ a >>> 12) &&& 0x0000f0f0#32) <<< 12)
  a ^^^ ((a ^^^ a >>> 6) &&& 0x00cc00cc#32) ^^^ (((a ^^^ a >>> 6) &&& 0x00cc00cc#32) <<< 6)

@[step]
theorem compact_word_spec (a : U32) : word.compact_word a ⦃ r => r.bv = compactWord a.bv ⦄ := by
  unfold word.compact_word
  step*
  simp only [compactWord]
  bv_tac 32

@[step]
theorem uncompact_word_spec (a : U32) : word.uncompact_word a ⦃ r => r.bv = uncompactWord a.bv ⦄ := by
  unfold word.uncompact_word
  step*
  simp only [uncompactWord]
  bv_tac 32

/-- `byte_column` on the words' bits. -/
def byteColumn (a0 a1 a2 a3 : BitVec 32) (k : Nat) : BitVec 32 :=
  (a0 >>> (8 * k) &&& 0xff#32) ||| ((a1 >>> (8 * k) &&& 0xff#32) <<< 8) |||
    ((a2 >>> (8 * k) &&& 0xff#32) <<< 16) ||| ((a3 >>> (8 * k) &&& 0xff#32) <<< 24)

@[step]
theorem byte_column_spec (a : Std.Array U32 4#usize) (k : U32) (hk : k.val < 4) :
    word.byte_column a k ⦃ r =>
      r.bv = byteColumn a.val[0]!.bv a.val[1]!.bv a.val[2]!.bv a.val[3]!.bv k.val ⦄ := by
  unfold word.byte_column
  step*
  simp_all [byteColumn]

/-- A constant index into a block reads its byte. -/
theorem index_byte (a : Std.Array U8 16#usize) (k : Usize) (hk : k.val < 16) :
    a.index_usize k = ok a.val[k.val]! := by
  have h := Array.index_usize_spec a k (by simpa using hk)
  rw [getElem!_pos a.val k.val (by simpa using hk)]
  revert h; cases a.index_usize k <;> simp_all

@[step]
theorem word_spec (b0 b1 b2 b3 : U8) :
    word.word b0 b1 b2 b3 ⦃ r => r.bv = b3.bv ++ b2.bv ++ b1.bv ++ b0.bv ⦄ := by
  unfold word.word
  simp only [lift, bind_ok]
  step*
  simp only [UScalar.bv_or, core.convert.num.FromU32U8.from_bv_eq] at *
  bv_tac 32

/-- Opens a block's bytes: reads each constant index, as a variable. -/
macro "open_block " b:ident : tactic => `(tactic| (
  simp (disch := simp) only [index_byte $b, bind_ok]
  simp only [show (0#usize).val = 0 from rfl, show (1#usize).val = 1 from rfl, show (2#usize).val = 2 from rfl,
    show (3#usize).val = 3 from rfl, show (4#usize).val = 4 from rfl, show (5#usize).val = 5 from rfl,
    show (6#usize).val = 6 from rfl, show (7#usize).val = 7 from rfl, show (8#usize).val = 8 from rfl,
    show (9#usize).val = 9 from rfl, show (10#usize).val = 10 from rfl, show (11#usize).val = 11 from rfl,
    show (12#usize).val = 12 from rfl, show (13#usize).val = 13 from rfl, show (14#usize).val = 14 from rfl,
    show (15#usize).val = 15 from rfl]))

/-- The compact form holds the block's bytes. -/
theorem compact_block_spec (input : Std.Array U8 16#usize) :
    word.compact_block input ⦃ r =>
      ∀ m < 16, cByte r.val[0]!.bv r.val[1]!.bv r.val[2]!.bv r.val[3]!.bv m = input.val[m]!.bv ⦄ := by
  unfold word.compact_block
  open_block input
  step*
  intro m hm
  simp only [cByte, compactWord, byteColumn, Std.Array.make, Std.Array.from_val, List.getElem!_cons_succ,
    List.getElem!_cons_zero] at *
  interval_cases m <;> bv_decide

/-- A constant index into a compact form reads its word. -/
theorem index_compact (a : Std.Array U32 4#usize) (k : Usize) (hk : k.val < 4) :
    a.index_usize k = ok a.val[k.val]! := by
  have h := Array.index_usize_spec a k (by simpa using hk)
  rw [getElem!_pos a.val k.val (by simpa using hk)]
  revert h; cases a.index_usize k <;> simp_all

/-- A word's low byte. -/
theorem cast8_bv (x : U32) : (UScalar.cast UScalarTy.U8 x).bv = BitVec.setWidth 8 (show BitVec 32 from x.bv) :=
  UScalar.cast_bv_eq _ _

/-- The bytes written are the compact form's block. -/
theorem uncompact_block_spec (out : Std.Array U8 16#usize) (input : Std.Array U32 4#usize) :
    word.uncompact_block out input ⦃ r =>
      ∀ m < 16, r.val[m]!.bv = cByte input.val[0]!.bv input.val[1]!.bv input.val[2]!.bv input.val[3]!.bv m ⦄ := by
  unfold word.uncompact_block
  simp only [lift, bind_ok]
  step*
  intro m hm
  simp only [cByte, uncompactWord, byteColumn, Std.Array.make, Std.Array.from_val] at *
  interval_cases m <;> simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, cast8_bv] <;>
    bv_decide

/-- `swap_bits::<1>` with the mask of every other bit. -/
@[step]
theorem swap_bits_spec (a b : U32) :
    word.swap_bits 1#i32 a b 1431655765#u32 ⦃ r =>
      r.1.bv = a.bv ^^^ (((a.bv >>> 1 ^^^ b.bv) &&& 0x55555555#32) <<< 1) ∧
      r.2.bv = b.bv ^^^ ((a.bv >>> 1 ^^^ b.bv) &&& 0x55555555#32) ⦄ := by
  unfold word.swap_bits
  simp only [lift, bind_ok, core.convert.FromSame.from]
  have h1 : U32.rMax / U32.rMax = 1 := by decide
  step*
  have hm : mask1.bv = 0x55555555#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [h1] at i2_post
    rw [← UScalar.val, mask1_post, i2_post]; rfl
  refine ⟨?_, ?_⟩ <;> simp only [UScalar.bv_xor, UScalar.bv_and, i5_post1, i3_post1, hm]

/-- A batch's words, each word's bits. -/
def low.portable.aes_nohw.Batch.bv (b : Batch) (j : Nat) : BitVec 32 := b.w.val[j]!.bv

/-- The transpose takes compact blocks to a bitsliced batch, and back: word
`i + 2k` of a compact batch is word `k` of block `i`. -/
theorem transpose_spec (b : Batch) :
    transpose b ⦃ r =>
      (∀ m < 16, r.byte (2 * m) = cByte (b.bv 0) (b.bv 2) (b.bv 4) (b.bv 6) m) ∧
      (∀ m < 16, r.byte (2 * m + 1) = cByte (b.bv 1) (b.bv 3) (b.bv 5) (b.bv 7) m) ∧
      (∀ m < 16, cByte (r.bv 0) (r.bv 2) (r.bv 4) (r.bv 6) m = b.byte (2 * m)) ∧
      (∀ m < 16, cByte (r.bv 1) (r.bv 3) (r.bv 5) (r.bv 7) m = b.byte (2 * m + 1)) ⦄ := by
  unfold transpose
  simp only [Batch.bv]
  open_batch b
  step*
  all_goals have hb : ¬ word.BATCH_SIZE ≥ 4#usize := by rw [word.BATCH_SIZE]; decide
  any_goals contradiction
  simp only [bsByte, cByte, Std.Array.make, Std.Array.from_val, List.getElem!_cons_succ,
    List.getElem!_cons_zero] at *
  refine ⟨fun m hm => ?_, fun m hm => ?_, fun m hm => ?_, fun m hm => ?_⟩ <;>
    interval_cases m <;> bv_decide

end rind.armv7
