import Rind.Armv7.AesNohw
open Aeneas Aeneas.Std Result rind.vale

/-!
# The bitsliced AES's round steps

Each step of a round on a batch is that step of FIPS 197 on both its blocks.
-/

namespace rind.armv7

open low.portable.aes_nohw

theorem shift_left_spec (N : I32) (a : U32) (h0 : 0 ≤ N.val) (h : N.val < 16) :
    word.shift_left N a ⦃ r => r.bv = a.bv <<< (2 * N.val.toNat) ⦄ := by
  unfold word.shift_left
  have hi := hcast_small N h0 h
  step*
  · simp only [word.BATCH_SIZE]; scalar_tac
  · simp only [word.BATCH_SIZE] at *; scalar_tac
  · have hv : i1.val = 2 * N.val.toNat := by
      rw [i1_post, i_post, hi]; simp only [word.BATCH_SIZE]; scalar_tac
    rw [hv] at r_post1; exact r_post1

@[step] theorem shr4_spec (a : U32) : word.shift_right 4#i32 a ⦃ r => r.bv = a.bv >>> 8 ⦄ :=
  shift_right_spec 4#i32 a (by decide) (by decide)
@[step] theorem shr8_spec (a : U32) : word.shift_right 8#i32 a ⦃ r => r.bv = a.bv >>> 16 ⦄ :=
  shift_right_spec 8#i32 a (by decide) (by decide)
@[step] theorem shr12_spec (a : U32) : word.shift_right 12#i32 a ⦃ r => r.bv = a.bv >>> 24 ⦄ :=
  shift_right_spec 12#i32 a (by decide) (by decide)
@[step] theorem shl4_spec (a : U32) : word.shift_left 4#i32 a ⦃ r => r.bv = a.bv <<< 8 ⦄ :=
  shift_left_spec 4#i32 a (by decide) (by decide)
@[step] theorem shl8_spec (a : U32) : word.shift_left 8#i32 a ⦃ r => r.bv = a.bv <<< 16 ⦄ :=
  shift_left_spec 8#i32 a (by decide) (by decide)
@[step] theorem shl12_spec (a : U32) : word.shift_left 12#i32 a ⦃ r => r.bv = a.bv <<< 24 ⦄ :=
  shift_left_spec 12#i32 a (by decide) (by decide)

/-- `shift_rows_word` on a word's bits. -/
def shiftRowsWord (w : BitVec 32) : BitVec 32 :=
  ((w &&& 0x03030303#32) ||| ((w &&& 0x0c0c0c0c#32) >>> 8 ||| (w &&& 0x0c0c0c0c#32) <<< 24)) |||
    (((w &&& 0x30303030#32) >>> 16 ||| (w &&& 0x30303030#32) <<< 16) |||
      ((w &&& 0xc0c0c0c0#32) >>> 24 ||| (w &&& 0xc0c0c0c0#32) <<< 8))

@[step]
theorem shift_rows_word_spec (w : U32) : shift_rows_word w ⦃ r => r.bv = shiftRowsWord w.bv ⦄ := by
  unfold shift_rows_word
  step*
  simp only [shiftRowsWord, word.ROW0, word.ROW1, word.ROW2, word.ROW3] at *
  bv_tac 32

@[step]
theorem rotate_rows_down_spec (v : U32) :
    word.rotate_rows_down v ⦃ r => r.bv = (v.bv >>> 2 &&& 0x3f3f3f3f#32) ||| (v.bv <<< 6 &&& 0xc0c0c0c0#32) ⦄ := by
  unfold word.rotate_rows_down
  step*

@[step]
theorem rotate_rows_twice_spec (v : U32) :
    word.rotate_rows_twice v ⦃ r => r.bv = (v.bv >>> 4 &&& 0x0f0f0f0f#32) ||| (v.bv <<< 4 &&& 0xf0f0f0f0#32) ⦄ := by
  unfold word.rotate_rows_twice
  step*

/-- Opens a batch's words: reads each constant index, as a variable. -/
macro "open_batch " b:ident : tactic => `(tactic| (
  simp (disch := simp) only [index_word ($b).w, bind_ok]
  simp only [show (0#usize).val = 0 from rfl, show (1#usize).val = 1 from rfl, show (2#usize).val = 2 from rfl,
    show (3#usize).val = 3 from rfl, show (4#usize).val = 4 from rfl, show (5#usize).val = 5 from rfl,
    show (6#usize).val = 6 from rfl, show (7#usize).val = 7 from rfl]
  try simp only [Batch.byte]
  generalize ($b).w.val[0]! = a0
  generalize ($b).w.val[1]! = a1
  generalize ($b).w.val[2]! = a2
  generalize ($b).w.val[3]! = a3
  generalize ($b).w.val[4]! = a4
  generalize ($b).w.val[5]! = a5
  generalize ($b).w.val[6]! = a6
  generalize ($b).w.val[7]! = a7))

/-- `AddRoundKey` on the byte at every bit. -/
theorem add_round_key_spec (b k : Batch) :
    add_round_key b k ⦃ r => ∀ p < 32, r.byte p = b.byte p ^^^ k.byte p ⦄ := by
  unfold add_round_key
  open_batch b
  open_batch k
  step*
  intro p hp
  simp only [bsByte, Std.Array.make, Std.Array.from_val, List.getElem!_cons_succ, List.getElem!_cons_zero]
  interval_cases p <;> bv_decide

/-- `ShiftRows`: byte `k` of each block takes byte `k % 4 + 4 * ((k / 4 + k % 4) % 4)`. -/
theorem shift_rows_spec (b : Batch) :
    shift_rows b ⦃ r => ∀ k < 16, ∀ i < 2,
      r.byte (2 * k + i) = b.byte (2 * (k % 4 + 4 * ((k / 4 + k % 4) % 4)) + i) ⦄ := by
  unfold shift_rows
  open_batch b
  step*
  intro k hk i hi
  simp only [bsByte, shiftRowsWord, Std.Array.make, Std.Array.from_val, List.getElem!_cons_succ,
    List.getElem!_cons_zero] at *
  interval_cases k <;> interval_cases i <;> bv_decide

/-- `MixColumns` on each column of each block. -/
theorem mix_columns_spec (b : Batch) :
    mix_columns b ⦃ r => ∀ k < 16, ∀ i < 2,
      r.byte (2 * k + i) = xtime (b.byte (2 * (k / 4 * 4 + k % 4) + i)) ^^^
        xtime (b.byte (2 * (k / 4 * 4 + (k % 4 + 1) % 4) + i)) ^^^
        b.byte (2 * (k / 4 * 4 + (k % 4 + 1) % 4) + i) ^^^ b.byte (2 * (k / 4 * 4 + (k % 4 + 2) % 4) + i) ^^^
        b.byte (2 * (k / 4 * 4 + (k % 4 + 3) % 4) + i) ⦄ := by
  unfold mix_columns
  open_batch b
  step*
  intro k hk i hi
  simp only [bsByte, xtime, Std.Array.make, Std.Array.from_val, List.getElem!_cons_succ,
    List.getElem!_cons_zero] at *
  interval_cases k <;> interval_cases i <;> bv_decide

/-! ## Blocks -/

/-- Block `i` of a bitsliced batch: its byte `k` is the batch's at bit `2k + i`. -/
def low.portable.aes_nohw.Batch.block (b : Batch) (i : Nat) : Quad32 := ofBytes fun k => b.byte (2 * k + i)

theorem byte_block (b : Batch) (i : Nat) {k : Nat} (hk : k < 16) : byte (b.block i) k = b.byte (2 * k + i) :=
  byte_ofBytes _ hk

/-- `SubBytes` on both blocks. -/
theorem sub_bytes_block (b : Batch) : sub_bytes b ⦃ r => ∀ i < 2, r.block i = subBytes (b.block i) ⦄ := by
  apply WP.spec_mono (sub_bytes_spec b)
  intro r hr i hi
  apply eq_of_byte_eq; intro k hk
  rw [byte_block _ _ hk, byte_subBytes _ hk, byte_block _ _ hk, hr _ (by omega)]

/-- `ShiftRows` on both blocks. -/
theorem shift_rows_block (b : Batch) : shift_rows b ⦃ r => ∀ i < 2, r.block i = shiftRows (b.block i) ⦄ := by
  apply WP.spec_mono (shift_rows_spec b)
  intro r hr i hi
  apply eq_of_byte_eq; intro k hk
  rw [byte_block _ _ hk, byte_shiftRows _ hk, byte_block _ _ (by omega), hr k hk i hi]

/-- `MixColumns` on both blocks. -/
theorem mix_columns_block (b : Batch) : mix_columns b ⦃ r => ∀ i < 2, r.block i = mixColumns (b.block i) ⦄ := by
  apply WP.spec_mono (mix_columns_spec b)
  intro r hr i hi
  apply eq_of_byte_eq; intro k hk
  rw [byte_block _ _ hk, mixColumns_eq, fips197MixColumns, byte_ofBytes _ hk, hr k hk i hi]
  simp only [Nat.add_zero, Nat.mod_mod]
  rw [byte_block _ _ (by omega), byte_block _ _ (by omega), byte_block _ _ (by omega), byte_block _ _ (by omega)]

/-- `AddRoundKey` on both blocks. -/
theorem add_round_key_block (b k : Batch) :
    add_round_key b k ⦃ r => ∀ i < 2, r.block i = b.block i ^^^ k.block i ⦄ := by
  apply WP.spec_mono (add_round_key_spec b k)
  intro r hr i hi
  apply eq_of_byte_eq; intro m hm
  rw [byte_xor, byte_block _ _ hm, byte_block _ _ hm, byte_block _ _ hm, hr _ (by omega)]

end rind.armv7
