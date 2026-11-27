import Rind.Armv7.Funs
import Rind.Aes
import Rind.AesSbox
open Aeneas Aeneas.Std Result rind.vale

/-!
# armv7's bitsliced AES

`low/generic/aes_nohw.rs`, aws-lc's `aes_nohw.c` in Rust, in its 32-bit
configuration: two blocks a batch, in eight words.
-/

namespace rind.armv7

open low.portable.aes_nohw

/-! ## The word operations -/

@[step]
theorem xor_spec (a b : U32) : word.xor a b ⦃ r => r.bv = a.bv ^^^ b.bv ⦄ := by
  simp [word.xor]

@[step]
theorem and_spec (a b : U32) : word.and a b ⦃ r => r.bv = a.bv &&& b.bv ⦄ := by
  simp [word.and]

@[step]
theorem or_spec (a b : U32) : word.or a b ⦃ r => r.bv = a.bv ||| b.bv ⦄ := by
  simp [word.or]

@[step]
theorem not_spec (a : U32) : word.not a ⦃ r => r.bv = ~~~a.bv ⦄ := by
  simp [word.not]

/-- A small constant shift count, as a `usize`. -/
theorem hcast_small (N : I32) (h0 : 0 ≤ N.val) (h : N.val < 16) :
    (IScalar.hcast UScalarTy.Usize N).val = N.val.toNat := by
  rw [IScalar.hcast_val_eq]
  have : (2 : Int) ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  rw [Int.emod_eq_of_lt h0 (by omega)]

theorem shift_right_spec (N : I32) (a : U32) (h0 : 0 ≤ N.val) (h : N.val < 16) :
    word.shift_right N a ⦃ r => r.bv = a.bv >>> (2 * N.val.toNat) ⦄ := by
  unfold word.shift_right
  have hi := hcast_small N h0 h
  step*
  · simp only [word.BATCH_SIZE]; scalar_tac
  · simp only [word.BATCH_SIZE] at *; scalar_tac
  · have hv : i1.val = 2 * N.val.toNat := by
      rw [i1_post, i_post, hi]; simp only [word.BATCH_SIZE]; scalar_tac
    rw [hv] at r_post1; exact r_post1

/-- The byte a batch's words hold at bit `p`: word `j` holds its bit `j`. -/
def bsByte (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32) (p : Nat) : BitVec 8 :=
  BitVec.ofBool (w7.getLsbD p) ++ BitVec.ofBool (w6.getLsbD p) ++ BitVec.ofBool (w5.getLsbD p) ++
    BitVec.ofBool (w4.getLsbD p) ++ BitVec.ofBool (w3.getLsbD p) ++ BitVec.ofBool (w2.getLsbD p) ++
    BitVec.ofBool (w1.getLsbD p) ++ BitVec.ofBool (w0.getLsbD p)

/-- A batch's byte at bit `p`. -/
def low.portable.aes_nohw.Batch.byte (b : Batch) (p : Nat) : BitVec 8 :=
  bsByte b.w.val[0]!.bv b.w.val[1]!.bv b.w.val[2]!.bv b.w.val[3]!.bv b.w.val[4]!.bv b.w.val[5]!.bv
    b.w.val[6]!.bv b.w.val[7]!.bv p

/-- A constant index into a batch reads its word. -/
theorem index_word (a : Std.Array U32 8#usize) (k : Usize) (hk : k.val < 8) :
    a.index_usize k = ok a.val[k.val]! := by
  have h := Array.index_usize_spec a k (by simpa using hk)
  rw [getElem!_pos a.val k.val (by simpa using hk)]
  revert h; cases a.index_usize k <;> simp_all

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The S-box circuit applies the S-box to the byte at every bit. -/
theorem sub_bytes_spec (b : Batch) :
    sub_bytes b ⦃ r => ∀ p < 32, r.byte p = sbox (b.byte p) ⦄ := by
  unfold sub_bytes
  simp (disch := simp) only [index_word b.w, bind_ok]
  simp only [show (0#usize).val = 0 from rfl, show (1#usize).val = 1 from rfl, show (2#usize).val = 2 from rfl,
    show (3#usize).val = 3 from rfl, show (4#usize).val = 4 from rfl, show (5#usize).val = 5 from rfl,
    show (6#usize).val = 6 from rfl, show (7#usize).val = 7 from rfl]
  simp only [Batch.byte]
  generalize b.w.val[0]! = a0
  generalize b.w.val[1]! = a1
  generalize b.w.val[2]! = a2
  generalize b.w.val[3]! = a3
  generalize b.w.val[4]! = a4
  generalize b.w.val[5]! = a5
  generalize b.w.val[6]! = a6
  generalize b.w.val[7]! = a7
  step*
  intro p hp
  rw [sbox_eq_tree]
  simp only [bsByte, sboxTree, Std.Array.make, Std.Array.from_val, List.getElem!_cons_succ,
    List.getElem!_cons_zero]
  interval_cases p <;> bv_decide

end rind.armv7
