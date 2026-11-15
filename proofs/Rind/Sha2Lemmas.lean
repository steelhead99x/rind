import Rind.Sha2
open Aeneas Aeneas.Std

/-! Facts about `Rind.Sha2`'s spec that the proofs use. -/

namespace rind.spec

/-- No slice reaches 2^64 elements. -/
theorem slice_length_lt {α : Type _} (s : Slice α) : s.length < 2 ^ 64 := by
  have := s.property
  rcases Usize.bounds_eq with h | h <;> simp only [Slice.length, h] at this ⊢ <;> scalar_tac

theorem compress_short (h : List U64) (bytes : List U8) (hb : bytes.length < 128) :
    compress h bytes = h := by
  rw [compress]; simp [show ¬ 128 ≤ bytes.length by omega]

@[simp] theorem compress_nil (h : List U64) : compress h [] = h :=
  compress_short h [] (by simp)

theorem compress_block (h : List U64) (bytes : List U8) (hb : 128 ≤ bytes.length) :
    compress h bytes = compress (processBlock h (blockWords (bytes.take 128))) (bytes.drop 128) := by
  rw [compress]; simp [hb]

/-- Compressing whole blocks, then more, is compressing them all. -/
theorem compress_append (h : List U64) (a b : List U8) (ha : a.length % 128 = 0) :
    compress h (a ++ b) = compress (compress h a) b := by
  by_cases hl : a.length = 0
  · simp [List.eq_nil_of_length_eq_zero hl]
  · have h128 : 128 ≤ a.length := by omega
    rw [compress_block h (a ++ b) (by simp; omega), compress_block h a h128,
      List.take_append_of_le_length h128, List.drop_append_of_le_length h128]
    exact compress_append _ _ _ (by simp; omega)
termination_by a.length
decreasing_by simp; omega

/-- `m` padded as the end of a message whose first `k` bytes came before it. -/
def padAfter (k : Nat) (m : List U8) : List U8 :=
  m ++ 0x80#u8 :: List.replicate ((239 - m.length % 128) % 128) 0#u8 ++
    (BitVec.ofNat 128 (8 * (k + m.length))).toBEBytes.map (@UScalar.mk UScalarTy.U8)

/-- Padding a message after whole blocks pads its rest. -/
theorem pad_append (p m : List U8) (hp : p.length % 128 = 0) :
    sha512Pad (p ++ m) = p ++ padAfter p.length m := by
  simp only [sha512Pad, padAfter, List.length_append, List.append_assoc,
    show (p.length + m.length) % 128 = m.length % 128 by omega]

/-- The compression function keeps eight words. -/
theorem processBlock_length (hv : List U64) (hl : hv.length = 8) (m : List U64) :
    (processBlock hv m).length = 8 := by
  simp only [processBlock, fips512.compressBlock, List.length_map, List.length_zipWith, hl]
  rw [show 80 = 79 + 1 from rfl, List.range_succ, List.foldl_append]
  simp

theorem compress_length (hv : List U64) (hl : hv.length = 8) (bytes : List U8) :
    (compress hv bytes).length = 8 := by
  by_cases hb : 128 ≤ bytes.length
  · rw [compress_block _ _ hb]
    exact compress_length _ (processBlock_length hv hl _) _
  · rwa [compress_short _ _ (by omega)]
termination_by bytes.length
decreasing_by simp; omega

theorem sha512Words_length (iv : List U64) (hiv : iv.length = 8) (m : List U8) :
    (sha512Words iv m).length = 64 := by
  have h8 : ∀ a : U64, a.bv.toBEBytes.length = 8 := fun a => by simp [BitVec.toBEBytes_length]
  simp only [sha512Words, List.length_flatMap, beBytes, List.length_map, h8, List.map_const',
    List.sum_replicate, compress_length iv hiv]
  rfl

end rind.spec
