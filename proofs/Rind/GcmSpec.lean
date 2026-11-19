module
public import Rind.GhashSpec
public import Rind.Lanes
@[expose] public section
open Aeneas Aeneas.Std Result rind.simd Polynomial

/-!
# Vale's GCM on bytes, as both targets' AES-GCM proofs reach it

What rind's x86_64 and aarch64 AES-GCM proofs share: a vector's bytes stored
and loaded back, a block's 64-bit halves swapped, Vale's `inc32` on a
counter block's lanes, GCTR over appended blocks, on one whole block, and on
the loads of a message's whole blocks, the counter block of a 96-bit IV and
of any other, the length block, and the hash `gcm_hash` takes as GHASH from
zero of the padded AAD, the padded ciphertext, and the lengths. Nothing here
is a target's.
-/

local notation "P" => Polynomial (ZMod 2)

set_option maxRecDepth 20000

namespace rind.vale

/-! ## Bits of lanes, halves, and bytes -/

theorem getLsbD_ofLanes32 (f : Nat → BitVec 32) (k : Nat) :
    (ofLanes32 f).getLsbD k = (decide (k < 128) && (f (k / 32)).getLsbD (k % 32)) := by
  by_cases hk : k < 128
  · simp only [ofLanes32, BitVec.getLsbD_append]
    interval_cases k <;> simp
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [hk]

theorem getLsbD_lane32 (a : BitVec 128) (j m : Nat) :
    (lane32 a j).getLsbD m = (decide (m < 32) && a.getLsbD (32 * j + m)) := by
  simp [lane32, BitVec.getLsbD_extractLsb']

theorem getLsbD_ite {w : Nat} (c : Prop) [Decidable c] (a b : BitVec w) (i : Nat) :
    (if c then a else b).getLsbD i = if c then a.getLsbD i else b.getLsbD i := by
  split <;> rfl

theorem getLsbD_swap (v : BitVec 128) (k : Nat) :
    (swap v).getLsbD k = (decide (k < 128) && v.getLsbD ((k + 64) % 128)) := by
  by_cases hk : k < 128
  · simp only [swap, lo, hi, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    by_cases h : k < 64
    · simp [h, hk, show (k + 64) % 128 = 64 + k by omega]
    · simp [h, hk, show (k + 64) % 128 = k - 64 by omega]; omega
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [hk]

theorem swap_swap (v : BitVec 128) : swap (swap v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_swap, getLsbD_swap]
  simp [hk, show (k + 64) % 128 < 128 by omega, show ((k + 64) % 128 + 64) % 128 = k by omega]

/-- A vector's bytes, stored and loaded back. -/
theorem load_store (v : BitVec 128) : loadBytes (storeBytes v).val = v := by
  apply eq_of_byte_eq; intro i hi
  simp only [loadBytes, storeBytes, Std.Array.from_val, List.map_map]
  rw [byte_leBytesToQuad32 _ hi]
  have hm : ∀ l : List (BitVec 8), l.map (fun x => U8.bv ⟨x⟩) = l := fun l => by
    conv_rhs => rw [← List.map_id l]
    rfl
  rw [Function.comp_def, hm, leQuad32ToBytes_getElem! _ hi]

theorem leBytesToQuad32_leQuad32ToBytes (q : Quad32) : leBytesToQuad32 (leQuad32ToBytes q) = q := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_leBytesToQuad32 _ hk, leQuad32ToBytes_getElem! _ (by omega), getLsbD_byte _ _ (by omega)]
  congr 1; omega

/-! ## The counter -/

theorem lane32_inc32_zero (q : Quad32) (n : Nat) : lane32 (inc32 q n) 0 = lane32 q 0 + BitVec.ofNat 32 n := by
  have hz : ∀ x : Quad32, lane32 x 0 = x.extractLsb' 0 32 := fun _ => rfl
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [hz, hz, inc32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hm]

theorem high_inc32 (q : Quad32) (n : Nat) : (inc32 q n).extractLsb' 32 96 = q.extractLsb' 32 96 := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  simp only [inc32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hm, decide_true, Bool.true_and,
    show ¬ 32 + m < 32 by omega, ite_false, show 32 + m - 32 = m by omega]

theorem inc32_eq (q : Quad32) (n : Nat) :
    inc32 q n = q.extractLsb' 32 96 ++ (lane32 q 0 + BitVec.ofNat 32 n) := rfl

theorem inc32_inc32 (q : Quad32) (i j : Nat) : inc32 (inc32 q i) j = inc32 q (i + j) := by
  rw [inc32_eq (inc32 q i), high_inc32, lane32_inc32_zero, inc32_eq q (i + j), BitVec.add_assoc,
    BitVec.ofNat_add]

theorem inc32_zero (q : Quad32) : inc32 q 0 = q := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [inc32, BitVec.add_zero, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : k < 32
  · simp [h]
  · simp [h, show k - 32 < 96 by omega, show 32 + (k - 32) = k by omega]

theorem lane32_swap (v : BitVec 128) {i : Nat} (hi : i < 4) : lane32 (swap v) i = lane32 v ((i + 2) % 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_lane32, getLsbD_lane32, getLsbD_swap]
  simp only [hm, decide_true, Bool.true_and, show 32 * i + m < 128 by omega]
  congr 1; omega

theorem lane32_inc32 (q : Quad32) (n : Nat) {i : Nat} (hi : 1 ≤ i) (hi' : i < 4) :
    lane32 (inc32 q n) i = lane32 q i := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_lane32, getLsbD_lane32]
  simp only [inc32, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hm, decide_true, Bool.true_and,
    show ¬ 32 * i + m < 32 by omega, ite_false, show 32 * i + m - 32 < 96 by omega]
  congr 1; omega

theorem ofLanes32_ext (f g : Nat → BitVec 32) (h : ∀ i < 4, f i = g i) : ofLanes32 f = ofLanes32 g := by
  simp only [ofLanes32, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem ofLanes32_lane32 (x : BitVec 128) : ofLanes32 (lane32 x) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_ofLanes32, getLsbD_lane32]
  simp only [hk, decide_true, Bool.true_and, Nat.mod_lt _ (by omega : 32 > 0)]
  congr 1; omega

/-! ## GCTR -/

theorem length_gctr (icb : Quad32) (alg : Algorithm) (kw : List (BitVec 32)) :
    ∀ (ps : List Quad32) (i : Nat), (gctrEncryptRecursive icb alg kw ps i).length = ps.length
  | [], _ => rfl
  | _ :: ps, i => by rw [gctrEncryptRecursive, List.length_cons, length_gctr icb alg kw ps (i + 1),
      List.length_cons]

theorem gctr_append (icb : Quad32) (alg : Algorithm) (kw : List (BitVec 32)) :
    ∀ (ps ps' : List Quad32) (i : Nat), gctrEncryptRecursive icb alg kw (ps ++ ps') i =
      gctrEncryptRecursive icb alg kw ps i ++ gctrEncryptRecursive icb alg kw ps' (i + ps.length)
  | [], _, _ => rfl
  | p :: ps, ps', i => by
    rw [List.cons_append, gctrEncryptRecursive, gctrEncryptRecursive, gctr_append icb alg kw ps ps' (i + 1),
      List.cons_append, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

theorem chunksOf_self {α : Type} {k : Nat} (l : List α) (hk : 0 < k) (h : l.length = k) : chunksOf k l = [l] := by
  rw [chunksOf_cons hk (by omega), List.take_of_length_le (by omega), chunksOf_of_lt (by simp; omega)]

/-- GCTR on one whole block XORs in the keystream of the counter block itself. -/
theorem gctr_block (icb q : Quad32) (alg : Algorithm) (kw : List (BitVec 32)) :
    gctrEncrypt icb (leQuad32ToBytes q) alg kw =
      leQuad32ToBytes (q ^^^ aesEncrypt alg kw (reverseBytesQuad32 icb)) := by
  have hl : (leQuad32ToBytes q).length = 16 := by simp [leQuad32ToBytes]
  have hs : leBytesToSeqQuad32 (leQuad32ToBytes q) = [q] := by
    rw [leBytesToSeqQuad32_eq, chunksOf_self _ (by omega) hl, List.map_singleton,
      leBytesToQuad32_leQuad32ToBytes]
  simp only [gctrEncrypt, hl, Nat.mod_self, ite_true, hs, gctrEncryptRecursive, gctrEncryptBlock, inc32_zero,
    leSeqQuad32ToBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem length_leSeqQuad32ToBytes : ∀ (qs : List Quad32), (leSeqQuad32ToBytes qs).length = 16 * qs.length
  | [] => rfl
  | q :: qs => by
    rw [leSeqQuad32ToBytes, List.flatMap_cons, List.length_append, ← leSeqQuad32ToBytes,
      length_leSeqQuad32ToBytes qs]
    simp [leQuad32ToBytes]; ring

theorem length_gctrEncrypt (icb : Quad32) (p : List (BitVec 8)) (alg : Algorithm) (kw : List (BitVec 32)) :
    (gctrEncrypt icb p alg kw).length = p.length := by
  unfold gctrEncrypt
  dsimp only
  split
  · rw [length_leSeqQuad32ToBytes, length_gctr, leBytesToSeqQuad32_eq, List.length_map, chunksOf_length]; omega
  · rw [List.length_append, length_leSeqQuad32ToBytes, length_gctr, leBytesToSeqQuad32_eq, List.length_map,
      chunksOf_length, List.length_take, List.length_take]
    simp only [leQuad32ToBytes, List.length_map, List.length_range]
    omega

theorem leBytesToSeqQuad32_load (b : List U8) :
    leBytesToSeqQuad32 (b.map (·.bv)) = (chunksOf 16 b).map loadBytes := by
  rw [leBytesToSeqQuad32_eq, chunksOf_map, List.map_map]
  rfl

theorem chunksOf_take16 (b : List U8) : chunksOf 16 (b.take (b.length - b.length % 16)) = chunksOf 16 b := by
  have hk : b.length - b.length % 16 = 16 * (b.length / 16) := by omega
  have hA : (b.take (b.length - b.length % 16)).length = 16 * (b.length / 16) := by simp; omega
  conv_rhs => rw [← List.take_append_drop (b.length - b.length % 16) b]
  rw [chunksOf_append (by omega) _ _ _ hA, chunksOf_of_lt (l := b.drop (b.length - b.length % 16)) (by simp; omega),
    List.append_nil]

/-! ## The counter block, the length block, and the tag's hash -/

theorem computeIvBE_96 (hLE : Quad32) (iv : List (BitVec 8)) (h : iv.length = 12) :
    computeIvBE hLE iv =
      (reverseBytesQuad32 (leBytesToQuad32 (iv ++ List.replicate 4 0))).extractLsb' 32 96 ++ (1 : BitVec 32) := by
  rw [computeIvBE, ite_eq_left (by omega), padTo128Bits, ite_eq_right (by omega), h]

/-- An IV other than 96 bits hashes as `gcm_hash` does with no AAD. -/
theorem computeIvBE_other (hLE : Quad32) (iv : List (BitVec 8)) (h : iv.length ≠ 12) :
    computeIvBE hLE iv = reverseBytesQuad32 (gcmHash hLE [] iv) := by
  have hz : insertNat64 (mkfour 0 0 0 0) (8 * ([] : List (BitVec 8)).length) 1 = mkfour 0 0 0 0 := by decide
  rw [computeIvBE, ite_eq_right (by omega), gcmHash, hz]
  simp [padTo128Bits, leBytesToSeqQuad32, seqNat8ToSeqNat32LE, seqToSeqFourLE]

theorem lengths_eq (A M : Nat) (hM : M < 2 ^ 64) :
    (BitVec.ofNat 128 A <<< 64) ||| BitVec.ofNat 128 M =
      insertNat64 (insertNat64 (mkfour 0 0 0 0) A 1) M 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [insertNat64, Nat.one_ne_zero, ite_false, ite_true, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  by_cases h : k < 64
  · simp [h]
  · have : M.testBit k = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [h, this, show k - 64 < 64 by omega, show k - 64 < 128 by omega, show 64 + (k - 64) = k by omega]

/-- GHASH from zero over the padded AAD and ciphertext, then the length
block, is `gcm_hash`'s, its bytes reversed. -/
theorem gcmHash_eq (hLE : Quad32) (a c : List U8) (x : BitVec 128)
    (hx : toPoly x = gf128MulRev (ghashPoly (polyLE hLE) 0 ((padBlocks a ++ padBlocks c).map toPoly) +
      toPoly (insertNat64 (insertNat64 (mkfour 0 0 0 0) (8 * a.length) 1) (8 * c.length) 0)) (polyLE hLE)) :
    reverseBytesQuad32 x = gcmHash hLE (a.map (·.bv)) (c.map (·.bv)) := by
  have hrev : ∀ q, polyLE (reverseBytesQuad32 q) = toPoly q := fun q => by
    rw [polyLE, reverseBytesQuad32_involutive]
  have h : polyLE (gcmHash hLE (a.map (·.bv)) (c.map (·.bv))) = toPoly x := by
    rw [hx, gcmHash]
    rw [polyLE_ghashLE, List.map_append, List.map_append, padBlocks_vale, padBlocks_vale, List.map_singleton,
      hrev, List.length_map, List.length_map, ← List.append_assoc, ghashPoly_append, ← List.map_append,
      ghashPoly_cons, ghashPoly_nil]
  rw [polyLE] at h
  rw [← toPoly_inj h, reverseBytesQuad32_involutive]

/-! ## Vale's words -/

theorem word_bytes (w : BitVec 32) :
    (BitVec.fromLEBytes ((List.range 4).map fun i => w.extractLsb' (8 * i) 8)).setWidth 32 = w := by
  apply eq_of_wbyte_eq; intro i hi
  rw [wbyte, byte_word _ hi, getElem!_range_map _ hi, wbyte]

/-- Vale's key bytes read back to the key's words. -/
theorem seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE :
    ∀ (w : List (BitVec 32)), seqNat8ToSeqNat32LE (seqNat32ToSeqNat8LE w) = w
  | [] => rfl
  | w :: ws => by
    have e : (List.range 4).map (fun i => w.extractLsb' (8 * i) 8) =
        [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8] := rfl
    rw [seqNat32ToSeqNat8LE, List.flatMap_cons, ← seqNat32ToSeqNat8LE, e, List.cons_append, List.cons_append,
      List.cons_append, List.cons_append, List.nil_append, seqNat8ToSeqNat32LE_cons4, ← e, word_bytes,
      seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE ws]

end rind.vale
