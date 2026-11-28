module
public import Rind.GhashSpec
public import Rind.Lanes
@[expose] public section
open Aeneas Aeneas.Std Result rind.simd Polynomial

/-!
# Vale's GCM on bytes, as every target's AES-GCM proofs reach it

What rind's AES-GCM proofs on each target share: a vector's bytes stored
and loaded back, a block's 64-bit halves swapped, Vale's `inc32` on a
counter block's lanes, GCTR over appended blocks, on one whole block, on
the loads of a message's whole blocks, and byte by byte, the counter block
of a 96-bit IV and of any other, the length block, and the hash `gcm_hash` takes as GHASH from
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

/-! ## GCTR byte by byte -/

theorem getElem!_append_of_lt {α : Type _} [Inhabited α] (a b : List α) {j : Nat} (h : j < a.length) :
    (a ++ b)[j]! = a[j]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

theorem getElem!_append_of_ge {α : Type _} [Inhabited α] (a b : List α) {j : Nat} (h : a.length ≤ j) :
    (a ++ b)[j]! = b[j - a.length]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right h]

/-- Byte `j` of GCTR's keystream from counter block `icb`. -/
def ksByte (alg : Algorithm) (kw : List (BitVec 32)) (icb : Quad32) (j : Nat) : BitVec 8 :=
  byte (aesEncrypt alg kw (reverseBytesQuad32 (inc32 icb (j / 16)))) (j % 16)

theorem getElem!_leSeq : ∀ (qs : List Quad32) {j : Nat}, j < 16 * qs.length →
    (leSeqQuad32ToBytes qs)[j]! = byte qs[j / 16]! (j % 16)
  | [], j, h => by simp at h
  | q :: qs, j, h => by
    rw [leSeqQuad32ToBytes, List.flatMap_cons, ← leSeqQuad32ToBytes]
    have hq : (leQuad32ToBytes q).length = 16 := by simp [leQuad32ToBytes]
    by_cases hj : j < 16
    · rw [getElem!_append_of_lt _ _ (by omega), leQuad32ToBytes_getElem! _ hj, Nat.div_eq_of_lt hj,
        Nat.mod_eq_of_lt hj, List.getElem!_cons_zero]
    · rw [getElem!_append_of_ge _ _ (by omega), hq, getElem!_leSeq qs (by simp at h; omega),
        show j / 16 = (j - 16) / 16 + 1 by omega, List.getElem!_cons_succ, show (j - 16) % 16 = j % 16 by omega]

theorem gctrRec_getElem! (icb : Quad32) (alg : Algorithm) (kw : List (BitVec 32)) :
    ∀ (ps : List Quad32) (i k : Nat), k < ps.length →
      (gctrEncryptRecursive icb alg kw ps i)[k]! = gctrEncryptBlock icb ps[k]! alg kw (i + k)
  | [], _, _, h => by simp at h
  | p :: ps, i, 0, _ => by simp [gctrEncryptRecursive]
  | p :: ps, i, k + 1, h => by
    rw [gctrEncryptRecursive, List.getElem!_cons_succ, List.getElem!_cons_succ,
      gctrRec_getElem! icb alg kw ps (i + 1) k (by simp at h; omega), show i + 1 + k = i + (k + 1) by omega]

theorem length_leBytesToSeqQuad32 (p : List (BitVec 8)) : (leBytesToSeqQuad32 p).length = p.length / 16 := by
  rw [leBytesToSeqQuad32_eq, List.length_map, chunksOf_length]

theorem byte_leBytesToSeq (p : List (BitVec 8)) {j : Nat} (hj : j < 16 * (p.length / 16)) :
    byte (leBytesToSeqQuad32 p)[j / 16]! (j % 16) = p[j]! := by
  rw [leBytesToSeqQuad32_eq]
  simp only [chunksOf, List.map_map]
  rw [getElem!_range_map _ (by omega), Function.comp_apply, byte_leBytesToQuad32 _ (Nat.mod_lt _ (by omega)),
    getElem!_take_drop _ _ _ _ (Nat.mod_lt _ (by omega)), show 16 * (j / 16) + j % 16 = j by omega]

/-- Byte `j` of GCTR's output is byte `j` of its input XORed with its keystream's. -/
theorem gctr_getElem! (icb : Quad32) (p : List (BitVec 8)) (alg : Algorithm) (kw : List (BitVec 32))
    {j : Nat} (hj : j < p.length) :
    (gctrEncrypt icb p alg kw)[j]! = p[j]! ^^^ ksByte alg kw icb j := by
  have hrec : ∀ (b : List (BitVec 8)) {j : Nat}, j < 16 * (b.length / 16) →
      (leSeqQuad32ToBytes (gctrEncryptRecursive icb alg kw (leBytesToSeqQuad32 b) 0))[j]! =
        b[j]! ^^^ ksByte alg kw icb j := by
    intro b j hj
    have hl := length_leBytesToSeqQuad32 b
    rw [getElem!_leSeq _ (by rw [length_gctr, hl]; exact hj), gctrRec_getElem! _ _ _ _ 0 _ (by rw [hl]; omega),
      gctrEncryptBlock, byte_xor, byte_leBytesToSeq b hj, Nat.zero_add, ksByte]
  unfold gctrEncrypt
  dsimp only
  split
  · exact hrec p (by omega)
  · rename_i hne
    have hlt : (p.take (p.length - p.length % 16)).length = p.length - p.length % 16 := by simp
    have hl1 : (leSeqQuad32ToBytes (gctrEncryptRecursive icb alg kw
        (leBytesToSeqQuad32 (p.take (p.length - p.length % 16))) 0)).length = p.length - p.length % 16 := by
      rw [length_leSeqQuad32ToBytes, length_gctr, length_leBytesToSeqQuad32, hlt]; omega
    by_cases hjn : j < p.length - p.length % 16
    · rw [getElem!_append_of_lt _ _ (by omega), hrec _ (by rw [hlt]; omega)]
      simp [hjn, hj]
    · rw [getElem!_append_of_ge _ _ (by omega), hl1]
      have hk : j - (p.length - p.length % 16) < p.length % 16 := by omega
      have hq : (leQuad32ToBytes (gctrEncryptBlock icb
          (leBytesToQuad32 (padTo128Bits (p.drop (p.length - p.length % 16))))
          alg kw ((p.length - p.length % 16) / 16))).length = 16 := by simp [leQuad32ToBytes]
      have hd : (p.drop (p.length - p.length % 16)).length = p.length % 16 := by simp; omega
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_take, ite_eq_left hk, ← List.getElem!_eq_getElem?_getD,
        leQuad32ToBytes_getElem! _ (by omega), gctrEncryptBlock, byte_xor, byte_leBytesToQuad32 _ (by omega),
        padTo128Bits, ite_eq_right (by rw [hd]; omega), getElem!_append_of_lt _ _ (by rw [hd]; exact hk)]
      have e1 : (p.drop (p.length - p.length % 16))[j - (p.length - p.length % 16)]! = p[j]! := by
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop, show p.length - p.length % 16 +
          (j - (p.length - p.length % 16)) = j by omega]
      rw [e1, ksByte, show j / 16 = (p.length - p.length % 16) / 16 by omega,
        show j % 16 = j - (p.length - p.length % 16) by omega]

/-- Bytes that are GCTR's byte by byte are GCTR's output. -/
theorem eq_gctr (icb : Quad32) (p : List (BitVec 8)) (alg : Algorithm) (kw : List (BitVec 32))
    (out : List (BitVec 8)) (hl : out.length = p.length)
    (h : ∀ j < p.length, out[j]! = p[j]! ^^^ ksByte alg kw icb j) : out = gctrEncrypt icb p alg kw := by
  apply List.ext_getElem (by rw [hl, length_gctrEncrypt])
  intro j h1 h2
  rw [← getElem!_pos out j h1, ← getElem!_pos _ j h2, h j (by omega), gctr_getElem! _ _ _ _ (by omega)]

/-- GCTR's keystream from `n` blocks on is its keystream `16 n` bytes on. -/
theorem ksByte_inc (alg : Algorithm) (kw : List (BitVec 32)) (J : Quad32) (n i : Nat) :
    ksByte alg kw (inc32 J n) i = ksByte alg kw J (16 * n + i) := by
  rw [ksByte, ksByte, inc32_inc32, show n + i / 16 = (16 * n + i) / 16 by omega,
    show i % 16 = (16 * n + i) % 16 by omega]

/-! ## Chunks -/

theorem getElem!_flatMapN {N : Usize} (hN : 0 < N.val) (l : List (Std.Array U8 N)) {j : Nat}
    (hj : j < N.val * l.length) :
    (l.flatMap (·.val))[j]! = (l[j / N.val]!).val[j % N.val]! := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    have ha : a.val.length = N.val := a.property
    rw [List.flatMap_cons]
    by_cases h : j < N.val
    · rw [getElem!_append_of_lt _ _ (by omega), Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, List.getElem!_cons_zero]
    · have hj' : j - N.val < N.val * l.length := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hj; omega
      have e2 : (j - N.val) % N.val = j % N.val := (Nat.mod_eq_sub_mod (by omega)).symm
      rw [getElem!_append_of_ge _ _ (by omega), ha, ih hj',
        show j / N.val = (j - N.val) / N.val + 1 by
          rw [Nat.div_eq_sub_div hN (by omega)],
        List.getElem!_cons_succ, e2]

theorem length_flatMapN {N : Usize} (l : List (Std.Array U8 N)) : (l.flatMap (·.val)).length = N.val * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih, Nat.mul_add]; omega

/-- What `as_chunks_mut` writes back, whole chunks then the rest, each byte
of the input XORed with `f` of its position, byte by byte. -/
theorem chunks_assemble {N : Usize} (hN : 0 < N.val) (f : Nat → BitVec 8) (inout : Slice U8)
    (chunks c1 : Slice (Std.Array U8 N)) (tail t1 : Slice U8)
    (hcl : chunks.length = inout.length / N.val)
    (hc : ∀ i (h : i < chunks.val.length), (chunks.val[i]).val = (inout.val.drop (i * N.val)).take N.val)
    (ht : tail.val = inout.val.drop (inout.length / N.val * N.val))
    (h1l : c1.length = chunks.length)
    (h1 : ∀ q < chunks.length, ∀ i < N.val,
      (c1.val[q]!).val[i]!.bv = (chunks.val[q]!).val[i]!.bv ^^^ f (N.val * q + i))
    (t1l : t1.length = tail.length)
    (ht1 : ∀ i < tail.length, t1.val[i]!.bv = tail.val[i]!.bv ^^^ f (N.val * chunks.length + i))
    (r : List U8) (hr : r = c1.val.flatMap (·.val) ++ t1.val) :
    r.length = inout.length ∧ ∀ j < inout.length, r[j]!.bv = inout.val[j]!.bv ^^^ f j := by
  have e0 : inout.length = inout.val.length := rfl
  have e1 : chunks.length = chunks.val.length := rfl
  have e2 : c1.length = c1.val.length := rfl
  have e3 : tail.length = tail.val.length := rfl
  have e4 : t1.length = t1.val.length := rfl
  have htl : tail.val.length = inout.length - inout.length / N.val * N.val := by rw [ht]; simp
  have hfl : (c1.val.flatMap (·.val)).length = N.val * c1.val.length := length_flatMapN c1.val
  have hdm := Nat.div_mul_le_self inout.length N.val
  have hcm : N.val * chunks.length = inout.length / N.val * N.val := by rw [hcl, Nat.mul_comm]
  have hcc : N.val * c1.val.length = N.val * chunks.length := by rw [← e2, h1l]
  refine ⟨by rw [hr, List.length_append, hfl]; omega, fun j hj => ?_⟩
  rw [hr]
  by_cases hjc : j < N.val * chunks.length
  · have hq : j / N.val < chunks.length := by
      rw [Nat.div_lt_iff_lt_mul hN, Nat.mul_comm]; exact hjc
    have hjm : j % N.val < N.val := Nat.mod_lt _ hN
    have hjd : N.val * (j / N.val) + j % N.val = j := Nat.div_add_mod j N.val
    rw [getElem!_append_of_lt _ _ (by omega), getElem!_flatMapN hN _ (by omega),
      h1 _ hq _ hjm, hjd, getElem!_pos chunks.val (j / N.val) (by omega), hc _ (by omega)]
    simp [List.getElem!_eq_getElem?_getD, hjm, Nat.mul_comm (j / N.val), hjd]
  · rw [getElem!_append_of_ge _ _ (by omega), hfl, ← e2, h1l, ht1 _ (by omega),
      show N.val * chunks.length + (j - N.val * chunks.length) = j by omega, ht]
    simp [List.getElem!_eq_getElem?_getD, ← hcm, show N.val * chunks.length + (j - N.val * chunks.length) = j by omega]

theorem getElem!_set_of_ne {α : Type _} [Inhabited α] (l : List α) {i j : Nat} (x : α) (h : i ≠ j) :
    (l.set i x)[j]! = l[j]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne h]

theorem eq_of_bv (a b : List U8) (hl : a.length = b.length) (h : ∀ j < a.length, a[j]!.bv = b[j]!.bv) :
    a = b := by
  apply List.ext_getElem hl
  intro j h1 h2
  have := h j h1
  rw [getElem!_pos a j h1, getElem!_pos b j h2] at this
  exact (UScalar.eq_equiv_bv_eq _ _).mpr this

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

/-! ## Tags -/

/-- AES-GCM's tag over the ciphertext `cipher`, as `gcm_encrypt_LE_def` and
`gcm_decrypt_LE_def` compute it. -/
noncomputable def gcmTag (alg : Algorithm) (key iv cipher auth : List (BitVec 8)) : List (BitVec 8) :=
  let keyLE := seqNat8ToSeqNat32LE key
  let hLE := aesEncrypt alg keyLE (mkfour 0 0 0 0)
  gctrEncrypt (computeIvBE hLE iv) (leQuad32ToBytes (gcmHash hLE auth cipher)) alg keyLE

/-- `gcm_decrypt_LE`'s plaintext, and whether `tag` is the first `tag.length`
bytes of the tag, `MSB_t` of it as SP 800-38D compares. SP 800-38D permits only
tag lengths of 4, 8, 12, 13, 14, 15, or 16 bytes, but this takes any, an empty
`tag` included, which always matches. -/
noncomputable def gcmDecryptTrunc (alg : Algorithm) (key iv cipher auth tag : List (BitVec 8)) :
    List (BitVec 8) × Bool :=
  ((gcmDecrypt alg key iv cipher auth tag).1, (gcmTag alg key iv cipher auth).take tag.length == tag)

theorem gcmEncrypt_tag (alg : Algorithm) (key iv plain auth : List (BitVec 8)) :
    (gcmEncrypt alg key iv plain auth).2 = gcmTag alg key iv (gcmEncrypt alg key iv plain auth).1 auth := rfl

theorem length_gcmTag (alg : Algorithm) (key iv cipher auth : List (BitVec 8)) :
    (gcmTag alg key iv cipher auth).length = 16 := by
  rw [gcmTag, length_gctrEncrypt]; simp [leQuad32ToBytes]

/-- A tag of 16 bytes is checked whole, as `gcm_decrypt_LE` does. -/
theorem gcmDecryptTrunc_full (alg : Algorithm) (key iv cipher auth tag : List (BitVec 8))
    (h : tag.length = 16) :
    gcmDecryptTrunc alg key iv cipher auth tag = gcmDecrypt alg key iv cipher auth tag := by
  rw [gcmDecryptTrunc, h, List.take_of_length_le (by rw [length_gcmTag])]
  rfl

end rind.vale
