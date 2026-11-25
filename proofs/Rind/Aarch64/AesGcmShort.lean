import Rind.Aarch64.GhashPmull
import Rind.Aarch64.AesModesLow
import Rind.GcmSpec
open Aeneas Aeneas.Std Result rind.vale rind.simd Polynomial
open core.core_arch.arm_shared.neon.generated core.core_arch.aarch64.neon.generated

/-!
# rind's one-pass AES-GCM for short messages on aarch64

`Rind.Aarch64.AesGcmModel`'s `short` is Vale's `gctr_encrypt_LE` and
`gcm_hash`: its counter blocks are `inc32` of the counter block, its rounds
FIPS 197's, `load` and `store` the bytes of a partial block, `KEEP` masks the
keystream past a short ciphertext chunk, and `Aggregate` is the Horner rule,
each group of up to eight blocks multiplied by descending powers of H and
reduced once, the first group short so the last ends with the length block.
-/

local notation "P" => Polynomial (ZMod 2)
local notation "V" => core.core_arch.arm_shared.neon.uint64x2_t

set_option maxRecDepth 20000

namespace rind.aarch64.short

open rind.aarch64.pmull

/-! ## Bytes -/

theorem getLsbD_loadBytes (l : List U8) {k : Nat} (hk : k < 128) :
    (loadBytes l).getLsbD k = (decide (k / 8 < l.length) && (l[k / 8]!).bv.getLsbD (k % 8)) := by
  rw [loadBytes, getLsbD_leBytesToQuad32 _ hk]
  by_cases h : k / 8 < l.length
  · simp [h]
  · simp only [h, decide_false, Bool.false_and, List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (show l.length ≤ k / 8 by omega), Option.map_none, Option.getD_none]
    change (0#8).getLsbD (k % 8) = false; simp

/-- Zeros after the bytes load nothing. -/
theorem loadBytes_append_zeros (l : List U8) (n : Nat) : loadBytes (l ++ List.replicate n 0#u8) = loadBytes l := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_loadBytes _ hk, getLsbD_loadBytes _ hk]
  by_cases h : k / 8 < l.length
  · simp [h, show k / 8 < l.length + n by omega]
  · simp only [h, decide_false, Bool.false_and, List.length_append, List.length_replicate]
    by_cases h2 : k / 8 < l.length + n
    · simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega : l.length ≤ k / 8),
        show k / 8 - l.length < n by omega]
    · simp [h2]

theorem getLsbD_swap' (v : BitVec 128) {k : Nat} (hk : k < 128) :
    (swap v).getLsbD k = v.getLsbD ((k + 64) % 128) := by
  rw [getLsbD_swap]; simp [hk]

/-- `reverse`, `REV64` then `EXT` by a doubleword: the block's bytes reversed. -/
theorem reverse_eq (b : BitVec 128) : low.aarch64.ghash.reverse b = ok (reverseBytesQuad32 b) := by
  unfold low.aarch64.ghash.reverse
  rw [vrev64q_u8, bind_ok, vreinterpretq_u64_u8, bind_ok, ext1_eq]
  refine congrArg ok ?_
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_swap' _ hk, getLsbD_ofBytes _ (by omega), getLsbD_reverseBytesQuad32 _ hk, getLsbD_byte _ _ (by omega)]
  congr 1; omega

/-! ## The rounds -/

theorem foldlM_ok {α β : Type} (f : α → β → α) :
    ∀ (l : List β) (a : α), l.foldlM (fun a b => (ok (f a b) : Result α)) a = ok (l.foldl f a)
  | [], _ => rfl
  | b :: l, a => by simp only [List.foldlM_cons, bind_tc_ok, List.foldl_cons]; exact foldlM_ok f l (f a b)

/-- `encrypt` on FIPS 197's round keys is Vale's AES. -/
theorem encrypt_eq (alg : Algorithm) (kw : List (BitVec 32)) (rk : List (BitVec 128))
    (hrk : rk = keyToRoundKeys alg kw) (hl : rk.length = nr alg + 1) (b : BitVec 128) :
    low.aarch64.aes_gcm.encrypt rk b = ok (aesEncrypt alg kw b) := by
  have hnr : 1 ≤ nr alg := by cases alg <;> decide
  rw [low.aarch64.aes_gcm.encrypt, ite_eq_right (by omega)]
  simp only [aesmc_eq, foldlM_ok, bind_ok, aese_eq, veorq_u8, aesEncrypt, ← hrk, evalCipher_fold alg rk hl,
    hl, show nr alg + 1 - 2 = nr alg - 1 by omega, show nr alg + 1 - 1 = nr alg by omega]
  rfl

/-! ## The counter -/

/-- The 32-bit counter `from_be_bytes` reads from a counter block's last four
bytes is the low word of the block they load to, reversed. -/
theorem y0_ctr_eq (j0 : Quad32) (y0 : Std.Array U8 16#usize) (hy : loadBytes y0.val = reverseBytesQuad32 j0) :
    y0.val[12]!.bv ++ y0.val[13]!.bv ++ y0.val[14]!.bv ++ y0.val[15]!.bv = lane32 j0 0 := by
  have hl : y0.val.length = 16 := by simp
  have hj : j0 = reverseBytesQuad32 (loadBytes y0.val) := by rw [hy, reverseBytesQuad32_involutive]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_lane32, hj, getLsbD_reverseBytesQuad32 _ (by omega), getLsbD_loadBytes _ (by omega), hl]
  simp only [BitVec.getLsbD_append, hk, decide_true, Bool.true_and]
  interval_cases k <;> simp

/-- The counter block for message block `i`: the counter block `j0` with its
low word stepped `i`, in memory order. -/
theorem counter_eq (j0 : Quad32) (y0 : Std.Array U8 16#usize) (hy : loadBytes y0.val = reverseBytesQuad32 j0)
    (i : Nat) :
    let ctr : BitVec 32 := (y0.val[12]!.bv ++ y0.val[13]!.bv ++ y0.val[14]!.bv ++ y0.val[15]!.bv) +
      BitVec.ofNat 32 i
    ofLanes32 (fun l => if l = 3 then
        ctr.extractLsb' 0 8 ++ ctr.extractLsb' 8 8 ++ ctr.extractLsb' 16 8 ++ ctr.extractLsb' 24 8
      else lane32 (loadBytes y0.val) l) = reverseBytesQuad32 (inc32 j0 i) := by
  intro ctr
  have hc : ctr = lane32 j0 0 + BitVec.ofNat 32 i := by simp only [ctr, y0_ctr_eq j0 y0 hy]
  rw [hy, inc32_eq, ← hc]
  generalize ctr = c
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_ofLanes32, getLsbD_reverseBytesQuad32 _ hk]
  simp only [hk, decide_true, Bool.true_and]
  by_cases h3 : k / 32 = 3
  · rw [ite_eq_left h3]
    simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    have : 96 ≤ k := by omega
    interval_cases k <;> simp
  · rw [ite_eq_right h3, getLsbD_lane32, getLsbD_reverseBytesQuad32 _ (by omega)]
    simp only [show k % 32 < 32 by omega, decide_true, Bool.true_and, BitVec.getLsbD_append,
      BitVec.getLsbD_extractLsb', show 32 * (k / 32) + k % 32 = k by omega]
    simp only [show 8 * (15 - k / 8) + k % 8 - 32 < 96 by omega, decide_true, Bool.true_and]
    rw [ite_eq_right (by omega)]
    congr 1; omega

/-! ## Partial blocks -/

theorem loadBytes_nil : loadBytes [] = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk; rw [getLsbD_loadBytes _ hk]; simp

/-- One of `load`'s moves: `size` more bytes, zero-padded to eight, shifted
past the `pos` bytes the word holds. -/
theorem loadParts_step (b : List U8) (pos size : Nat) (hs : size ≤ 8) (hp : pos + size ≤ b.length)
    (h16 : pos + size ≤ 16) :
    loadBytes (b.take pos) ||| (loadBytes ((b.drop pos).take size ++ List.replicate (8 - size) 0#u8) <<< (8 * pos)) =
      loadBytes (b.take (pos + size)) := by
  rw [loadBytes_append_zeros]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, getLsbD_loadBytes _ hk, getLsbD_loadBytes _ hk]
  simp only [hk, decide_true, Bool.true_and, List.length_take, show min pos b.length = pos by omega,
    show min (pos + size) b.length = pos + size by omega]
  by_cases h1 : k < 8 * pos
  · have h2 : k / 8 < pos := by omega
    simp [h1, h2, show k / 8 < pos + size by omega, List.getElem!_eq_getElem?_getD]
  · rw [getLsbD_loadBytes _ (by omega)]
    have e1 : (k - 8 * pos) / 8 = k / 8 - pos := by omega
    have e2 : (k - 8 * pos) % 8 = k % 8 := by omega
    simp only [h1, decide_false, Bool.not_false, Bool.true_and, show ¬ k / 8 < pos by omega, Bool.false_and,
      Bool.false_or, e1, e2]
    by_cases h2 : k / 8 < pos + size
    · simp [h2, show k / 8 - pos < size by omega, List.getElem!_eq_getElem?_getD,
        show pos + (k / 8 - pos) = k / 8 by omega, show k / 8 - pos < b.length - pos by omega]
      rw [List.getElem?_eq_getElem (show k / 8 < b.length by omega)]; rfl
    · simp [h2, show ¬ k / 8 - pos < size by omega]

/-- The sizes `load` and `store` move for a slice of `n` bytes. -/
abbrev moved (n : Nat) (sizes : List Nat) : Nat := (sizes.filter fun s => decide (n &&& s ≠ 0)).sum

theorem moved_cons (n s : Nat) (sizes : List Nat) :
    moved n (s :: sizes) = (if n &&& s ≠ 0 then s else 0) + moved n sizes := by
  by_cases h : n &&& s ≠ 0 <;> simp [moved, h]

theorem moved_all : ∀ n < 16, moved n [8, 4, 2, 1] = n := by decide

theorem loadParts_eq (b : List U8) : ∀ (sizes : List Nat) (pos : Nat), (∀ s ∈ sizes, s ≤ 8) →
    pos + moved b.length sizes ≤ b.length → pos + moved b.length sizes ≤ 16 →
    low.aarch64.aes_gcm.loadParts b sizes (loadBytes (b.take pos), pos) =
      (loadBytes (b.take (pos + moved b.length sizes)), pos + moved b.length sizes)
  | [], pos, _, _, _ => by simp [low.aarch64.aes_gcm.loadParts, moved]
  | s :: sizes, pos, hs, h1, h2 => by
    rw [moved_cons] at h1 h2 ⊢
    rw [low.aarch64.aes_gcm.loadParts]
    have hs' : ∀ s ∈ sizes, s ≤ 8 := fun s h => hs s (by simp [h])
    by_cases hc : b.length &&& s ≠ 0
    · rw [ite_eq_left hc]
      rw [ite_eq_left hc] at h1 h2 ⊢
      dsimp only
      rw [loadParts_step b pos s (hs s (by simp)) (by omega) (by omega),
        loadParts_eq b sizes (pos + s) hs' (by omega) (by omega), Nat.add_assoc]
    · rw [ite_eq_right hc]
      rw [ite_eq_right hc, Nat.zero_add] at h1 h2 ⊢
      exact loadParts_eq b sizes pos hs' h1 h2

/-- `load` of up to a block's bytes: them, zero-padded. -/
theorem load_eq (b : List U8) (h : b.length ≤ 16) : low.aarch64.aes_gcm.load b = ok (loadBytes b) := by
  unfold low.aarch64.aes_gcm.load
  by_cases h16 : b.length = 16
  · rw [ite_eq_left h16]
  · rw [ite_eq_right h16]
    have hm := moved_all b.length (by omega)
    have := loadParts_eq b [8, 4, 2, 1] 0 (by simp) (by omega) (by omega)
    rw [List.take_zero, loadBytes_nil, Nat.zero_add, hm, List.take_of_length_le (le_refl _)] at this
    rw [this]

theorem storeBytes_val (v : BitVec 128) : (storeBytes v).val = (leQuad32ToBytes v).map fun b => (⟨b⟩ : U8) := by
  simp [storeBytes, Std.Array.from_val]

theorem length_storeBytes (v : BitVec 128) : (storeBytes v).val.length = 16 := by simp

theorem storeBytes_getElem! (v : BitVec 128) {i : Nat} (hi : i < 16) : ((storeBytes v).val[i]!).bv = byte v i := by
  have h1 : i < (leQuad32ToBytes v).length := by simp [leQuad32ToBytes]; omega
  rw [storeBytes_val, List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h1]
  show (leQuad32ToBytes v)[i] = byte v i
  rw [← leQuad32ToBytes_getElem! v hi, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl

/-- One of `store`'s moves: the word's bytes from `pos`, as its shift by
`pos` bytes lays them out first. -/
theorem storeBytes_shift (w : BitVec 128) (pos size : Nat) (hs : size ≤ 8) (h16 : pos + size ≤ 16) :
    ((storeBytes (w >>> (8 * pos))).val.take 8).take size = ((storeBytes w).val.drop pos).take size := by
  rw [List.take_take, show min size 8 = size by omega]
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [storeBytes_val, List.getElem_take, List.getElem_drop, List.getElem_map, leQuad32ToBytes,
    List.getElem_range]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hm, decide_true, Bool.true_and]
  congr 1; omega

theorem storeParts_eq (n : Nat) (w : BitVec 128) (bytes : List U8) (hb : bytes.length = n) :
    ∀ (sizes : List Nat) (pos : Nat), (∀ s ∈ sizes, s ≤ 8) → pos + moved n sizes ≤ n → pos + moved n sizes ≤ 16 →
      low.aarch64.aes_gcm.storeParts n w sizes ((storeBytes w).val.take pos ++ bytes.drop pos, pos) =
        ((storeBytes w).val.take (pos + moved n sizes) ++ bytes.drop (pos + moved n sizes), pos + moved n sizes)
  | [], pos, _, _, _ => by simp [low.aarch64.aes_gcm.storeParts, moved]
  | s :: sizes, pos, hs, h1, h2 => by
    rw [moved_cons] at h1 h2 ⊢
    rw [low.aarch64.aes_gcm.storeParts]
    have hs' : ∀ s ∈ sizes, s ≤ 8 := fun s h => hs s (by simp [h])
    by_cases hc : n &&& s ≠ 0
    · rw [ite_eq_left hc]
      rw [ite_eq_left hc] at h1 h2 ⊢
      have hl : ((storeBytes w).val.take pos).length = pos := by rw [List.length_take, length_storeBytes]; omega
      have hd : ((storeBytes w).val.take pos ++ bytes.drop pos).drop (pos + s) = bytes.drop (pos + s) := by
        rw [List.drop_append, List.drop_drop, hl, List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append]
        congr 1; omega
      dsimp only
      rw [List.take_left' hl, storeBytes_shift w pos s (hs s (by simp)) (by omega), hd, ← List.take_add]
      have := storeParts_eq n w bytes hb sizes (pos + s) hs' (by omega) (by omega)
      rw [Nat.add_assoc] at this
      exact this
    · rw [ite_eq_right hc]
      rw [ite_eq_right hc, Nat.zero_add] at h1 h2 ⊢
      exact storeParts_eq n w bytes hb sizes pos hs' h1 h2

/-- `store` of a block into up to a block's bytes: its first bytes. -/
theorem store_eq (b : List U8) (v : BitVec 128) (h : b.length ≤ 16) :
    low.aarch64.aes_gcm.store b v = ok ((storeBytes v).val.take b.length) := by
  unfold low.aarch64.aes_gcm.store
  by_cases h16 : b.length = 16
  · rw [ite_eq_left h16, h16, List.take_of_length_le (by simp)]
  · rw [ite_eq_right h16]
    have hm := moved_all b.length (by omega)
    have := storeParts_eq b.length v b rfl [8, 4, 2, 1] 0 (by simp) (by omega) (by omega)
    rw [List.take_zero, List.drop_zero, List.nil_append, Nat.zero_add, hm, List.drop_of_length_le (le_refl _),
      List.append_nil] at this
    rw [this]

theorem keep_eq (n : Nat) (h1 : 1 ≤ n) (h16 : n ≤ 16) :
    (low.aarch64.aes_gcm.KEEP.drop (16 - n)).take 16 = List.replicate n 0xff#u8 ++ List.replicate (16 - n) 0#u8 := by
  interval_cases n <;> decide

/-- `KEEP`'s mask keeps a block's first `n` bytes. -/
theorem mask_eq (v : BitVec 128) (n : Nat) (h16 : n ≤ 16) :
    v &&& loadBytes (List.replicate n 0xff#u8 ++ List.replicate (16 - n) 0#u8) = loadBytes ((storeBytes v).val.take n) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_and, getLsbD_loadBytes _ hk, getLsbD_loadBytes _ hk]
  simp only [List.length_append, List.length_replicate, List.length_take, length_storeBytes,
    show n + (16 - n) = 16 by omega, show min n 16 = n by omega, show k / 8 < 16 by omega, decide_true,
    Bool.true_and]
  by_cases h : k / 8 < n
  · simp only [decide_true, Bool.true_and, List.getElem!_eq_getElem?_getD, List.getElem?_append_left
      (by simp; omega : k / 8 < (List.replicate n 0xff#u8).length), List.getElem?_replicate, h, ite_true,
      Option.getD_some, List.getElem?_take]
    rw [← List.getElem!_eq_getElem?_getD, storeBytes_getElem! _ (by omega), getLsbD_byte _ _ (by omega),
      show 8 * (k / 8) + k % 8 = k by omega]
    have : (0xff#u8).bv.getLsbD (k % 8) = true := by
      have hk8 : k % 8 < 8 := by omega
      interval_cases (k % 8) <;> decide
    rw [this, Bool.and_true]
  · simp only [h, decide_false, Bool.false_and]
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right
      (by simp; omega : (List.replicate n 0xff#u8).length ≤ k / 8), List.getElem?_replicate, List.length_replicate,
      show k / 8 - n < 16 - n by omega, ite_true, Option.getD_some]
    simp

/-! ## The length block -/

theorem leQuad32ToBytes_leBytesToQuad32 (M : List (BitVec 8)) (h : M.length = 16) :
    leQuad32ToBytes (leBytesToQuad32 M) = M := by
  apply List.ext_getElem (by simp [leQuad32ToBytes, h])
  intro i h1 h2
  have hi : i < 16 := by simpa [leQuad32ToBytes] using h1
  simp only [leQuad32ToBytes, List.getElem_map, List.getElem_range]
  have := byte_leBytesToQuad32 M hi
  rw [byte] at this
  rw [this, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- A `u128`'s big-endian bytes, loaded and reversed, are the `u128`. -/
theorem rev_load_be (u : Std.U128) : reverseBytesQuad32 (loadBytes (core.num.U128.to_be_bytes u).val) = u.bv := by
  have hb : (core.num.U128.to_be_bytes u).val.map (·.bv) = u.bv.toBEBytes := by
    simp only [core.num.U128.to_be_bytes, Std.Array.from_val, List.map_map]
    exact List.map_id _
  have hl : u.bv.toLEBytes.length = 16 := by simp
  rw [loadBytes, hb, BitVec.toBEBytes, reverseBytesQuad32,
    leQuad32ToBytes_leBytesToQuad32 _ (by simp [hl]), List.reverse_reverse, leBytesToQuad32,
    BitVec.fromLEBytes_toLEBytes (by decide)]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp [hk]

/-! ## `Aggregate` -/

/-- `Aggregate::add` of the block `x`, its bytes already reversed, under the
key powers `p`: within a group, `x` times the power `power` names, its
Karatsuba terms added; at a group's start, the last group's terms reduced and
XORed into `x`, times H^8. -/
def aggStep (p : List (BitVec 128)) (s : low.aarch64.ghash.Aggregate) (x : BitVec 128) :
    low.aarch64.ghash.Aggregate :=
  if s.power = 0 then
    let a := accum (0, 0, 0) [(x ^^^ reduceModel s.lo s.mi s.hi, p[7]!)]
    { s with power := 7, lo := a.1, mi := a.2.1, hi := a.2.2 }
  else
    let a := accum (s.lo, s.mi, s.hi) [(x, p[s.power - 1]!)]
    { s with power := s.power - 1, lo := a.1, mi := a.2.1, hi := a.2.2 }

theorem aggStep_table (p : List (BitVec 128)) (s : low.aarch64.ghash.Aggregate) (x : BitVec 128) :
    (aggStep p s x).table = s.table := by
  unfold aggStep; split <;> rfl

theorem aggStep_power (p : List (BitVec 128)) (s : low.aarch64.ghash.Aggregate) (x : BitVec 128)
    (h : s.power ≤ 8) : (aggStep p s x).power ≤ 7 := by
  unfold aggStep; split <;> dsimp only <;> omega

theorem word_bv (t : List V) (m : Nat) : (low.aarch64.ghash.word t m).bv = lane64 t[m / 2]! (m % 2) := rfl

theorem lane64_dup (a : BitVec 64) : lane64 (a ++ a) 0 = a := by rw [lane64_0, lo_append]

/-- `POWERS` names, for H^(q+1), the table entry of its halves swapped and
the word of its Karatsuba middle term. -/
theorem powers_eq (p : List (BitVec 128)) {q : Nat} (hq : q < 8) :
    (htableOf p)[(low.aarch64.ghash.Aggregate.POWERS[q]!).1]! = swap p[q]! ∧
    lane64 ((low.aarch64.ghash.word (htableOf p) (low.aarch64.ghash.Aggregate.POWERS[q]!).2).bv ++
      (low.aarch64.ghash.word (htableOf p) (low.aarch64.ghash.Aggregate.POWERS[q]!).2).bv) 0 =
      lo (swap p[q]! ^^^ p[q]!) := by
  interval_cases q <;> refine ⟨rfl, ?_⟩ <;> rw [lane64_dup, word_bv] <;>
    simp only [low.aarch64.ghash.Aggregate.POWERS, htableOf, List.getElem!_cons_succ, List.getElem!_cons_zero,
      zipm, lane64_0, lane64_1, lo_append, hi_append, Nat.reduceDiv, Nat.reduceMod]

theorem mulStep_pow (p : List (BitVec 128)) {q : Nat} (hq : q < 8) (lo' mi hi' x : V) :
    low.aarch64.ghash.mulStep lo' mi hi' x (htableOf p)[(low.aarch64.ghash.Aggregate.POWERS[q]!).1]!
      ((low.aarch64.ghash.word (htableOf p) (low.aarch64.ghash.Aggregate.POWERS[q]!).2).bv ++
        (low.aarch64.ghash.word (htableOf p) (low.aarch64.ghash.Aggregate.POWERS[q]!).2).bv) false =
      ok ((karaTerms x p[q]!).1 ^^^ lo', (karaTerms x p[q]!).2.1 ^^^ mi, (karaTerms x p[q]!).2.2 ^^^ hi') := by
  obtain ⟨h1, h2⟩ := powers_eq p hq
  rw [h1]
  exact mulStep_eq _ _ _ _ _ _ false (by simpa using h2)

/-- `Aggregate::add` on a table of the powers `p` is `aggStep`. -/
theorem add_eq (p : List (BitVec 128)) (s : low.aarch64.ghash.Aggregate) (hp : s.table.htable.val = htableOf p)
    (hpow : s.power ≤ 8) (b : BitVec 128) :
    s.add b = ok (aggStep p s (reverseBytesQuad32 b)) := by
  unfold low.aarch64.ghash.Aggregate.add
  rw [reverse_eq, bind_ok]
  by_cases h0 : s.power = 0
  · have hm := mulStep_pow p (q := 7) (by omega)
    rw [ite_eq_left h0]
    simp only [reduce_eq, veorq_u64, rind.aarch64.pmull.zero_eq, bind_ok]
    show (do
      let md ← vdupq_n_u64 (low.aarch64.ghash.word s.table.htable.val (low.aarch64.ghash.Aggregate.POWERS[7]!).2)
      let r ← low.aarch64.ghash.mulStep 0 0 0 (reverseBytesQuad32 b ^^^ reduceModel s.lo s.mi s.hi)
        s.table.htable.val[(low.aarch64.ghash.Aggregate.POWERS[7]!).1]! md false
      ok { s with power := 7, lo := r.1, mi := r.2.1, hi := r.2.2 }) = _
    rw [hp, vdupq_n_u64, bind_tc_ok, hm, bind_tc_ok]
    simp [aggStep, h0, accum]
  · have hm := mulStep_pow p (q := s.power - 1) (by omega)
    rw [ite_eq_right h0, bind_ok]
    show (do
      let md ← vdupq_n_u64
        (low.aarch64.ghash.word s.table.htable.val (low.aarch64.ghash.Aggregate.POWERS[s.power - 1]!).2)
      let r ← low.aarch64.ghash.mulStep s.lo s.mi s.hi (reverseBytesQuad32 b)
        s.table.htable.val[(low.aarch64.ghash.Aggregate.POWERS[s.power - 1]!).1]! md false
      ok { s with power := s.power - 1, lo := r.1, mi := r.2.1, hi := r.2.2 }) = _
    rw [hp, vdupq_n_u64, bind_tc_ok, hm, bind_tc_ok]
    simp [aggStep, h0, accum]

/-- What `Aggregate` holds partway through `m` blocks short of the end of a
GHASH whose Horner value so far is `Y`: its power is at most 8 and
congruent to the blocks left mod 8, so 8 rather than 0 before a whole first
group, and its terms are of pairs whose products sum to `Y` times H to that
power, or `Y` itself at a group's end. -/
def AggInv (H : P) (s : low.aarch64.ghash.Aggregate) (Y : P) (m : Nat) : Prop :=
  s.power ≤ 8 ∧ s.power % 8 = m % 8 ∧ ∃ ps : List (BitVec 128 × BitVec 128),
    (s.lo, s.mi, s.hi) = accum (0, 0, 0) ps ∧
    (ps.map fun q => toPoly (mulModel q.1 q.2)).sum = if s.power = 0 then Y else gf128MulRev Y (gPower H s.power)

theorem reduce_inv (s : low.aarch64.ghash.Aggregate) (ps : List (BitVec 128 × BitVec 128))
    (hs : (s.lo, s.mi, s.hi) = accum (0, 0, 0) ps) :
    toPoly (reduceModel s.lo s.mi s.hi) = (ps.map fun q => toPoly (mulModel q.1 q.2)).sum := by
  have e1 : s.lo = (accum (0, 0, 0) ps).1 := congrArg Prod.fst hs
  have e2 : s.mi = (accum (0, 0, 0) ps).2.1 := congrArg (·.2.1) hs
  have e3 : s.hi = (accum (0, 0, 0) ps).2.2 := congrArg (·.2.2) hs
  apply reduce_sum
  rw [e1, e2, e3, kara_accum, kara_zero, zero_add]

section powers
variable (H : P) (hH : Small H) (p : List (BitVec 128))
  (hp : ∀ i < 8, toPoly p[i]! = shiftKey1 128 gf128ModulusLowTerms (gPower H (i + 1)))
include hH hp

theorem aggStep_inv (s : low.aarch64.ghash.Aggregate) (Y : P) (m : Nat) (hs : AggInv H s Y (m + 1))
    (x : BitVec 128) :
    AggInv H (aggStep p s x) (gf128MulRev (Y + toPoly x) H) m ∧ (aggStep p s x).power ≤ 7 := by
  obtain ⟨hle, hmod, ps, hacc, hsum⟩ := hs
  by_cases h0 : s.power = 0
  · have hY : toPoly (reduceModel s.lo s.mi s.hi) = Y := by rw [reduce_inv s ps hacc, hsum, ite_eq_left h0]
    refine ⟨⟨by simp [aggStep, h0], by simp [aggStep, h0]; omega,
      [(x ^^^ reduceModel s.lo s.mi s.hi, p[7]!)], by simp only [aggStep, h0, ite_true], ?_⟩, by simp [aggStep, h0]⟩
    simp only [aggStep, h0, ite_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      show (7 : Nat) ≠ 0 by decide, ite_false]
    rw [mul_data _ _ _ (small_gPower H hH _) (hp 7 (by omega)), toPoly_xor, hY, mulRev_pow _ _ 7 (by omega),
      add_comm]
  · obtain ⟨q, hq⟩ : ∃ q, s.power = q + 1 := ⟨s.power - 1, by omega⟩
    refine ⟨⟨by simp [aggStep, h0]; omega, by simp [aggStep, h0]; omega, ps ++ [(x, p[s.power - 1]!)],
      by simp only [aggStep, h0, ite_false]; rw [accum_append, ← hacc], ?_⟩, by simp [aggStep, h0]; omega⟩
    simp only [aggStep, h0, ite_false, List.map_append, List.sum_append, hsum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [mul_data _ _ _ (small_gPower H hH _) (hp _ (by omega)), hq, show q + 1 - 1 = q by omega,
      ← mulRev_add_left]
    by_cases hq0 : q = 0
    · subst hq0; simp [gPower_one]
    · rw [ite_eq_right hq0, mulRev_pow _ _ q (by omega)]

theorem aggFold_inv : ∀ (bs : List (BitVec 128)) (s : low.aarch64.ghash.Aggregate) (Y : P) (m : Nat),
    AggInv H s Y (m + bs.length) →
      AggInv H (bs.foldl (aggStep p) s) (ghashPoly H Y (bs.map toPoly)) m ∧
        (bs ≠ [] → (bs.foldl (aggStep p) s).power ≤ 7)
  | [], s, Y, m, h => ⟨by simpa [ghashPoly_nil] using h, by simp⟩
  | b :: bs, s, Y, m, h => by
    have h' : AggInv H s Y ((m + bs.length) + 1) := by
      simpa [List.length_cons, Nat.add_assoc] using h
    obtain ⟨h1, h2⟩ := aggStep_inv H hH p hp s Y _ h' b
    obtain ⟨h3, h4⟩ := aggFold_inv bs _ _ m h1
    refine ⟨by simpa [List.foldl_cons, ghashPoly_cons] using h3, fun _ => ?_⟩
    cases bs with
    | nil => simpa using h2
    | cons _ _ => exact h4 (by simp)

end powers

theorem aggFold_table (p : List (BitVec 128)) :
    ∀ (bs : List (BitVec 128)) (s : low.aarch64.ghash.Aggregate), (bs.foldl (aggStep p) s).table = s.table
  | [], _ => rfl
  | b :: bs, s => by rw [List.foldl_cons, aggFold_table p bs, aggStep_table]

theorem new_inv (H : P) (t : low.aarch64.ghash.PmullTable) (n : Nat) (hn : 0 < n) :
    ∃ s, low.aarch64.ghash.Aggregate.new t n = ok s ∧ s.table = t ∧ AggInv H s 0 n := by
  refine ⟨⟨t, (n - 1) % 8 + 1, 0, 0, 0⟩, by simp [low.aarch64.ghash.Aggregate.new, hn, rind.aarch64.pmull.zero_eq], rfl,
    by dsimp only; omega, by dsimp only; omega, [], rfl, ?_⟩
  simp [mulRev_zero_left]

theorem finish_eq (s : low.aarch64.ghash.Aggregate) :
    s.finish = ok (reverseBytesQuad32 (reduceModel s.lo s.mi s.hi)) := by
  simp [low.aarch64.ghash.Aggregate.finish, reduce_eq, vreinterpretq_u8_u64, reverse_eq]

theorem finish_inv (H : P) (s : low.aarch64.ghash.Aggregate) (Y : P) (h : AggInv H s Y 0) (h7 : s.power ≤ 7) :
    toPoly (reduceModel s.lo s.mi s.hi) = Y := by
  obtain ⟨-, hmod, ps, hacc, hsum⟩ := h
  rw [reduce_inv s ps hacc, hsum, ite_eq_left (by omega)]

/-! ## Chunks -/

theorem length_flatten16 {α : Type} : ∀ (L : List (List α)), (∀ c ∈ L, c.length = 16) →
    L.flatten.length = 16 * L.length
  | [], _ => rfl
  | c :: L, h => by
    rw [List.flatten_cons, List.length_append, h c (by simp),
      length_flatten16 L (fun c' h' => h c' (by simp [h'])), List.length_cons]
    ring

theorem chunksOf_flatten16 {α : Type} : ∀ (L : List (List α)), (∀ c ∈ L, c.length = 16) →
    chunksOf 16 L.flatten = L
  | [], _ => by simp [chunksOf]
  | c :: L, h => by
    have hc := h c (by simp)
    rw [List.flatten_cons, chunksOf_append (by omega) 1 _ _ (by rw [hc]), chunksOf_self _ (by omega) hc,
      chunksOf_flatten16 L (fun c' h' => h c' (by simp [h'])), List.singleton_append]

/-- Whole chunks, then fewer than 16 more, chunk back to themselves. -/
theorem chunksUpTo_flatten {α : Type} (L : List (List α)) (R : List α) (hL : ∀ c ∈ L, c.length = 16)
    (hR : R.length < 16) : chunksUpTo 16 (L.flatten ++ R) = L ++ if R = [] then [] else [R] := by
  rw [chunksUpTo, chunksOf_append (by omega) _ _ _ (length_flatten16 L hL),
    chunksRest_append (by omega) _ _ _ (length_flatten16 L hL), chunksOf_flatten16 L hL, chunksOf_of_lt hR,
    chunksRest_of_lt hR, List.append_nil]

theorem chunksUpTo_mem {α : Type} {l c : List α} (h : c ∈ chunksUpTo 16 l) : 1 ≤ c.length ∧ c.length ≤ 16 := by
  rw [chunksUpTo, List.mem_append] at h
  rcases h with h | h
  · have := chunksOf_length_mem h; omega
  · split at h
    · simp at h
    · rename_i hne
      rw [List.mem_singleton] at h
      subst h
      have h1 := chunksRest_length 16 l
      have h2 : (chunksRest 16 l).length ≠ 0 := by simpa using hne
      omega

/-- GHASH's blocks of some bytes are their chunks of up to 16, each loaded
and reversed. -/
theorem padBlocks_chunks (l : List U8) : (chunksUpTo 16 l).map blockBE = padBlocks l := by
  rw [chunksUpTo, padBlocks, List.map_append]
  congr 1
  split
  · rfl
  · simp [tailBlock, blockBE, loadBytes_append_zeros]

theorem bv_storeBytes (v : BitVec 128) : (storeBytes v).val.map (·.bv) = leQuad32ToBytes v := by
  rw [storeBytes_val, List.map_map]; exact List.map_id _

/-- Fewer than 16 bytes, padded as Vale pads them, load as they are. -/
theorem loadBytes_pad (R : List U8) (h : R.length < 16) :
    leBytesToQuad32 (padTo128Bits (R.map (·.bv))) = loadBytes R := by
  rw [padTo128Bits, List.length_map, Nat.mod_eq_of_lt h]
  split
  · rfl
  · rw [← loadBytes_append_zeros R (16 - R.length), loadBytes, List.map_append, List.map_replicate]; rfl

/-! ## The message loop -/

section loop
variable (alg : Algorithm) (kw : List (BitVec 32)) (j0 : Quad32)

/-- The chunk `c` of up to 16 bytes XORed with the keystream of counter
`inc32 j0 i`. -/
def chunkOut (c : List U8) (i : Nat) : List U8 :=
  (storeBytes (loadBytes c ^^^ aesEncrypt alg kw (reverseBytesQuad32 (inc32 j0 i)))).val.take c.length

/-- The chunks `chunkOut` makes from counter `i`. -/
def loopOuts : List (List U8) → Nat → List (List U8)
  | [], _ => []
  | c :: cs, i => chunkOut alg kw j0 c i :: loopOuts cs (i + 1)

theorem length_chunkOut (c : List U8) (i : Nat) (h : c.length ≤ 16) :
    (chunkOut alg kw j0 c i).length = c.length := by
  rw [chunkOut, List.length_take, length_storeBytes]; omega

theorem loopOuts_append : ∀ (A B : List (List U8)) (i : Nat),
    loopOuts alg kw j0 (A ++ B) i = loopOuts alg kw j0 A i ++ loopOuts alg kw j0 B (i + A.length)
  | [], B, i => rfl
  | c :: A, B, i => by
    rw [List.cons_append, loopOuts, loopOuts, loopOuts_append A B (i + 1), List.length_cons, List.cons_append,
      Nat.add_assoc, Nat.add_comm 1]

theorem loopOuts_16 : ∀ (C : List (List U8)) (i : Nat), (∀ c ∈ C, c.length = 16) →
    ∀ o ∈ loopOuts alg kw j0 C i, o.length = 16
  | [], _, _ => by simp [loopOuts]
  | c :: C, i, h => by
    intro o ho
    rw [loopOuts, List.mem_cons] at ho
    rcases ho with rfl | ho
    · rw [length_chunkOut _ _ _ _ _ (by rw [h c (by simp)]), h c (by simp)]
    · exact loopOuts_16 C (i + 1) (fun c' h' => h c' (by simp [h'])) o ho

theorem loopOuts_whole : ∀ (C : List (List U8)) (k : Nat), (∀ c ∈ C, c.length = 16) →
    (loopOuts alg kw j0 C (k + 1)).flatten.map (·.bv) =
      leSeqQuad32ToBytes (gctrEncryptRecursive (inc32 j0 1) alg kw (C.map loadBytes) k)
  | [], _, _ => rfl
  | c :: C, k, h => by
    have hc := h c (by simp)
    rw [loopOuts, List.flatten_cons, List.map_append, loopOuts_whole C (k + 1) (fun c' h' => h c' (by simp [h'])),
      List.map_cons, gctrEncryptRecursive]
    simp only [leSeqQuad32ToBytes, List.flatMap_cons]
    rw [chunkOut, hc, List.take_of_length_le (by rw [length_storeBytes]), bv_storeBytes, gctrEncryptBlock,
      inc32_inc32, Nat.add_comm 1 k]

/-- The loop's output over a message's chunks from counter 1 is Vale's GCTR
from the block after `j0`. -/
theorem loop_gctr (b : List U8) :
    (loopOuts alg kw j0 (chunksUpTo 16 b) 1).flatten.map (·.bv) = gctrEncrypt (inc32 j0 1) (b.map (·.bv)) alg kw := by
  have hch : ∀ c ∈ chunksOf 16 b, c.length = 16 := fun c h => chunksOf_length_mem h
  have hr := chunksRest_length 16 b
  have hq := chunksOf_length 16 b
  rw [chunksUpTo, loopOuts_append, List.flatten_append, List.map_append, loopOuts_whole alg kw j0 _ 0 hch]
  simp only [gctrEncrypt, List.length_map]
  by_cases h0 : b.length % 16 = 0
  · have ht : chunksRest 16 b = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [ht, ite_true, h0, loopOuts, List.flatten_nil, List.map_nil, List.append_nil, leBytesToSeqQuad32_load]
  · have ht : chunksRest 16 b ≠ [] := by intro h; rw [h] at hr; simp at hr; omega
    have hd : b.drop (b.length - b.length % 16) = chunksRest 16 b := by
      rw [chunksRest]; congr 1; omega
    rw [ite_eq_right ht, ite_eq_right h0, loopOuts, loopOuts, List.flatten_cons, List.flatten_nil, List.append_nil,
      ← List.map_take, leBytesToSeqQuad32_load, chunksOf_take16, ← List.map_drop, hd,
      loadBytes_pad _ (by omega), chunkOut, List.map_take, bv_storeBytes, gctrEncryptBlock, inc32_inc32, hq, hr,
      show (b.length - b.length % 16) / 16 = b.length / 16 by omega]

/-- `short`'s loop over chunks of 1 to 16 bytes from counter `i`: the
`chunkOut`s, and `Aggregate` stepped over the chunks it hashes, the
ciphertext's. -/
theorem short_loop_eq (ENC : Bool) (rk : List (BitVec 128)) (hrk : rk = keyToRoundKeys alg kw)
    (hl : rk.length = nr alg + 1) (y0 : Std.Array U8 16#usize) (hy : loadBytes y0.val = reverseBytesQuad32 j0)
    (p : List (BitVec 128)) :
    ∀ (cs : List (List U8)) (i : Nat) (g : low.aarch64.ghash.Aggregate), (∀ c ∈ cs, 1 ≤ c.length ∧ c.length ≤ 16) →
      g.table.htable.val = htableOf p → g.power ≤ 8 →
      low.aarch64.aes_gcm.short_loop ENC rk ⟨y0.val[12]!.bv ++ y0.val[13]!.bv ++ y0.val[14]!.bv ++ y0.val[15]!.bv⟩
        (loadBytes y0.val) cs i g =
      ok (((if ENC then loopOuts alg kw j0 cs i else cs).map blockBE).foldl (aggStep p) g,
        (loopOuts alg kw j0 cs i).flatten)
  | [], i, g, _, _, _ => by cases ENC <;> rfl
  | c :: cs, i, g, hc, ht, hpow => by
    obtain ⟨h1, h16⟩ := hc c (by simp)
    have hcs : ∀ c ∈ cs, 1 ≤ c.length ∧ c.length ≤ 16 := fun c' h' => hc c' (by simp [h'])
    have h3 : (3#i32).bv.toNat % 4 = 3 := by decide
    have hctr := counter_eq j0 y0 hy i
    simp only at hctr
    have ih := fun g' (ht' : g'.table.htable.val = htableOf p) (hp' : g'.power ≤ 8) =>
      short_loop_eq ENC rk hrk hl y0 hy p cs (i + 1) g' hcs ht' hp'
    rw [low.aarch64.aes_gcm.short_loop]
    simp only [vsetq_lane_u32, h3, hctr, vreinterpretq_u8_u32, bind_ok, encrypt_eq alg kw rk hrk hl,
      load_eq c h16, veorq_u8, store_eq c _ h16]
    cases ENC
    · have e := ih (aggStep p g (reverseBytesQuad32 (loadBytes c))) (by rw [aggStep_table]; exact ht)
        (by have := aggStep_power p g (reverseBytesQuad32 (loadBytes c)) hpow; omega)
      simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false, add_eq p g ht hpow, bind_ok, e,
        uncurry_apply_pair]
      simp [loopOuts, chunkOut, blockBE]
    · have e := ih (aggStep p g (reverseBytesQuad32 (loadBytes (chunkOut alg kw j0 c i))))
        (by rw [aggStep_table]; exact ht)
        (by have := aggStep_power p g (reverseBytesQuad32 (loadBytes (chunkOut alg kw j0 c i))) hpow; omega)
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, bind_ok, keep_eq c.length h1 h16,
        load_eq (List.replicate c.length 0xff#u8 ++ List.replicate (16 - c.length) 0#u8) (by simp; omega),
        vandq_u8, mask_eq _ _ h16, add_eq p g ht hpow]
      rw [show (storeBytes (loadBytes c ^^^ aesEncrypt alg kw (reverseBytesQuad32 (inc32 j0 i)))).val.take c.length =
        chunkOut alg kw j0 c i from rfl, e]
      simp [loopOuts, blockBE, uncurry_apply_pair]

/-- The loop's outputs chunk back to themselves. -/
theorem loopOuts_chunks (b : List U8) :
    chunksUpTo 16 (loopOuts alg kw j0 (chunksUpTo 16 b) 1).flatten = loopOuts alg kw j0 (chunksUpTo 16 b) 1 := by
  have hch : ∀ c ∈ chunksOf 16 b, c.length = 16 := fun c h => chunksOf_length_mem h
  have h16 := loopOuts_16 alg kw j0 (chunksOf 16 b) 1 hch
  have hr := chunksRest_length 16 b
  have e : chunksUpTo 16 b = chunksOf 16 b ++ if chunksRest 16 b = [] then [] else [chunksRest 16 b] := rfl
  rw [e, loopOuts_append, List.flatten_append]
  by_cases h : chunksRest 16 b = []
  · rw [ite_eq_left h]
    simp only [loopOuts, List.flatten_nil, List.append_nil]
    simpa using chunksUpTo_flatten _ [] h16 (by simp)
  · have hlen := length_chunkOut alg kw j0 (chunksRest 16 b) (1 + (chunksOf 16 b).length) (by omega)
    rw [ite_eq_right h, loopOuts, loopOuts, List.flatten_cons, List.flatten_nil, List.append_nil,
      chunksUpTo_flatten _ _ h16 (by omega), ite_eq_right]
    intro h'
    have := congrArg List.length h'
    rw [hlen] at this
    exact h (List.eq_nil_of_length_eq_zero this)

end loop

theorem foldlM_agg (p : List (BitVec 128))
    (f : low.aarch64.ghash.Aggregate → List U8 → Result low.aarch64.ghash.Aggregate)
    (hf : ∀ g c, c.length ≤ 16 → g.table.htable.val = htableOf p → g.power ≤ 8 →
      f g c = ok (aggStep p g (blockBE c))) :
    ∀ (cs : List (List U8)) (g : low.aarch64.ghash.Aggregate), (∀ c ∈ cs, c.length ≤ 16) →
      g.table.htable.val = htableOf p → g.power ≤ 8 → cs.foldlM f g = ok ((cs.map blockBE).foldl (aggStep p) g)
  | [], _, _, _, _ => rfl
  | c :: cs, g, h, ht, hp => by
    rw [List.foldlM_cons, hf g c (h c (by simp)) ht hp, bind_tc_ok,
      foldlM_agg p f hf cs _ (fun c' h' => h c' (by simp [h'])) (by rw [aggStep_table]; exact ht)
        (by have := aggStep_power p g (blockBE c) hp; omega)]
    rfl

/-- `lengthsBytes` loads as the length block. -/
theorem lengthsBytes_load (a m : Nat) (hm : m < 2 ^ 61) :
    reverseBytesQuad32 (loadBytes (low.aarch64.aes_gcm.lengthsBytes a m)) =
      insertNat64 (insertNat64 (mkfour 0 0 0 0) (8 * a) 1) (8 * m) 0 := by
  rw [low.aarch64.aes_gcm.lengthsBytes, rev_load_be]
  show (BitVec.ofNat 128 (a * 8) <<< 64) ||| BitVec.ofNat 128 (m * 8) = _
  rw [lengths_eq _ _ (by omega), Nat.mul_comm 8 a, Nat.mul_comm 8 m]

/-! ## `short` -/

/-- `short`: Vale's GCTR from the block after `j0`, and the tag GCTR from
`j0` on `gcm_hash` of the AAD and the ciphertext, for the AAD and message
lengths `tagged_from` passes it. -/
theorem short_spec (ENC : Bool) (alg : Algorithm) (kw : List (BitVec 32)) {N : Usize}
    (rk : Std.Array (BitVec 128) N) (hrk : rk.val = keyToRoundKeys alg kw) (hN : N.val = nr alg + 1)
    (t : low.aarch64.ghash.PmullTable) (ht : TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t)
    (j0 : Quad32) (y0 : Std.Array U8 16#usize) (hy : loadBytes y0.val = reverseBytesQuad32 j0)
    (aad inout : Slice U8) (hshort : (aad.length + 15) / 16 + (inout.length + 15) / 16 ≤ if ENC then 15 else 31) :
    ∃ tag out, low.aarch64.aes_gcm.short ENC rk t y0 aad inout = ok (tag, out) ∧
      out.length = inout.length ∧
      bvs out.val = gctrEncrypt (inc32 j0 1) (bvs inout.val) alg kw ∧
      bvs tag.val = gctrEncrypt j0 (leQuad32ToBytes (gcmHash (aesEncrypt alg kw (mkfour 0 0 0 0)) (bvs aad.val)
        (bvs (if ENC then out.val else inout.val)))) alg kw := by
  have hin : inout.length < 2 ^ 61 := by split at hshort <;> omega
  have hH : Small (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) := small_toPoly _
  obtain ⟨p, hp, htab⟩ := ht
  have ha : aad.length = aad.val.length := rfl
  have hi : inout.length = inout.val.length := rfl
  have hl : rk.val.length = nr alg + 1 := by rw [rk.property, hN]
  have hout := loop_gctr alg kw j0 inout.val
  have hlen : (loopOuts alg kw j0 (chunksUpTo 16 inout.val) 1).flatten.length = inout.val.length := by
    have := congrArg List.length hout
    rwa [List.length_map, length_gctrEncrypt, List.length_map] at this
  have hhash : (if ENC then loopOuts alg kw j0 (chunksUpTo 16 inout.val) 1 else chunksUpTo 16 inout.val).map blockBE =
      padBlocks (if ENC then (loopOuts alg kw j0 (chunksUpTo 16 inout.val) 1).flatten else inout.val) := by
    cases ENC
    · simp only [Bool.false_eq_true, ite_false, padBlocks_chunks]
    · simp only [ite_true]; rw [← loopOuts_chunks alg kw j0 inout.val, padBlocks_chunks, loopOuts_chunks]
  have hclen : (if ENC then (loopOuts alg kw j0 (chunksUpTo 16 inout.val) 1).flatten else inout.val).length =
      inout.val.length := by cases ENC <;> simp [hlen]
  obtain ⟨s0, hs0, hst0, hinv0⟩ := new_inv (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t
    ((aad.length + 15) / 16 + (inout.length + 15) / 16 + 1) (by omega)
  have ht0 : s0.table.htable.val = htableOf p := by rw [hst0]; exact htab
  have hpow0 := hinv0.1
  have e0 : (aad.length + 15) / 16 + (inout.length + 15) / 16 + 1 =
      ((inout.length + 15) / 16 + 1) + (padBlocks aad.val).length := by rw [length_padBlocks]; omega
  rw [e0] at hinv0
  obtain ⟨hinv1, -⟩ := aggFold_inv _ hH p hp (padBlocks aad.val) s0 0 _ hinv0
  have e1 : (inout.length + 15) / 16 + 1 = 1 + (padBlocks
      (if ENC then (loopOuts alg kw j0 (chunksUpTo 16 inout.val) 1).flatten else inout.val)).length := by
    rw [length_padBlocks, hclen]; omega
  rw [e1] at hinv1
  obtain ⟨hinv2, -⟩ := aggFold_inv _ hH p hp _ _ _ 1 hinv1
  obtain ⟨hinv3, h7⟩ := aggStep_inv _ hH p hp _ _ 0 hinv2
    (reverseBytesQuad32 (loadBytes (low.aarch64.aes_gcm.lengthsBytes aad.length inout.length)))
  have hY := finish_inv _ _ _ hinv3 h7
  have ht1 : ((padBlocks aad.val).foldl (aggStep p) s0).table.htable.val = htableOf p := by
    rw [aggFold_table]; exact ht0
  have ht2 : ((padBlocks (if ENC then (loopOuts alg kw j0 (chunksUpTo 16 inout.val) 1).flatten else inout.val)).foldl
      (aggStep p) ((padBlocks aad.val).foldl (aggStep p) s0)).table.htable.val = htableOf p := by
    rw [aggFold_table]; exact ht1
  have hxl : reverseBytesQuad32 (loadBytes (low.aarch64.aes_gcm.lengthsBytes aad.length inout.length)) =
      insertNat64 (insertNat64 (mkfour 0 0 0 0) (8 * aad.val.length) 1)
        (8 * (if ENC then (loopOuts alg kw j0 (chunksUpTo 16 inout.val) 1).flatten else inout.val).length) 0 := by
    rw [hclen]; exact lengthsBytes_load _ _ (by simp only [Slice.length] at hin; omega)
  unfold low.aarch64.aes_gcm.short
  simp only [hs0, bind_ok, load_eq y0.val (by simp), encrypt_eq alg kw rk.val hrk hl]
  rw [foldlM_agg p _ ?hf _ s0 (fun c h => (chunksUpTo_mem h).2) ht0 hpow0]
  case hf =>
    intro g c hc ht hp
    simp only [load_eq c hc, bind_ok, add_eq p g ht hp]
    rfl
  simp only [bind_ok, padBlocks_chunks, vreinterpretq_u32_u8,
    short_loop_eq alg kw j0 ENC rk.val hrk hl y0 hy p _ 1 _ (fun c h => chunksUpTo_mem h) ht1 hinv1.1,
    uncurry_apply_pair, hhash, load_eq (low.aarch64.aes_gcm.lengthsBytes aad.length inout.length)
      (by simp [low.aarch64.aes_gcm.lengthsBytes]), add_eq p _ ht2 hinv2.1,
    finish_eq, veorq_u8, store_eq _ _ (by simp : (List.replicate 16 0#u8).length ≤ 16)]
  rw [dite_eq_left (by simp), dite_eq_left (by rw [hlen]; exact Slice.length_ineq inout)]
  refine ⟨_, _, rfl, ?_, ?_, ?_⟩
  · simp [Slice.from_val, hlen]
  · rw [Slice.from_val]; exact hout
  · rw [Array.make_val, Slice.from_val, List.length_replicate, List.take_of_length_le (by rw [length_storeBytes])]
    show (storeBytes _).val.map (·.bv) = _
    rw [bv_storeBytes, gctr_block, ← hy, ← gcmHash_eq _ aad.val _ _ ?hx, BitVec.xor_comm]
    case hx => rw [hY, hxl, List.map_append, ghashPoly_append]

end rind.aarch64.short
