import Rind.Armv7.AesNohwCtr
import Rind.Armv7.GhashNohw
import Rind.Armv7.CtEqual
open Aeneas Aeneas.Std Result rind.vale rind.simd Polynomial

/-!
# AES-GCM on armv7 without the crypto extension or NEON

`mid/portable/aes_gcm.rs`'s `Portable`: aws-lc's bitsliced AES in 32-bit
words, `Rind.Armv7.AesNohwCtr`'s counter mode, and its integer GHASH,
`Rind.Armv7.GhashNohw`'s, composed by `Parts::tagged`. `tagged_spec` proves
`tagged` for any `Parts` whose table hashes, whose `encrypt_block` is AES, whose
`ctr` is GCTR, and whose `pass` is the trait's default, so the NEON and
crypto-extension compositions need only those; `Portable` is proven to be one.
`AesGcm::new`, with the CPU checks finding neither extension, keys `Portable`.
On any tier whose `Parts` are `PartsFor`, which `GcmReady` names, `AesGcm`'s
`encrypt`, `decrypt`, and `encrypt_any` are Vale's `gcm_encrypt_LE` and
`gcm_decrypt_LE`, and `decrypt_any` is `gcmDecryptTrunc`,
which compares only the first `tag.length` bytes of the tag, all of them for
`decrypt`, over `Rind.Armv7.CtEqual`'s restatement of HOL Light's proofs of the
compares.
-/

local notation "P" => Polynomial (ZMod 2)

namespace rind.armv7

open low.portable.aes_nohw low.portable.ghash_nohw

/-- Bytes as the specs take them. -/
abbrev bvs (l : List U8) : List (BitVec 8) := l.map (·.bv)

/-! ## Blocks -/

theorem blockQ_load (a : Std.Array U8 16#usize) : blockQ a = loadBytes a.val := blockQ_eq a

theorem blockBE_blockQ (a : Std.Array U8 16#usize) : blockBE a.val = reverseBytesQuad32 (blockQ a) := by
  rw [blockBE, blockQ_load]

theorem blockQ_to_be (u : U128) : blockQ (core.num.U128.to_be_bytes u) = reverseBytesQuad32 u.bv := by
  rw [← blockBE_to_be u, blockBE_blockQ, reverseBytesQuad32_involutive]

theorem add32_bv (b : BitVec 128) (n : BitVec 32) :
    (b &&& ~~~0xffffffff#128) ||| (b.setWidth 32 + n).setWidth 128 = b.extractLsb' 32 96 ++ (b.extractLsb' 0 32 + n) := by
  bv_decide

/-- `add32` steps the counter block's low word by `n`, as `inc32` does. -/
theorem add32_spec (J : Quad32) (block : Std.Array U8 16#usize) (hb : blockQ block = reverseBytesQuad32 J)
    (n : U32) : mid.aes_gcm.add32 block n ⦃ r => blockQ r = reverseBytesQuad32 (inc32 J n.val) ⦄ := by
  unfold mid.aes_gcm.add32
  step*
  simp only [lift, bind_ok, WP.spec_ok]
  rw [blockQ_to_be]
  apply congrArg
  have hbv : b.bv = J := by
    rw [b_post, fromBE_blockBE, blockBE_blockQ, hb, reverseBytesQuad32_involutive]
  have c : (~~~4294967295#u128 : U128).bv = ~~~0xffffffff#128 := rfl
  have hn : BitVec.ofNat 32 n.val = n.bv := by simp
  simp only [UScalar.bv_or, i2_post1, i1_post, c, core.convert.num.FromU128U32.from_bv_eq, ctr_post,
    core.num.U32.wrapping_add_bv_eq, i_post, UScalar.cast_bv_eq, hbv, inc32_eq, hn, UScalarTy.U32_numBits_eq,
    UScalarTy.U128_numBits_eq]
  exact add32_bv J n.bv

theorem usize_lt (n : Usize) : n.val < 2 ^ 64 := by
  have := n.hmax
  rcases System.Platform.numBits_eq with h | h
  · simp_all [UScalarTy.Usize_numBits_eq]; omega
  · simp_all [UScalarTy.Usize_numBits_eq]

/-- `lengths` is GCM's last GHASH block, the AAD's and the message's bit
lengths, as GHASH reads it. -/
theorem lengths_spec (aad msg : Usize) (ha : 8 * aad.val < 2 ^ 64) (hm : 8 * msg.val < 2 ^ 64) :
    mid.aes_gcm.lengths aad msg ⦃ r =>
      blockBE r.val = insertNat64 (insertNat64 (mkfour 0 0 0 0) (8 * aad.val) 1) (8 * msg.val) 0 ⦄ := by
  unfold mid.aes_gcm.lengths
  have hab := usize_lt aad
  have hmb := usize_lt msg
  step*
  have h1 : i1.bv = BitVec.ofNat 128 (8 * aad.val) := by
    apply BitVec.eq_of_toNat_eq
    rw [UScalar.bv_toNat, i1_post, i_post, UScalar.cast_val_eq, BitVec.toNat_ofNat]
    simp only [UScalarTy.U128_numBits_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; ring
  have h4 : i4.bv = BitVec.ofNat 128 (8 * msg.val) := by
    apply BitVec.eq_of_toNat_eq
    rw [UScalar.bv_toNat, i4_post, i3_post, UScalar.cast_val_eq, BitVec.toNat_ofNat]
    simp only [UScalarTy.U128_numBits_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; ring
  rw [blockBE_to_be, ← lengths_eq _ _ hm]
  simp only [i5_post1, i2_post1, h1, h4]

/-! ## GHASH over bytes -/

/-- A `Ghash` instance and table that hash as GHASH does under the key `H`. -/
def GhashFor (H : P) {T : Type} (G : mid.aes_gcm.Ghash T) (t : T) : Prop :=
  ∀ xi input, G.ghash t xi input ⦃ r =>
    toPoly (blockBE r.val) = ghashPoly H (toPoly (blockBE xi.val)) (input.val.map fun b => toPoly (blockBE b.val)) ⦄

theorem nohw_ghashFor (H : P) (hH : Small H) (t : NohwTable) (ht : TableFor H t) :
    GhashFor H NohwTable.Insts.RindMidAes_gcmGhash t :=
  fun xi input => ghash_spec H hH t ht xi input

theorem as_chunks_spec (N : Usize) (hN : N.val ≠ 0) (s : Slice U8) :
    core.slice.Slice.as_chunks N s ⦃ p =>
      p.1.val.map (·.val) = chunksOf N.val s.val ∧ p.2.val = chunksRest N.val s.val ⦄ := by
  simp only [core.slice.Slice.as_chunks, hN, ite_false, WP.spec_ok]
  refine ⟨?_, by simp [Slice.from_val, chunksRest, Slice.length, Nat.mul_comm]⟩
  apply List.ext_getElem (by simp [Slice.from_val, chunksOf, Slice.length])
  intro i h1 h2
  simp [Slice.from_val, chunksOf, Std.Array.from_val, Nat.mul_comm]

/-- `ghash` folds `data` into `xi`, its last block padded with zeros. -/
theorem ghash_pad_spec (H : P) {T : Type} (G : mid.aes_gcm.Ghash T) (t : T) (hG : GhashFor H G t)
    (xi : Std.Array U8 16#usize) (data : Slice U8) :
    mid.aes_gcm.ghash G t xi data ⦃ r =>
      toPoly (blockBE r.val) = ghashPoly H (toPoly (blockBE xi.val)) ((padBlocks data.val).map toPoly) ⦄ := by
  unfold mid.aes_gcm.ghash
  step with as_chunks_spec 16#usize (by decide) data as ⟨blocks, tail, hb, ht⟩
  step with hG xi blocks as ⟨x1, hx1⟩
  have hbm : blocks.val.map (fun b => toPoly (blockBE b.val)) = (chunksOf 16 data.val).map (toPoly ∘ blockBE) := by
    simp only [← hb, List.map_map, Function.comp_def]
  step as ⟨b, hbe⟩
  split
  · rename_i hb1
    have he : chunksRest 16 data.val = [] := by
      rw [← ht]; simpa [Slice.length, hb1] using hbe
    rw [WP.spec_ok, hx1, hbm, padBlocks, he, ite_eq_left rfl, List.append_nil, List.map_map]
  · rename_i hb1
    have he : chunksRest 16 data.val ≠ [] := by
      rw [← ht]; intro h; apply hb1; simp [hbe, Slice.length, h]
    have htl : tail.length < 16 := by
      simp only [Slice.length, ht, chunksRest_length]; omega
    step with Array.index_mut_SliceIndexRangeToUsizeSlice (Std.Array.repeat 16#usize 0#u8)
      { «end» := tail.len } (by scalar_tac) as ⟨s, back, hs, hsl, hback⟩
    step with core.slice.Slice.copy_from_slice.step_spec _ s tail (by rw [hsl]; simp) as ⟨s1, hs1⟩
    step*
    apply WP.spec_mono (hG x1 s2)
    intro r hr
    have hs2 : s2.val = [back tail] := by rw [s2_post, hs1]; simp [Std.Array.to_slice, Std.Array.make]
    have hlast : (back tail).val = tail.val ++ List.replicate (16 - tail.val.length) 0#u8 := by
      have hrep : (Std.Array.repeat 16#usize 0#u8).val = List.replicate 16 0#u8 := rfl
      simp only [Slice.length] at htl
      rw [hback, hrep, List.setSlice!]
      simp only [List.take_zero, List.length_replicate, Nat.sub_zero, Nat.min_eq_left htl.le,
        List.take_of_length_le le_rfl, Nat.zero_add, List.drop_replicate, List.nil_append]
    rw [hr, hs2, List.map_singleton, hx1, hbm, padBlocks, ite_eq_right he, List.map_append, ghashPoly_append,
      List.map_map, List.map_singleton, ← ht, tailBlock, hlast]

theorem blockBE_zero : blockBE (Std.Array.repeat 16#usize 0#u8).val = 0 := by
  apply eq_of_byte_eq; intro i hi
  rw [blockBE, byte_reverseBytes _ hi, loadBytes, byte_leBytesToQuad32 _ (by omega)]
  have hz : (0 : Quad32) = 0#128 := rfl
  simp [Std.Array.repeat, byte, hz, show 15 - i < 16 by omega]
  interval_cases i <;> rfl

/-! ## The counter block -/

/-- A 96-bit IV, then the counter 1, is `compute_iv_BE`'s counter block. -/
theorem load_counter (hLE : Quad32) (l : List U8) (hl : l.length = 12) :
    loadBytes (l ++ [0#u8, 0#u8, 0#u8, 1#u8]) = reverseBytesQuad32 (computeIvBE hLE (l.map (·.bv))) := by
  rw [computeIvBE_96 hLE _ (by simp [hl])]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_reverseBytesQuad32 _ hk, loadBytes, getLsbD_leBytesToQuad32 _ hk]
  by_cases h : k < 96
  · have hj : ¬ 8 * (15 - k / 8) + k % 8 < 32 := by omega
    have h96 : 8 * (15 - k / 8) + k % 8 - 32 < 96 := by omega
    simp only [BitVec.getLsbD_append, hj, ite_false, BitVec.getLsbD_extractLsb', h96, decide_true, Bool.true_and]
    rw [getLsbD_reverseBytesQuad32 _ (by omega), getLsbD_leBytesToQuad32 _ (by omega)]
    have e1 : (32 + (8 * (15 - k / 8) + k % 8 - 32)) / 8 = 15 - k / 8 := by omega
    have e2 : (32 + (8 * (15 - k / 8) + k % 8 - 32)) % 8 = k % 8 := by omega
    rw [e1, e2, show 8 * (15 - (15 - k / 8)) + k % 8 = k by omega]
    simp only [List.getElem!_eq_getElem?_getD, List.map_append, List.getElem?_append_left
      (by simp [hl]; omega : k / 8 < (l.map (·.bv)).length)]
  · have hl' : (l.map (·.bv)).length = 12 := by simp [hl]
    have hj : 8 * (15 - k / 8) + k % 8 < 32 := by omega
    simp only [BitVec.getLsbD_append, hj, ite_true, List.getElem!_eq_getElem?_getD, List.map_append,
      List.getElem?_append_right (by omega : (l.map (·.bv)).length ≤ k / 8), hl']
    interval_cases k <;> decide

/-- `initial_counter` is `compute_iv_BE`'s counter block for an IV under 2^61
bytes, on a table that hashes as GHASH does under the key `hLE`. -/
theorem initial_counter_spec (hLE : Quad32) {T : Type} (G : mid.aes_gcm.Ghash T) (t : T)
    (hG : GhashFor (polyLE hLE) G t) (iv : Slice U8) (hiv : iv.length < 2 ^ 61) :
    mid.aes_gcm.initial_counter G t iv ⦃ y0 =>
      blockQ y0 = reverseBytesQuad32 (computeIvBE hLE (iv.val.map (·.bv))) ⦄ := by
  unfold mid.aes_gcm.initial_counter
  have hl := Slice.len_val iv
  by_cases h12 : iv.len = 12#usize
  · simp only [h12, ↓reduceIte]
    have h12' : iv.length = 12 := by rw [← hl, h12]; rfl
    step with Array.index_mut_SliceIndexRangeToUsizeSlice (Std.Array.repeat 16#usize 0#u8)
      { «end» := 12#usize } (by scalar_tac) as ⟨s, back, hs, hsl, hback⟩
    step with core.slice.Slice.copy_from_slice.step_spec _ s iv (by rw [hsl, h12']) as ⟨s1, hs1⟩
    step*
    rw [blockQ_load, ← load_counter hLE iv.val h12']
    congr 1
    have hrep : (Std.Array.repeat 16#usize 0#u8).val = List.replicate 16 0#u8 := rfl
    simp only [Slice.length] at h12'
    rw [y0_post, Std.Array.set_val_eq, hback, hs1, hrep, List.setSlice!]
    simp [h12']
  · simp only [h12, ↓reduceIte]
    have h12' : iv.length ≠ 12 := by intro h; apply h12; scalar_tac
    step with ghash_pad_spec (polyLE hLE) G t hG _ iv as ⟨y1, hy1⟩
    step with lengths_spec 0#usize iv.len (by simp) (by rw [hl]; omega) as ⟨a, ha⟩
    step*
    apply WP.spec_mono (hG y1 s)
    intro y0 hy0
    have hs : s.val = [a] := by rw [s_post]; simp [Std.Array.to_slice, Std.Array.make]
    have hx := gcmHash_eq hLE [] iv.val (blockBE y0.val) (by
      rw [hy0, hs, List.map_singleton, hy1, blockBE_zero, toPoly_zero, ghashPoly_cons, ghashPoly_nil, ha,
        padBlocks_nil, List.nil_append, hl, List.length_nil, Nat.mul_zero])
    rw [computeIvBE_other _ _ (by simpa using h12'), List.map_nil] at *
    rw [← hx, reverseBytesQuad32_involutive, blockBE_blockQ, reverseBytesQuad32_involutive]

/-! ## `Parts` -/

/-- A `Parts` whose table hashes as GHASH does under the key AES gives the
zero block, whose `encrypt_block` is AES, whose `ctr` is GCTR, and whose
`pass` is the trait's. -/
structure PartsFor (alg : Algorithm) (kw : List (BitVec 32)) {S T : Type} (PI : mid.aes_gcm.Parts S T)
    (key : S) : Prop where
  table : ∃ t, PI.table key = ok t ∧ GhashFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) PI.GhashInst t
  encrypt_block : ∀ b, PI.encrypt_block key b ⦃ r => blockQ r = aesEncrypt alg kw (blockQ b) ⦄
  ctr : ∀ (J : Quad32) (ivec : Std.Array U8 16#usize), blockQ ivec = reverseBytesQuad32 J → ∀ inout : Slice U8,
    PI.ctr key ivec inout ⦃ r => blockQ r.1 = reverseBytesQuad32 (inc32 J ((inout.length + 15) / 16)) ∧
      r.2.length = inout.length ∧ ∀ j < inout.length, r.2.val[j]!.bv = inout.val[j]!.bv ^^^ ksByte alg kw J j ⦄
  pass : ∀ ENC, PI.pass ENC = mid.aes_gcm.Parts.pass.default ENC PI

/-- `pass` runs GCTR over `chunk` from `counter` and folds the ciphertext into
`xi`, returning the counter block after the chunk's. -/
theorem pass_spec (ENC : Bool) (alg : Algorithm) (kw : List (BitVec 32)) {S T : Type}
    (PI : mid.aes_gcm.Parts S T) (self : S) (hP : PartsFor alg kw PI self)
    (J : Quad32) (counter : Std.Array U8 16#usize) (hc : blockQ counter = reverseBytesQuad32 J)
    (xi : Std.Array U8 16#usize) (chunk : Slice U8) :
    mid.aes_gcm.Parts.pass.default ENC PI self xi counter chunk ⦃ r =>
      blockQ r.1 = reverseBytesQuad32 (inc32 J ((chunk.length + 15) / 16)) ∧ r.2.2.length = chunk.length ∧
      (∀ j < chunk.length, r.2.2.val[j]!.bv = chunk.val[j]!.bv ^^^ ksByte alg kw J j) ∧
      toPoly (blockBE r.2.1.val) = ghashPoly (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) (toPoly (blockBE xi.val))
        ((padBlocks (if ENC then r.2.2.val else chunk.val)).map toPoly) ⦄ := by
  obtain ⟨t, ht, hG⟩ := hP.table
  unfold mid.aes_gcm.Parts.pass.default
  rw [ht, bind_ok]
  cases ENC
  · simp only [Bool.false_eq_true, ite_false]
    step with ghash_pad_spec _ _ _ hG xi chunk as ⟨x1, hx1⟩
    step with hP.ctr J counter hc chunk as ⟨nx, ch1, hn, hl, hb⟩
    exact ⟨hn, hl, hb, hx1⟩
  · simp only [ite_true, bind_ok]
    step with hP.ctr J counter hc chunk as ⟨nx, ch1, hn, hl, hb⟩
    step with ghash_pad_spec _ _ _ hG xi ch1 as ⟨x1, hx1⟩
    exact ⟨hn, hl, hb, hx1⟩

/-! ## `tagged` -/

theorem getElem!_take_lt {α : Type _} [Inhabited α] (l : List α) {k n : Nat} (h : k < n) :
    (l.take n)[k]! = l[k]! := by
  simp [List.getElem!_eq_getElem?_getD, h]

/-- GCTR's output from counter block `J`, as bytes. -/
def gctrBytes (alg : Algorithm) (kw : List (BitVec 32)) (J : Quad32) (l : List U8) : List U8 :=
  (List.range l.length).map fun j => (⟨l[j]!.bv ^^^ ksByte alg kw J j⟩ : U8)

theorem length_gctrBytes (alg : Algorithm) (kw : List (BitVec 32)) (J : Quad32) (l : List U8) :
    (gctrBytes alg kw J l).length = l.length := by simp [gctrBytes]

theorem getElem!_gctrBytes (alg : Algorithm) (kw : List (BitVec 32)) (J : Quad32) (l : List U8) {j : Nat}
    (hj : j < l.length) : (gctrBytes alg kw J l)[j]!.bv = l[j]!.bv ^^^ ksByte alg kw J j := by
  rw [gctrBytes, getElem!_range_map _ hj]

theorem bvs_gctrBytes (alg : Algorithm) (kw : List (BitVec 32)) (J : Quad32) (l : List U8) :
    (gctrBytes alg kw J l).map (·.bv) = gctrEncrypt J (l.map (·.bv)) alg kw := by
  apply eq_gctr _ _ _ _ _ (by simp [length_gctrBytes])
  intro j hj
  simp only [List.length_map] at hj
  have h1 : j < (gctrBytes alg kw J l).length := by rw [length_gctrBytes]; exact hj
  rw [getElem!_pos _ j (by simpa using h1), getElem!_pos _ j (by simpa using hj), List.getElem_map,
    List.getElem_map, ← getElem!_pos _ j h1, ← getElem!_pos l j hj, getElem!_gctrBytes _ _ _ _ hj]

theorem padBlocks_append (a b : List U8) (ha : a.length % 16 = 0) :
    padBlocks (a ++ b) = padBlocks a ++ padBlocks b := by
  have hj : a.length = 16 * (a.length / 16) := by omega
  have hr : chunksRest 16 a = [] := List.eq_nil_of_length_eq_zero (by rw [chunksRest_length]; omega)
  rw [padBlocks, padBlocks, padBlocks, chunksOf_append (by omega) _ _ _ hj, chunksRest_append (by omega) _ _ _ hj,
    hr, ite_eq_left rfl, List.append_nil, List.map_append, List.append_assoc]

/-- The whole 3072-byte chunks, from `iter.start` on: each passes from the
counter block 192 blocks past the last's, its ciphertext folded into `xi`. -/
theorem tagged_loop0_spec (ENC : Bool) (alg : Algorithm) (kw : List (BitVec 32)) {S T : Type}
    (PI : mid.aes_gcm.Parts S T) (key : S) (hP : PartsFor alg kw PI key) (J1 : Quad32) (A : P)
    (c0 : Slice (Std.Array U8 3072#usize)) (C : List U8) (hCl : C.length = 3072 * c0.length)
    (hC : ∀ q < c0.length, ∀ i < 3072, C[3072 * q + i]!.bv = if ENC then
      (c0.val[q]!).val[i]!.bv ^^^ ksByte alg kw J1 (3072 * q + i) else (c0.val[q]!).val[i]!.bv)
    (iter : core.ops.range.Range Usize) (xi counter : Std.Array U8 16#usize)
    (chunks : Slice (Std.Array U8 3072#usize))
    (hs : iter.start.val ≤ c0.length) (he : iter.end.val = c0.length) (hl : chunks.length = c0.length)
    (hc : blockQ counter = reverseBytesQuad32 (inc32 J1 (192 * iter.start.val)))
    (hd : ∀ q < c0.length, ∀ i < 3072, (chunks.val[q]!).val[i]!.bv = if q < iter.start.val then
      (c0.val[q]!).val[i]!.bv ^^^ ksByte alg kw J1 (3072 * q + i) else (c0.val[q]!).val[i]!.bv)
    (hx : toPoly (blockBE xi.val) = ghashPoly (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) A
      ((padBlocks (C.take (3072 * iter.start.val))).map toPoly)) :
    mid.aes_gcm.Parts.tagged.default_loop0 ENC PI iter key xi counter chunks ⦃ r =>
      blockQ r.2.1 = reverseBytesQuad32 (inc32 J1 (192 * c0.length)) ∧ r.2.2.length = c0.length ∧
      (∀ q < c0.length, ∀ i < 3072,
        (r.2.2.val[q]!).val[i]!.bv = (c0.val[q]!).val[i]!.bv ^^^ ksByte alg kw J1 (3072 * q + i)) ∧
      toPoly (blockBE r.1.val) = ghashPoly (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) A
        ((padBlocks C).map toPoly) ⦄ := by
  unfold mid.aes_gcm.Parts.tagged.default_loop0
  apply loop.spec_decr_nat (fun x => c0.length - x.1.start.val)
    (fun x => x.1.start.val ≤ c0.length ∧ x.1.end.val = c0.length ∧ x.2.2.2.length = c0.length ∧
      blockQ x.2.2.1 = reverseBytesQuad32 (inc32 J1 (192 * x.1.start.val)) ∧
      (∀ q < c0.length, ∀ i < 3072, (x.2.2.2.val[q]!).val[i]!.bv = if q < x.1.start.val then
        (c0.val[q]!).val[i]!.bv ^^^ ksByte alg kw J1 (3072 * q + i) else (c0.val[q]!).val[i]!.bv) ∧
      toPoly (blockBE x.2.1.val) = ghashPoly (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) A
        ((padBlocks (C.take (3072 * x.1.start.val))).map toPoly))
  · rintro ⟨it, x, ct, ch⟩ ⟨hs, he, hl, hc, hd, hx⟩
    simp only at hs he hl hc hd hx ⊢
    unfold mid.aes_gcm.Parts.tagged.default_loop0.body
    have e0 : ch.length = ch.val.length := rfl
    have e1 : c0.length = c0.val.length := rfl
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst', hen⟩
      subst ho'
      rw [hP.pass ENC]
      step*
      have hst : it.start.val < c0.length := by omega
      have hsl : s.val.length = 3072 := by rw [s_post]; simp
      have hsj : ∀ j < 3072, s.val[j]!.bv = (c0.val[it.start.val]!).val[j]!.bv := by
        intro j hj
        rw [s_post, a_post, ← getElem!_pos ch.val it.start.val (by omega), hd _ hst j hj, ite_eq_right (by omega)]
      step with pass_spec ENC alg kw PI key hP (inc32 J1 (192 * it.start.val)) ct hc x s
        as ⟨n1, x1, s1, hn1, hs1l, hs1, hx1⟩
      have hs1l' : s1.val.length = 3072 := by simp only [Slice.length] at hs1l; omega
      have hfin : (index_mut_back (to_slice_mut_back s1)).val = ch.val.set it.start.val (Std.Array.from_slice a s1) := by
        rw [index_mut_back_post, to_slice_mut_back_post, Slice.set_val_eq]
      have hfs : (Std.Array.from_slice a s1).val = s1.val := Std.Array.from_slice_val a s1 hs1l'
      have hseg : (if ENC then s1.val else s.val) = (C.drop (3072 * it.start.val)).take 3072 := by
        apply eq_of_bv _ _ (by cases ENC <;> simp [hsl, hs1l', hCl] <;> omega)
        intro j hj
        have hj' : j < 3072 := by cases ENC <;> simp_all
        rw [getElem!_take_drop _ _ _ _ hj', hC _ hst _ hj']
        cases ENC
        · simp only [Bool.false_eq_true, ite_false]; exact hsj j hj'
        · simp only [ite_true]
          rw [hs1 j (by simp only [Slice.length]; omega), hsj j hj', ksByte_inc,
            show 16 * (192 * it.start.val) + j = 3072 * it.start.val + j by ring]
      refine ⟨by omega, by rw [hen]; omega, by simp [Slice.length, hfin] at hl ⊢; omega, ?_, ?_, ?_, by omega⟩
      · rw [hn1, show s.length = 3072 from hsl, inc32_inc32, hst']
        congr 2
      · intro q hq i hi
        rw [hfin]
        by_cases hqs : q = it.start.val
        · subst hqs
          rw [getElem!_pos (ch.val.set it.start.val (Std.Array.from_slice a s1)) it.start.val (by simp; omega),
            List.getElem_set_self, ite_eq_left (by omega), hfs,
            hs1 i (by simp only [Slice.length]; omega), hsj i hi, ksByte_inc,
            show 16 * (192 * it.start.val) + i = 3072 * it.start.val + i by ring]
        · rw [getElem!_set_of_ne _ _ (Ne.symm hqs), hd q hq i hi]
          by_cases hq2 : q < it.start.val
          · rw [ite_eq_left hq2, ite_eq_left (by omega)]
          · rw [ite_eq_right hq2, ite_eq_right (by omega)]
      · have htk : (C.take (3072 * it.start.val)).length % 16 = 0 := by
          rw [List.length_take, Nat.min_eq_left (by omega)]; omega
        rw [hx1, hx, hseg, ← ghashPoly_append, ← List.map_append, ← padBlocks_append _ _ htk, hst',
          show 3072 * (it.start.val + 1) = 3072 * it.start.val + 3072 by ring, List.take_add]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      simp only [WP.spec_ok]
      have hst : it.start.val = c0.length := by omega
      refine ⟨by rw [hc, hst], hl, fun q hq i hi => ?_, ?_⟩
      · rw [hd q hq i hi, ite_eq_left (by omega)]
      · rw [hx, hst, ← hCl, List.take_of_length_le le_rfl]
  · exact ⟨hs, he, hl, hc, hd, hx⟩

/-- The tag's mask, XORed in from byte `iter.start` on. -/
theorem tagged_loop1_spec (x0 mask : Std.Array U8 16#usize) (iter : core.ops.range.Range Usize)
    (xi : Std.Array U8 16#usize) (hs : iter.start.val ≤ 16) (he : iter.end.val = 16)
    (hd : ∀ i < 16, xi.val[i]!.bv = if i < iter.start.val then x0.val[i]!.bv ^^^ mask.val[i]!.bv else x0.val[i]!.bv) :
    mid.aes_gcm.Parts.tagged.default_loop1 iter xi mask ⦃ r =>
      ∀ i < 16, r.val[i]!.bv = x0.val[i]!.bv ^^^ mask.val[i]!.bv ⦄ := by
  unfold mid.aes_gcm.Parts.tagged.default_loop1
  apply loop.spec_decr_nat (fun x => 16 - x.1.start.val)
    (fun x => x.1.start.val ≤ 16 ∧ x.1.end.val = 16 ∧
      ∀ i < 16, x.2.val[i]!.bv = if i < x.1.start.val then x0.val[i]!.bv ^^^ mask.val[i]!.bv else x0.val[i]!.bv)
  · rintro ⟨it, x⟩ ⟨hs, he, hd⟩
    simp only at hs he hd ⊢
    unfold mid.aes_gcm.Parts.tagged.default_loop1.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst', hen⟩
      subst ho'
      step*
      refine ⟨by omega, by rw [hen]; omega, fun i hi => ?_, by omega⟩
      rw [a_post, Std.Array.set_val_eq]
      by_cases hie : i = it.start.val
      · subst hie
        rw [getElem!_pos _ _ (by simp; omega), List.getElem_set_self, ite_eq_left (by omega)]
        refine Eq.trans i3_post1 ?_
        have h1 := hd _ hi
        rw [ite_eq_right (by omega)] at h1
        rw [i2_post, i1_post, getElem!_pos x.val it.start.val (by simp; omega),
          getElem!_pos mask.val it.start.val (by simp; omega)] at *
        rw [← h1]
      · rw [getElem!_set_of_ne _ _ (Ne.symm hie), hd i hi]
        by_cases hlt2 : i < it.start.val
        · rw [ite_eq_left hlt2, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt2, ite_eq_right (by omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      simp only [WP.spec_ok]
      intro i hi
      rw [hd i hi, ite_eq_left (by omega)]
  · exact ⟨hs, he, hd⟩

/-- `tagged`'s last partial chunk, if any, through one `pass`. -/
theorem tagged_tail_spec (ENC : Bool) (alg : Algorithm) (kw : List (BitVec 32)) {S T : Type}
    (PI : mid.aes_gcm.Parts S T) (key : S) (hP : PartsFor alg kw PI key) (J : Quad32)
    (xi counter : Std.Array U8 16#usize) (hc : blockQ counter = reverseBytesQuad32 J) (tail : Slice U8)
    (b : Bool) (hb : (b = true) = (tail.length = 0)) :
    (if b = true then ok (xi, tail) else do
      let (_, xi4, tail2) ← PI.pass ENC key xi counter tail
      ok (xi4, tail2)) ⦃ r =>
      r.2.length = tail.length ∧ (∀ j < tail.length, r.2.val[j]!.bv = tail.val[j]!.bv ^^^ ksByte alg kw J j) ∧
      toPoly (blockBE r.1.val) = ghashPoly (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) (toPoly (blockBE xi.val))
        ((padBlocks (if ENC then r.2.val else tail.val)).map toPoly) ⦄ := by
  split
  · rename_i h
    have h0 : tail.val = [] := by simpa [Slice.length, h] using hb
    simp only [WP.spec_ok]
    refine ⟨by simp, fun j hj => by simp [Slice.length, h0] at hj, ?_⟩
    rw [h0]; cases ENC <;> simp [padBlocks_nil, ghashPoly_nil]
  · rw [hP.pass ENC]
    step with pass_spec ENC alg kw PI key hP J counter hc xi tail as ⟨n1, x1, t1, hn1, ht1l, ht1, hx1⟩
    exact ⟨ht1l, ht1, hx1⟩

/-- `tagged`, for any `Parts` that hashes, encrypts, and counts as GCM's do:
GCTR from `inc32 J0`, the block after `compute_iv_BE`'s counter block `J0`, and
the tag GCTR from `J0` on `gcm_hash` of the AAD and the ciphertext. -/
theorem tagged_spec (ENC : Bool) (alg : Algorithm) (kw : List (BitVec 32)) {S T : Type}
    (PI : mid.aes_gcm.Parts S T) (key : S) (hP : PartsFor alg kw PI key) (iv aad inout : Slice U8)
    (hiv : iv.length < 2 ^ 61) (haad : 8 * aad.length < 2 ^ 64) (hin : 8 * inout.length < 2 ^ 64) :
    mid.aes_gcm.Parts.tagged.default ENC PI key iv aad inout ⦃ r =>
      r.2.length = inout.length ∧
      r.2.val.map (·.bv) = gctrEncrypt (inc32 (computeIvBE (aesEncrypt alg kw (mkfour 0 0 0 0))
        (iv.val.map (·.bv))) 1) (inout.val.map (·.bv)) alg kw ∧
      r.1.val.map (·.bv) = gctrEncrypt (computeIvBE (aesEncrypt alg kw (mkfour 0 0 0 0)) (iv.val.map (·.bv)))
        (leQuad32ToBytes (gcmHash (aesEncrypt alg kw (mkfour 0 0 0 0)) (aad.val.map (·.bv))
          ((if ENC then r.2.val else inout.val).map (·.bv)))) alg kw ⦄ := by
  obtain ⟨t, ht, hG⟩ := hP.table
  generalize hH : aesEncrypt alg kw (mkfour 0 0 0 0) = hLE at hG ⊢
  generalize hj0 : computeIvBE hLE (iv.val.map (·.bv)) = j0
  have hmax := Slice.length_ineq inout
  have e0 : inout.length = inout.val.length := rfl
  unfold mid.aes_gcm.Parts.tagged.default
  rw [ht, bind_ok]
  step with initial_counter_spec hLE PI.GhashInst t hG iv hiv as ⟨y0, hy0⟩
  rw [hj0] at hy0
  step with ghash_pad_spec _ _ _ hG (Std.Array.repeat 16#usize 0#u8) aad as ⟨xi1, hxi1⟩
  rw [blockBE_zero, toPoly_zero] at hxi1
  step with add32_spec j0 y0 hy0 1#u32 as ⟨ctr, hctr⟩
  step with rind.modes.as_chunks_mut_spec 3072#usize (by decide) inout as ⟨chunks, tail, back, hcl, hc, ht, hback⟩
  -- The ciphertext GHASH reads.
  obtain ⟨Cf, hCfd⟩ : ∃ Cf : List U8, Cf = if ENC then gctrBytes alg kw (inc32 j0 1) inout.val else inout.val :=
    ⟨_, rfl⟩
  have hCfl : Cf.length = inout.length := by
    rw [hCfd]; split <;> simp [length_gctrBytes, Slice.length]
  have hCf : ∀ j < inout.length, Cf[j]!.bv = if ENC then inout.val[j]!.bv ^^^ ksByte alg kw (inc32 j0 1) j
      else inout.val[j]!.bv := by
    intro j hj
    rw [hCfd]; split
    · exact getElem!_gctrBytes _ _ _ _ (by omega)
    · rfl
  have e1 : chunks.length = chunks.val.length := rfl
  have hchunk : ∀ q < chunks.length, ∀ i < 3072, (chunks.val[q]!).val[i]!.bv = inout.val[3072 * q + i]!.bv := by
    intro q hq i hi
    rw [getElem!_pos chunks.val q (by omega), hc q (by omega), getElem!_take_drop _ _ _ _ hi, Nat.mul_comm]
  have hN : (3072#usize : Usize).val = 3072 := rfl
  have hLc : 3072 * chunks.length ≤ inout.length := by
    rw [hcl]; omega
  have hCt : (Cf.take (3072 * chunks.length)).length = 3072 * chunks.length := by
    rw [List.length_take]; omega
  have hCq : ∀ q < chunks.length, ∀ i < 3072, (Cf.take (3072 * chunks.length))[3072 * q + i]!.bv =
      if ENC then (chunks.val[q]!).val[i]!.bv ^^^ ksByte alg kw (inc32 j0 1) (3072 * q + i)
      else (chunks.val[q]!).val[i]!.bv := by
    intro q hq i hi
    have hlt : 3072 * q + i < 3072 * chunks.length := by
      have := Nat.mul_le_mul_left 3072 (show q + 1 ≤ chunks.length from hq); omega
    rw [getElem!_take_lt _ hlt, hCf _ (by omega), hchunk q hq i hi]
  have hctr0 : blockQ ctr = reverseBytesQuad32 (inc32 (inc32 j0 1) (192 * (0#usize : Usize).val)) := by
    rw [hctr]; simp [inc32_zero]
  have hd0 : ∀ q < chunks.length, ∀ i < 3072, (chunks.val[q]!).val[i]!.bv = if q < (0#usize : Usize).val then
      (chunks.val[q]!).val[i]!.bv ^^^ ksByte alg kw (inc32 j0 1) (3072 * q + i) else (chunks.val[q]!).val[i]!.bv := by
    intro q _ i _; simp
  have hx0 : toPoly (blockBE xi1.val) = ghashPoly (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0)))
      (toPoly (blockBE xi1.val)) ((padBlocks ((Cf.take (3072 * chunks.length)).take (3072 * (0#usize : Usize).val))).map toPoly) := by
    simp [padBlocks_nil, ghashPoly_nil]
  step with tagged_loop0_spec ENC alg kw PI key hP (inc32 j0 1) (toPoly (blockBE xi1.val)) chunks
    (Cf.take (3072 * chunks.length)) hCt hCq
    { start := 0#usize, «end» := chunks.len } xi1 ctr chunks (by simp) (by simp [Slice.length]) rfl
    hctr0 hd0 hx0
    as ⟨xi2, ctr1, chunks1, hctr1, hl1, hd1, hx2⟩
  step as ⟨b, hb⟩
  step with tagged_tail_spec ENC alg kw PI key hP _ xi2 ctr1 hctr1 tail b hb as ⟨xi3, tail1, ht1l, ht1, hx3⟩
  step with lengths_spec aad.len inout.len (by simpa using haad) (by simpa using hin) as ⟨a, ha⟩
  simp only [lift, bind_ok]
  step with hG xi3 as ⟨xi4, hx4⟩
  step with hP.encrypt_block y0 as ⟨mask, hmask⟩
  step with tagged_loop1_spec xi4 mask { start := 0#usize, «end» := 16#usize } xi4 (by simp) rfl
    (fun i _ => by simp) as ⟨xi5, hx5⟩
  rw [hH] at hx2 hx3
  -- The output, chunks and tail back together, is GCTR's.
  have e2 : tail.length = tail.val.length := rfl
  have htl : tail.length = inout.length - 3072 * chunks.length := by
    rw [e2, ht, List.length_drop, hcl, Nat.mul_comm]
  have hbk : (back (chunks1, tail1)).val = chunks1.val.flatMap (·.val) ++ tail1.val := by
    apply hback
    rw [List.length_append, length_flatMapN]
    have : (3072#usize : Usize).val * chunks1.val.length + tail1.val.length = inout.length := by
      have e3 : chunks1.length = chunks1.val.length := rfl
      have e4 : tail1.length = tail1.val.length := rfl
      rw [hN]; omega
    omega
  have ht1' : ∀ i < tail.length, tail1.val[i]!.bv = tail.val[i]!.bv ^^^
      ksByte alg kw (inc32 j0 1) ((3072#usize : Usize).val * chunks.length + i) := by
    intro i hi
    rw [ht1 i hi, ksByte_inc, hN, show 16 * (192 * chunks.length) + i = 3072 * chunks.length + i by ring]
  obtain ⟨hrl, hr⟩ := chunks_assemble (N := 3072#usize) (by decide) (ksByte alg kw (inc32 j0 1)) inout
    chunks chunks1 tail tail1 hcl hc ht hl1 (fun q hq i hi => hd1 q hq i hi) ht1l ht1' _ hbk
  have hbe : (back (chunks1, tail1)).val = gctrBytes alg kw (inc32 j0 1) inout.val := by
    apply eq_of_bv _ _ (by rw [length_gctrBytes]; exact hrl)
    intro j hj
    rw [hr j (by rw [← hrl]; exact hj), getElem!_gctrBytes _ _ _ _ (by rw [← e0]; omega)]
  have hCe : (if ENC then (back (chunks1, tail1)).val else inout.val) = Cf := by rw [hbe, hCfd]
  -- The GHASH input: the padded AAD, then the padded ciphertext.
  have hdrop : (if ENC then tail1.val else tail.val) = Cf.drop (3072 * chunks.length) := by
    have hil : (if ENC then tail1.val else tail.val).length = tail.length := by
      split
      · exact ht1l
      · rfl
    apply eq_of_bv _ _ (by rw [hil, List.length_drop, hCfl]; omega)
    intro j hj
    have hj' : j < tail.length := by rw [hil] at hj; exact hj
    have hti : tail.val[j]!.bv = inout.val[3072 * chunks.length + j]!.bv := by
      have : tail.val[j]! = inout.val[3072 * chunks.length + j]! := by
        rw [ht, ← hcl, Nat.mul_comm]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]
      rw [this]
    have hdj : (Cf.drop (3072 * chunks.length))[j]! = Cf[3072 * chunks.length + j]! := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]
    rw [hdj, hCf _ (by omega)]
    cases ENC
    · simpa using hti
    · simp only [ite_true]
      rw [ht1 j hj', hti, ksByte_inc, show 16 * (192 * chunks.length) + j = 3072 * chunks.length + j by ring]
  have htk : (Cf.take (3072 * chunks.length)).length % 16 = 0 := by
    rw [List.length_take, Nat.min_eq_left (by omega)]; omega
  have hpad : padBlocks Cf = padBlocks (Cf.take (3072 * chunks.length)) ++
      padBlocks (if ENC then tail1.val else tail.val) := by
    rw [hdrop, ← padBlocks_append _ _ htk, List.take_append_drop]
  have hsv : ((Array.make 1#usize [a] (by simp)).to_slice).val = [a] := rfl
  have hX : toPoly (blockBE xi4.val) = gf128MulRev (ghashPoly (polyLE hLE) 0
      ((padBlocks aad.val ++ padBlocks Cf).map toPoly) +
      toPoly (insertNat64 (insertNat64 (mkfour 0 0 0 0) (8 * aad.val.length) 1) (8 * Cf.length) 0)) (polyLE hLE) := by
    rw [hx4, hsv, List.map_singleton, ghashPoly_cons, ghashPoly_nil, hx3, hx2, hxi1, ha, hpad, List.map_append,
      List.map_append, ghashPoly_append, ghashPoly_append, hCfl]
    simp [Slice.length]
  have htag := gcmHash_eq hLE aad.val Cf (blockBE xi4.val) hX
  rw [blockBE_blockQ, reverseBytesQuad32_involutive] at htag
  refine ⟨hrl, by rw [hbe, bvs_gctrBytes], ?_⟩
  rw [hCe, ← htag, gctr_block, ← hy0, ← hmask]
  have hl5 : xi5.val.length = 16 := by simp
  apply List.ext_getElem (by simp [leQuad32ToBytes])
  intro i h1 h2
  rw [List.length_map, hl5] at h1
  rw [← getElem!_pos _ i (by simpa using h1), ← getElem!_pos _ i h2, leQuad32ToBytes_getElem! _ h1, byte_xor,
    blockQ, blockQ, byte_ofBytes _ h1, byte_ofBytes _ h1, ← hx5 i h1]
  rw [getElem!_pos _ i (by simpa using h1), List.getElem_map, getElem!_pos xi5.val i (by omega)]

/-! ## `Portable` -/

theorem inc32_mod (q : Quad32) (n : Nat) : inc32 q (n % 2 ^ 32) = inc32 q n := by
  rw [inc32_eq, inc32_eq]
  apply congrArg
  apply congrArg
  apply BitVec.eq_of_toNat_eq
  simp

/-- A `Portable` keyed with `kw`: its round keys and its GHASH table. -/
def PortableFor (alg : Algorithm) (kw : List (BitVec 32)) (p : mid.aes_gcm.Portable) : Prop :=
  Keyed alg kw p.key ∧ TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) p.table

/-- `Portable` hashes, encrypts, and counts as GCM's `Parts` do. -/
theorem portable_partsFor (alg : Algorithm) (kw : List (BitVec 32)) (p : mid.aes_gcm.Portable)
    (h : PortableFor alg kw p) :
    PartsFor alg kw mid.aes_gcm.Portable.Insts.RindMidAes_gcmPartsNohwTable p where
  table := ⟨p.table, rfl, nohw_ghashFor _ (small_toPoly _) p.table h.2⟩
  encrypt_block b := aes_key_encrypt_block_spec alg kw p.key h.1 b
  ctr J ivec hiv inout := by
    show mid.aes_gcm.Portable.Insts.RindMidAes_gcmPartsNohwTable.ctr p ivec inout ⦃ _ ⦄
    unfold mid.aes_gcm.Portable.Insts.RindMidAes_gcmPartsNohwTable.ctr low.portable.aes.AesKey.ctr32
    step with ctr32_spec alg kw p.key h.1 J ivec hiv inout as ⟨r, hrl, hr⟩
    step with div_ceil_spec r.len 16#usize (by decide) as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    step with add32_spec J ivec hiv i2 as ⟨a, ha⟩
    refine ⟨?_, hrl, hr⟩
    rw [ha, hi2, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, inc32_mod, hi1]
    simp [Slice.length, ← hrl]
  pass _ := rfl

theorem blockQ_zero : blockQ (Std.Array.repeat 16#usize 0#u8) = mkfour 0 0 0 0 := by
  rw [blockQ_load]; decide

/-- `Portable::new` keys `Portable` with the key's words. -/
theorem portable_new_spec (alg : Algorithm) (key : Slice U8) (h : KeyLen alg key.length) :
    mid.aes_gcm.Portable.new key ⦃ p => PortableFor alg (seqNat8ToSeqNat32LE (key.val.map (·.bv))) p ⦄ := by
  unfold mid.aes_gcm.Portable.new
  step with aes_key_new_spec alg key h as ⟨k, hk⟩
  step with aes_key_encrypt_block_spec alg _ k hk _ as ⟨hb, hhb⟩
  step with table_new_spec hb as ⟨t, ht⟩
  refine ⟨hk, ?_⟩
  rw [blockBE_blockQ, hhb, blockQ_zero] at ht
  exact ht

/-- An `AesGcm` keyed with `kw`, on any tier: the `Parts` it runs hash,
encrypt, and count as GCM's do. `aes_gcm_new_spec` makes one on `Portable`;
the NEON and crypto-extension tiers need only `PartsFor` their own `Arm`. -/
def GcmReady (alg : Algorithm) (kw : List (BitVec 32)) : mid.aes_gcm.AesGcm → Prop
  | .Portable p => PartsFor alg kw mid.aes_gcm.Portable.Insts.RindMidAes_gcmPartsNohwTable p
  | .Neon a => PartsFor alg kw (mid.aes_gcm.Arm.Insts.RindMidAes_gcmParts
      low.arm.vpaes_armv7.NeonKey.Insts.RindMidAes_gcmBlocksKey
      low.arm.ghash_armv4.NeonTable.Insts.RindMidAes_gcmGhash) a
  | .Hw a => PartsFor alg kw (mid.aes_gcm.Arm.Insts.RindMidAes_gcmParts
      low.arm.aesv8_armx.AesHwKey.Insts.RindMidAes_gcmBlocksKey
      low.arm.ghashv8_armx.GhashTable.Insts.RindMidAes_gcmGhash) a

/-- rind runs proven AES-GCM on this CPU: its entry guards pass, and its CPU
checks find neither the crypto extension nor NEON, so it keys `Portable`, the
one tier whose `Parts` are proven. None reads an input. -/
def RunsAesGcm : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧
  low.arm.cpu.HaveCryptoExt.check = ok none ∧ low.arm.cpu.HaveNeon.check = ok none

/-- `AesGcm::new`, finding neither the crypto extension nor NEON, keys
`Portable` with the key's words, which the theorem states as `GcmReady`, all
that `encrypt` and `decrypt` need. -/
theorem aes_gcm_new_spec (h : RunsAesGcm) (alg : Algorithm) (key : Slice U8) (hk : KeyLen alg key.length) :
    mid.aes_gcm.AesGcm.new key ⦃ g => GcmReady alg (seqNat8ToSeqNat32LE (bvs key.val)) g ⦄ := by
  obtain ⟨⟨e, he⟩, hce, hneon⟩ := h
  have hl : key.length ≤ 32 := by rcases hk with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  unfold mid.aes_gcm.AesGcm.new
  rw [he, bind_ok]
  step with Array.index_mut_SliceIndexRangeToUsizeSlice (Std.Array.repeat 32#usize 0#u8)
    { «end» := key.len } (by scalar_tac) as ⟨s, back, hs, hsl, hback⟩
  step with core.slice.Slice.copy_from_slice.step_spec _ s key (by rw [hsl]; simp) as ⟨s1, hs1⟩
  rw [hs1]
  simp only [low.ct.secret_slice, bind_ok, hce, hneon]
  step with portable_new_spec alg key hk as ⟨p, hp⟩
  exact portable_partsFor alg _ p hp

/-! ## The refusals -/

/-- `check_gcm_iv` refuses an empty IV or one of 2^61 bytes or more. -/
theorem check_gcm_iv_spec (iv : Slice U8) :
    mid.aes.check_gcm_iv iv ⦃ r =>
      r = if iv.length = 0 ∨ 2 ^ 61 ≤ iv.length then .Err .WrongLength else .Ok () ⦄ := by
  have hl := Slice.len_val iv
  have hb := usize_lt iv.len
  unfold mid.aes.check_gcm_iv
  step*
  all_goals
    have hc : i1.val = iv.length := by
      rw [i1_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, Nat.mod_eq_of_lt hb, hl]
    have h2 : i2.val = 2 ^ 61 := by rw [i2_post]; simp [Nat.shiftLeft_eq, U64.size, U64.numBits]
  · rw [ite_eq_left (Or.inr (by scalar_tac))]
  · rw [ite_eq_right (by simp_all)]

/-- From block 2, past the tag's, the 32-bit block counter covers 2^36 - 32
bytes. -/
theorem gcm_check_counter_spec (len : Usize) :
    mid.aes.check_counter 2#u32 len ⦃ r =>
      r = if len.val ≤ 2 ^ 36 - 32 then .Ok () else .Err .WrongLength ⦄ := by
  unfold mid.aes.check_counter core.num.Usize.div_ceil
  simp only [lift, bind_ok, show ¬ (16#usize : Usize).val = 0 by decide, ↓reduceDIte]
  have h1 : (core.convert.num.FromU64U32.from 2#u32 : U64).val = 2 := rfl
  have hb := usize_lt len
  have hm : (len.val + 16 - 1) / 16 % 2 ^ UScalarTy.U64.numBits = (len.val + 15) / 16 := by
    rw [UScalarTy.U64_numBits_eq]; apply Nat.mod_eq_of_lt; omega
  step*
  all_goals simp only [h1, UScalar.cast_val_eq, UScalar.ofNatCore_val_eq] at *
  all_goals simp only [hm] at *
  all_goals first
    | scalar_tac
    | (have h4 : i4.val = 2 ^ 32 := by rw [i4_post]; simp [Nat.shiftLeft_eq, U64.size, U64.numBits]
       first
        | (rw [ite_eq_right (by intro; scalar_tac)])
        | (rw [ite_eq_left (by scalar_tac)]))

/-- `check_gcm_lengths` refuses AAD of 2^61 bytes or more, and messages past
2^36 - 32 bytes. -/
theorem check_gcm_lengths_eq (aad msg : Usize) :
    mid.aes.check_gcm_lengths aad msg ⦃ r =>
      r = if 2 ^ 61 ≤ aad.val ∨ 2 ^ 36 - 32 < msg.val then .Err .WrongLength else .Ok () ⦄ := by
  have hb := usize_lt aad
  unfold mid.aes.check_gcm_lengths
  step*
  all_goals
    have hc : i.val = aad.val := by
      rw [i_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, Nat.mod_eq_of_lt hb]
    have h2 : i1.val = 2 ^ 61 := by rw [i1_post]; simp [Nat.shiftLeft_eq, U64.size, U64.numBits]
  · rw [ite_eq_left (Or.inl (by scalar_tac))]
  · apply WP.spec_mono (gcm_check_counter_spec msg)
    rintro r rfl
    by_cases hm : msg.val ≤ 2 ^ 36 - 32
    · rw [ite_eq_left hm, ite_eq_right (by scalar_tac)]
    · rw [ite_eq_right hm, ite_eq_left (Or.inr (by omega))]

/-! ## The API -/

theorem map_bv_beq (a b : List U8) : (a.map (·.bv) == b.map (·.bv)) = decide (a = b) := by
  have hinj : Function.Injective (fun x : U8 => x.bv) := by
    intro x y h; cases x; cases y; simp_all
  by_cases h : a = b
  · subst h; simp
  · have : a.map (·.bv) ≠ b.map (·.bv) := fun e => h (List.map_injective_iff.2 hinj e)
    simp [h, this]

/-- A slice of `tag` up to `n`, at most 16, is its first `n` bytes. -/
theorem index_tag (tag : Std.Array U8 16#usize) (n : Usize) (hn : n.val ≤ 16) :
    core.slice.index.SliceIndexRangeToUsizeSlice.index { «end» := n } tag.to_slice ⦃ s =>
      s.val = tag.val.take n.val ∧ s.length = n.val ⦄ := by
  apply WP.spec_mono (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec _ _
    (by simp [Std.Array.to_slice, Slice.length]; exact hn))
  rintro s ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  rw [h1]; simp [Std.Array.to_slice, List.slice]

/-- `tagged` on `Parts` keyed with `kw` is AES-GCM under the key bytes
`seqNat32ToSeqNat8LE kw`: its ciphertext or plaintext, and its tag over the
ciphertext. -/
theorem parts_tagged_spec (ENC : Bool) (alg : Algorithm) (kw : List (BitVec 32)) {S T : Type}
    (PI : mid.aes_gcm.Parts S T) (key : S) (hP : PartsFor alg kw PI key) (iv aad inout : Slice U8)
    (hiv : iv.length < 2 ^ 61) (haad : aad.length < 2 ^ 61) (hin : inout.length ≤ 2 ^ 36 - 32) :
    mid.aes_gcm.Parts.tagged.default ENC PI key iv aad inout
      ⦃ r => r.2.length = inout.length ∧
        r.2.val.map (·.bv) = (gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (iv.val.map (·.bv))
          (inout.val.map (·.bv)) (aad.val.map (·.bv)) []).1 ∧
        r.1.val.map (·.bv) = gcmTag alg (seqNat32ToSeqNat8LE kw) (iv.val.map (·.bv))
          ((if ENC then r.2.val else inout.val).map (·.bv)) (aad.val.map (·.bv)) ⦄ := by
  apply WP.spec_mono (tagged_spec ENC alg kw PI key hP iv aad inout hiv (by omega) (by omega))
  rintro r ⟨hl, hout, htag⟩
  refine ⟨hl, ?_, ?_⟩
  · rw [hout]; simp only [gcmDecrypt, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE]
  · rw [htag]; simp only [gcmTag, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE]

theorem gcmEncrypt_eq (alg : Algorithm) (key iv plain auth c t : List (BitVec 8))
    (hc : c = (gcmDecrypt alg key iv plain auth []).1) (ht : t = gcmTag alg key iv c auth) :
    (c, t) = gcmEncrypt alg key iv plain auth := by
  subst hc ht; rfl

/-- `AesGcm::encrypt` on a `GcmReady` key, for AAD under 2^61 bytes and
messages rind takes: the ciphertext in place and the tag are AES-GCM's. -/
theorem aes_gcm_encrypt_spec (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) (hg : GcmReady alg kw g)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (haad : aad.length < 2 ^ 61) (hin : inout.length ≤ 2 ^ 36 - 32) :
    mid.aes_gcm.AesGcm.encrypt g nonce aad inout tag ⦃ r =>
      r.1 = .Ok () ∧ r.2.1.length = inout.length ∧ (bvs r.2.1.val, bvs r.2.2.val) =
        gcmEncrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val) ⦄ := by
  simp only [bvs]
  obtain ⟨e, he⟩ := he
  cases g
  all_goals
    simp only [GcmReady] at hg
    unfold mid.aes_gcm.AesGcm.encrypt
    rw [he, bind_ok]
    apply WP.spec_bind (check_gcm_lengths_eq _ _)
    rintro r rfl
    rw [Slice.len_val, Slice.len_val, ite_eq_right (by omega)]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
    step with parts_tagged_spec true alg kw _ _ hg nonce.to_slice aad inout
      (by rw [Array.length_to_slice]; simp) haad hin as ⟨res, hl, hout, htag⟩
    obtain ⟨tg, out⟩ := res
    simp only [ite_true, Array.val_to_slice] at hl hout htag
    simp only [low.ct.public_slice, bind_ok]
    step*
    exact ⟨hl, gcmEncrypt_eq _ _ _ _ _ _ _ hout htag⟩

/-- `AesGcm::decrypt` on a `GcmReady` key, for AAD under 2^61 bytes and
messages rind takes: it succeeds exactly when the tag is AES-GCM's, leaving
the plaintext in place, and otherwise fails, leaving zeros. -/
theorem aes_gcm_decrypt_spec (he : ∃ e, low.entry.Entry.new_secret = ok e)
    (hheld : low.entry.Entry.assert_held = ok ()) (alg : Algorithm)
    (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) (hg : GcmReady alg kw g)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (haad : aad.length < 2 ^ 61) (hin : inout.length ≤ 2 ^ 36 - 32) :
    mid.aes_gcm.AesGcm.decrypt g nonce aad inout tag ⦃ r =>
      let out := gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val)
        (bvs aad.val) (bvs tag.val)
      if out.2 then r.1 = .Ok () ∧ bvs r.2.val = out.1
      else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate inout.length 0#u8 ⦄ := by
  simp only [bvs]
  obtain ⟨e, he⟩ := he
  cases g
  all_goals
    simp only [GcmReady] at hg
    unfold mid.aes_gcm.AesGcm.decrypt
    rw [he, bind_ok]
    apply WP.spec_bind (check_gcm_lengths_eq _ _)
    rintro r rfl
    rw [Slice.len_val, Slice.len_val, ite_eq_right (by omega)]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
    step with parts_tagged_spec false alg kw _ _ hg nonce.to_slice aad inout
      (by rw [Array.length_to_slice]; simp) haad hin as ⟨res, hl, hout, htag⟩
    obtain ⟨want, out⟩ := res
    simp only [Bool.false_eq_true, ite_false, Array.val_to_slice] at hl hout htag
    step*
    apply WP.spec_bind (ct_equal_spec hheld _ _)
    rintro b rfl
    simp only [Array.val_to_slice]
    have hb : (gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (nonce.val.map (·.bv)) (inout.val.map (·.bv))
        (aad.val.map (·.bv)) (tag.val.map (·.bv))).2 = decide (want.val = tag.val) := by
      rw [← map_bv_beq, htag]; simp only [gcmDecrypt, gcmTag]
    have hp1 : (gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (nonce.val.map (·.bv)) (inout.val.map (·.bv))
        (aad.val.map (·.bv)) (tag.val.map (·.bv))).1 = out.val.map (·.bv) := by
      rw [hout]; simp only [gcmDecrypt]
    simp only [hb, hp1, low.ct.into_public, bind_ok]
    by_cases hc : want.val = tag.val
    · simp only [hc, decide_true, ite_true, low.ct.public_slice, bind_ok, WP.spec_ok]
      exact ⟨trivial, trivial⟩
    · simp only [hc, decide_false, Bool.false_eq_true, ite_false]
      step*

/-- `AesGcm::encrypt_any` on a `GcmReady` key: an empty IV, or an IV or AAD
of 2^61 bytes or more, or a message past 2^36 - 32 bytes, is refused, and the
buffers left as they were; otherwise the ciphertext in place is AES-GCM's
under the IV, and `tag_out`, of at most 16 bytes, holds the first bytes of
its tag. -/
theorem aes_gcm_encrypt_any_spec (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) (hg : GcmReady alg kw g)
    (iv aad inout tag_out : Slice U8) (htl : tag_out.length ≤ 16) :
    mid.aes_gcm.AesGcm.encrypt_any g iv aad inout tag_out ⦃ r =>
      if iv.length = 0 ∨ 2 ^ 61 ≤ iv.length ∨ 2 ^ 61 ≤ aad.length ∨ 2 ^ 36 - 32 < inout.length then
        r.1 = .Err .WrongLength ∧ r.2.1 = inout ∧ r.2.2 = tag_out
      else
        let out := gcmEncrypt alg (seqNat32ToSeqNat8LE kw) (bvs iv.val) (bvs inout.val) (bvs aad.val)
        r.1 = .Ok () ∧ r.2.1.length = inout.length ∧ r.2.2.length = tag_out.length ∧
          bvs r.2.1.val = out.1 ∧ bvs r.2.2.val = out.2.take tag_out.length ⦄ := by
  simp only [bvs]
  obtain ⟨e, he⟩ := he
  cases g
  all_goals
    simp only [GcmReady] at hg
    unfold mid.aes_gcm.AesGcm.encrypt_any
    rw [he, bind_ok]
    apply WP.spec_bind (check_gcm_iv_spec iv)
    rintro r rfl
    by_cases hiv : iv.length = 0 ∨ 2 ^ 61 ≤ iv.length
    · simp only [hiv, ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      exact (WP.spec_ok _).2 (by simp_all; tauto)
    simp only [hiv, ite_false, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_bind (check_gcm_lengths_eq _ _)
    rintro r rfl
    rw [Slice.len_val, Slice.len_val]
    by_cases hl : 2 ^ 61 ≤ aad.length ∨ 2 ^ 36 - 32 < inout.length
    · simp only [hl, ite_true, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      exact (WP.spec_ok _).2 (by simp_all)
    simp only [hl, ite_false, bind_ok]
    step with parts_tagged_spec true alg kw _ _ hg iv aad inout (by omega) (by omega) (by omega) as ⟨res, hlen, hout, htag⟩
    obtain ⟨tag, out⟩ := res
    simp only [ite_true] at hlen hout htag
    step with index_tag tag tag_out.len (by rw [Slice.len_val]; exact htl) as ⟨s, hs1, hs2⟩
    step with core.slice.Slice.copy_from_slice.step_spec _ tag_out s (by rw [hs2, Slice.len_val]) as ⟨s', hs'⟩
    subst hs'
    simp only [low.ct.public_slice, bind_ok, WP.spec_ok]
    simp only [or_false, hiv, ite_false]
    have he := gcmEncrypt_eq _ _ _ _ _ _ _ hout htag
    refine ⟨trivial, hlen, by rw [hs2, Slice.len_val], by rw [← he], ?_⟩
    rw [hs1, Slice.len_val, List.map_take, ← he]

/-- `AesGcm::decrypt_any` on a `GcmReady` key: refused as `encrypt_any` is,
the buffer left as it was; otherwise it succeeds exactly when `tag`, of at most 16
bytes, is the first bytes of AES-GCM's tag under the IV, leaving the plaintext
in place, and otherwise fails, leaving zeros. -/
theorem aes_gcm_decrypt_any_spec (he : ∃ e, low.entry.Entry.new_secret = ok e)
    (hheld : low.entry.Entry.assert_held = ok ()) (alg : Algorithm)
    (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) (hg : GcmReady alg kw g)
    (iv aad inout tag : Slice U8) (htl : tag.length ≤ 16) :
    mid.aes_gcm.AesGcm.decrypt_any g iv aad inout tag ⦃ r =>
      if iv.length = 0 ∨ 2 ^ 61 ≤ iv.length ∨ 2 ^ 61 ≤ aad.length ∨ 2 ^ 36 - 32 < inout.length then
        r.1 = .Err .WrongLength ∧ r.2 = inout
      else
        let out := gcmDecryptTrunc alg (seqNat32ToSeqNat8LE kw) (bvs iv.val) (bvs inout.val)
          (bvs aad.val) (bvs tag.val)
        if out.2 then r.1 = .Ok () ∧ bvs r.2.val = out.1
        else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate inout.length 0#u8 ⦄ := by
  simp only [bvs]
  obtain ⟨e, he⟩ := he
  cases g
  all_goals
    simp only [GcmReady] at hg
    unfold mid.aes_gcm.AesGcm.decrypt_any
    rw [he, bind_ok]
    apply WP.spec_bind (check_gcm_iv_spec iv)
    rintro r rfl
    by_cases hiv : iv.length = 0 ∨ 2 ^ 61 ≤ iv.length
    · simp only [hiv, ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      exact (WP.spec_ok _).2 (by simp_all; tauto)
    simp only [hiv, ite_false, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_bind (check_gcm_lengths_eq _ _)
    rintro r rfl
    rw [Slice.len_val, Slice.len_val]
    by_cases hl : 2 ^ 61 ≤ aad.length ∨ 2 ^ 36 - 32 < inout.length
    · simp only [hl, ite_true, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      exact (WP.spec_ok _).2 (by simp_all)
    simp only [hl, ite_false, bind_ok]
    step with parts_tagged_spec false alg kw _ _ hg iv aad inout (by omega) (by omega) (by omega) as ⟨res, hlen, hout, htag⟩
    obtain ⟨want, out⟩ := res
    simp only [Bool.false_eq_true, ite_false] at hlen hout htag
    step with index_tag want tag.len (by rw [Slice.len_val]; exact htl) as ⟨s, hs1, hs2⟩
    step with ct_equal_spec hheld s tag as ⟨b, hb0⟩
    subst hb0
    simp only [or_false, hiv, ite_false]
    have hb : (gcmDecryptTrunc alg (seqNat32ToSeqNat8LE kw) (iv.val.map (·.bv)) (inout.val.map (·.bv))
        (aad.val.map (·.bv)) (tag.val.map (·.bv))).2 = decide (s.val = tag.val) := by
      rw [← map_bv_beq, hs1, Slice.len_val, List.map_take, htag]
      simp only [gcmDecryptTrunc, List.length_map, Slice.length]
    have hp1 : (gcmDecryptTrunc alg (seqNat32ToSeqNat8LE kw) (iv.val.map (·.bv)) (inout.val.map (·.bv))
        (aad.val.map (·.bv)) (tag.val.map (·.bv))).1 = out.val.map (·.bv) := by
      rw [hout]; simp only [gcmDecrypt, gcmDecryptTrunc]
    rw [hb, hp1]
    simp only [low.ct.into_public, bind_ok]
    by_cases hc : s.val = tag.val
    · simp only [hc, decide_true, ite_true, low.ct.public_slice, bind_ok, WP.spec_ok]
      exact ⟨trivial, trivial⟩
    · simp only [hc, decide_false, Bool.false_eq_true, ite_false]
      step*

end rind.armv7
