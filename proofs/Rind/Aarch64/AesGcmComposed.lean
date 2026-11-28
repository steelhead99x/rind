import Rind.Aarch64.AesGcm
open Aeneas Aeneas.Std Result rind.vale rind.simd Polynomial

/-!
# rind's composed AES-GCM on aarch64

`composed` runs AES-CTR and GHASH in turn over each 128-byte chunk, then the
rest: `aes_ctr::apply`, which `Rind.Aarch64.AesModesLow` proves is SP
800-38A's CTR mode, and `Ghash::add`, which `Rind.Aarch64.GhashPmull` proves
is GHASH over the padded blocks. `cipher` takes it for an AES-192 key on a
PMULL table without `eight_way`, the cores without SHA3, where no stitched
kernel takes the key. From the counter block `J` it is Vale's GCTR, byte by
byte as `Rind.GcmSpec`'s `ksByte` states it, and GHASH of the ciphertext's
padded blocks.
-/

local notation "P" => Polynomial (ZMod 2)
local notation "V" => core.core_arch.arm_shared.neon.uint64x2_t

namespace rind.aarch64.composed

open rind.aarch64 rind.aarch64.pmull

/-! ## The counter -/

/-- The counter block whose first 12 bytes are `nonce` and whose last four
are the counter `c` big-endian, `m + n` blocks past `J` when `c` is `m`
past `y`'s, which holds `J`. -/
theorem counter_quad (J : Quad32) (y : Std.Array U8 16#usize) (hy : loadBytes y.val = reverseBytesQuad32 J)
    (nonce : Std.Array U8 12#usize) (hn : nonce.val = y.val.take 12) (m n : Nat) (c : U32)
    (hc : c.bv = (y.val[12]!.bv ++ y.val[13]!.bv ++ y.val[14]!.bv ++ y.val[15]!.bv) + BitVec.ofNat 32 m) :
    leBytesToQuad32 (bvs nonce.val ++ be32 ((c.val + n) % 2 ^ 32)) = reverseBytesQuad32 (inc32 J (m + n)) := by
  have hbase : ∀ i < 12, y.val[i]! = nonce.val[i]! := by
    intro i hi
    rw [hn, List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_take, ite_eq_left hi]
  have hx := ctr_vec nonce y.val (by simp) hbase (c.bv + BitVec.ofNat 32 n)
  have hxn : (c.bv + BitVec.ofNat 32 n).toNat = (c.val + n) % 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [UScalar.bv_toNat]
    omega
  rw [hxn] at hx
  rw [← hx]
  have he := short.counter_eq J y hy (m + n)
  simp only at he
  rw [← he, hc, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `aes_ctr::apply` from the counter `c`, `m` blocks past the counter block
`y` holding `J`, XORs in GCTR's keystream from `J`, `16 m` bytes on. -/
theorem apply_ks (alg : Algorithm) (kw : List (BitVec 32)) (hk : low.aarch64.aes.HwKey)
    (hkey : HwKeyIs alg kw hk) (J : Quad32) (y : Std.Array U8 16#usize)
    (hy : loadBytes y.val = reverseBytesQuad32 J) (nonce : Std.Array U8 12#usize) (hn : nonce.val = y.val.take 12)
    (m : Nat) (c : U32)
    (hc : c.bv = (y.val[12]!.bv ++ y.val[13]!.bv ++ y.val[14]!.bv ++ y.val[15]!.bv) + BitVec.ofNat 32 m)
    (inout : Slice U8) :
    low.aarch64.aes_ctr.apply (.Hw hk) nonce c inout ⦃ r => r.length = inout.length ∧
      ∀ j < inout.length, r.val[j]!.bv = inout.val[j]!.bv ^^^ ksByte alg kw J (16 * m + j) ⦄ := by
  have hkey' : HwKeyIs alg (seqNat8ToSeqNat32LE (seqNat32ToSeqNat8LE kw)) hk := by
    rw [seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE]; exact hkey
  apply WP.spec_mono (aes_ctr_apply_hw_spec alg _ hk hkey' nonce c inout)
  intro r hr
  have hl : r.val.length = inout.val.length := by
    have := congrArg List.length hr
    simpa [bvs, aesCtr] using this
  refine ⟨hl, fun j hj => ?_⟩
  have hj' : j < inout.val.length := hj
  have h1 := congrArg (·[j]!) hr
  have hn12 : (bvs nonce.val).length = 12 := by simp
  have hcl : c.val < 2 ^ 32 := by scalar_tac
  rw [bvs_getElem! _ _ (by omega), aesCtr, getElem!_range_map _ (by simpa [bvs] using hj'),
    bvs_getElem! _ _ hj', ofBe_append, ofBe_be32 _ hcl] at h1
  rw [h1]
  congr 1
  have hct : ctrBlock 32 (ofBe (bvs nonce.val) * 256 ^ (be32 c.val).length + c.val) (j / 16) =
      ctrBlock 32 (ofBe (bvs nonce.val ++ be32 c.val)) (j / 16) := by
    rw [ofBe_append, ofBe_be32 _ hcl]
  rw [hct, ctr_block_eq _ hn12 _ _ hcl, aesBlock, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE,
    leQuad32ToBytes_getElem! _ (Nat.mod_lt _ (by omega)), counter_quad J y hy nonce hn m (j / 16) c hc, ksByte,
    show (16 * m + j) / 16 = m + j / 16 by omega, show (16 * m + j) % 16 = j % 16 by omega]

/-! ## The loop over 128-byte chunks -/

theorem padBlocks_append (a b : List U8) (ha : a.length % 16 = 0) :
    padBlocks (a ++ b) = padBlocks a ++ padBlocks b := by
  have hj : a.length = 16 * (a.length / 16) := by omega
  have hr : chunksRest 16 a = [] := List.eq_nil_of_length_eq_zero (by rw [chunksRest_length]; omega)
  rw [padBlocks, padBlocks, padBlocks, chunksOf_append (by omega) _ _ _ hj, chunksRest_append (by omega) _ _ _ hj,
    hr, ite_eq_left rfl, List.append_nil, List.map_append, List.append_assoc]

theorem getElem!_take_lt {α : Type _} [Inhabited α] (l : List α) {k n : Nat} (h : k < n) :
    (l.take n)[k]! = l[k]! := by
  simp [List.getElem!_eq_getElem?_getD, h]

/-- The whole 128-byte chunks, from `iter.start` on: each XORed with GCTR's
keystream from `J`, its counter eight blocks past the last's, and hashed
before decrypting or after encrypting, as `C`, the bytes GHASH reads, holds
them. -/
theorem loop_spec (ENC : Bool) (alg : Algorithm) (kw : List (BitVec 32)) (hk : low.aarch64.aes.HwKey)
    (hkey : HwKeyIs alg kw hk) (H : P) (hH : Small H) (t : low.aarch64.ghash.PmullTable) (ht : TableFor H t)
    (J : Quad32) (y : Std.Array U8 16#usize) (hy : loadBytes y.val = reverseBytesQuad32 J)
    (nonce : Std.Array U8 12#usize) (hn : nonce.val = y.val.take 12) (A : P)
    (c0 : Slice (Std.Array U8 128#usize)) (C : List U8) (hCl : C.length = 128 * c0.length)
    (hC : ∀ q < c0.length, ∀ i < 128, C[128 * q + i]!.bv = if ENC then
      (c0.val[q]!).val[i]!.bv ^^^ ksByte alg kw J (128 * q + i) else (c0.val[q]!).val[i]!.bv)
    (iter : core.ops.range.Range Usize) (x : V) (ctr : U32) (chunks : Slice (Std.Array U8 128#usize))
    (hs : iter.start.val ≤ c0.length) (he : iter.end.val = c0.length) (hl : chunks.length = c0.length)
    (hc : ctr.bv = (y.val[12]!.bv ++ y.val[13]!.bv ++ y.val[14]!.bv ++ y.val[15]!.bv) +
      BitVec.ofNat 32 (8 * iter.start.val))
    (hd : ∀ q < c0.length, ∀ i < 128, (chunks.val[q]!).val[i]!.bv = if q < iter.start.val then
      (c0.val[q]!).val[i]!.bv ^^^ ksByte alg kw J (128 * q + i) else (c0.val[q]!).val[i]!.bv)
    (hx : toPoly x = ghashPoly H A ((padBlocks (C.take (128 * iter.start.val))).map toPoly)) :
    low.aarch64.aes_gcm.composed_loop ENC iter (.Hw hk) (.Pmull t) x nonce ctr chunks ⦃ r =>
      r.1 = .Pmull t ∧
      r.2.2.1.bv = (y.val[12]!.bv ++ y.val[13]!.bv ++ y.val[14]!.bv ++ y.val[15]!.bv) +
        BitVec.ofNat 32 (8 * c0.length) ∧
      r.2.2.2.length = c0.length ∧
      (∀ q < c0.length, ∀ i < 128,
        (r.2.2.2.val[q]!).val[i]!.bv = (c0.val[q]!).val[i]!.bv ^^^ ksByte alg kw J (128 * q + i)) ∧
      toPoly r.2.1 = ghashPoly H A ((padBlocks C).map toPoly) ⦄ := by
  unfold low.aarch64.aes_gcm.composed_loop
  apply loop.spec_decr_nat (fun s => c0.length - s.1.start.val)
    (fun s => s.1.start.val ≤ c0.length ∧ s.1.end.val = c0.length ∧ s.2.1 = .Pmull t ∧
      s.2.2.2.2.length = c0.length ∧
      s.2.2.2.1.bv = (y.val[12]!.bv ++ y.val[13]!.bv ++ y.val[14]!.bv ++ y.val[15]!.bv) +
        BitVec.ofNat 32 (8 * s.1.start.val) ∧
      (∀ q < c0.length, ∀ i < 128, (s.2.2.2.2.val[q]!).val[i]!.bv = if q < s.1.start.val then
        (c0.val[q]!).val[i]!.bv ^^^ ksByte alg kw J (128 * q + i) else (c0.val[q]!).val[i]!.bv) ∧
      toPoly s.2.2.1 = ghashPoly H A ((padBlocks (C.take (128 * s.1.start.val))).map toPoly))
  · rintro ⟨it, gt, ux, ct, ch⟩ ⟨hs, he, hgt, hl, hc, hd, hx⟩
    simp only at hs he hgt hl hc hd hx ⊢
    subst hgt
    unfold low.aarch64.aes_gcm.composed_loop.body
    have e0 : ch.length = ch.val.length := rfl
    have e1 : c0.length = c0.val.length := rfl
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst', hen⟩
      subst ho'
      have hst : it.start.val < c0.length := by omega
      have hsj : ∀ j < 128, (ch.val[it.start.val]!).val[j]!.bv = (c0.val[it.start.val]!).val[j]!.bv := by
        intro j hj
        rw [hd _ hst j hj, ite_eq_right (by omega)]
      cases ENC
      · simp only [Bool.false_eq_true, ↓reduceIte] at hC ⊢
        step with Slice.index_usize_spec as ⟨a0, ha0⟩
        step as ⟨x, x_post⟩
        obtain ⟨y1, hy1, hpy1⟩ := ghash_add_spec H hH t ht ux x
        have hxv : x.val = (ch.val[it.start.val]!).val := by
          rw [x_post, Std.Array.val_to_slice, ha0, getElem!_pos ch.val it.start.val (by omega)]
        rw [hy1]
        step*
        step with apply_ks alg kw hk hkey J y hy nonce hn (8 * it.start.val) ct hc s as ⟨s1, hs1l, hs1⟩
        step*
        have hsl : s.val.length = 128 := by rw [s_post]; simp
        have hs1l' : s1.val.length = 128 := by simp only [Slice.length] at hs1l; omega
        have hfin : (index_mut_back (to_slice_mut_back s1)).val =
            ch.val.set it.start.val (Std.Array.from_slice a s1) := by
          rw [index_mut_back_post, to_slice_mut_back_post, Slice.set_val_eq]
        have hfs : (Std.Array.from_slice a s1).val = s1.val := Std.Array.from_slice_val a s1 hs1l'
        have hsj' : ∀ j < 128, s.val[j]!.bv = (c0.val[it.start.val]!).val[j]!.bv := by
          intro j hj
          rw [s_post, a_post, ← getElem!_pos ch.val it.start.val (by omega), hsj j hj]
        have hks : ∀ j < 128, s1.val[j]!.bv = (c0.val[it.start.val]!).val[j]!.bv ^^^
            ksByte alg kw J (128 * it.start.val + j) := by
          intro j hj
          rw [hs1 j (by simp only [Slice.length]; omega), hsj' j hj,
            show 16 * (8 * it.start.val) + j = 128 * it.start.val + j by ring]
        have hctr : (core.num.U32.wrapping_add ct 8#u32).bv =
            (y.val[12]!.bv ++ y.val[13]!.bv ++ y.val[14]!.bv ++ y.val[15]!.bv) +
              BitVec.ofNat 32 (8 * it'.start.val) := by
          rw [core.num.U32.wrapping_add_bv_eq, hc, hst']
          generalize y.val[12]!.bv ++ y.val[13]!.bv ++ y.val[14]!.bv ++ y.val[15]!.bv = b
          apply BitVec.eq_of_toNat_eq
          simp
          omega
        have htk : (C.take (128 * it.start.val)).length % 16 = 0 := by
          rw [List.length_take, Nat.min_eq_left (by omega)]; omega
        have hseg : x.val = (C.drop (128 * it.start.val)).take 128 := by
          rw [hxv]
          apply eq_of_bv _ _ (by simp [hCl]; omega)
          intro j hj
          have hj' : j < 128 := by simpa using hj
          rw [getElem!_take_drop _ _ _ _ hj', hC _ hst _ hj', hsj j hj']
        refine ⟨by omega, by rw [hen]; omega, by simp [Slice.length, hfin] at hl ⊢; omega, by rw [ctr1_post, hctr],
          ?_, ?_, by omega⟩
        · intro q hq i hi
          rw [hfin]
          by_cases hqs : q = it.start.val
          · subst hqs
            rw [getElem!_pos (ch.val.set it.start.val (Std.Array.from_slice a s1)) it.start.val (by simp; omega),
              List.getElem_set_self, ite_eq_left (by omega), hfs, hks i hi]
          · rw [getElem!_set_of_ne _ _ (Ne.symm hqs), hd q hq i hi]
            by_cases hq2 : q < it.start.val
            · rw [ite_eq_left hq2, ite_eq_left (by omega)]
            · rw [ite_eq_right hq2, ite_eq_right (by omega)]
        · rw [hpy1, hx, hseg, ← ghashPoly_append, ← List.map_append, ← padBlocks_append _ _ htk, hst',
            show 128 * (it.start.val + 1) = 128 * it.start.val + 128 by ring, List.take_add]
      · simp only [↓reduceIte] at hC ⊢
        step*
        step with apply_ks alg kw hk hkey J y hy nonce hn (8 * it.start.val) ct hc s as ⟨s1, hs1l, hs1⟩
        step*
        · simp only [Slice.length] at hl ⊢
          rw [index_mut_back_post, Slice.set_val_eq, List.length_set]
          omega
        obtain ⟨y1, hy1, hpy1⟩ := ghash_add_spec H hH t ht ux s2
        rw [hy1]
        step*
        have hsl : s.val.length = 128 := by rw [s_post]; simp
        have hs1l' : s1.val.length = 128 := by simp only [Slice.length] at hs1l; omega
        have hfin : (index_mut_back (to_slice_mut_back s1)).val =
            ch.val.set it.start.val (Std.Array.from_slice a s1) := by
          rw [index_mut_back_post, to_slice_mut_back_post, Slice.set_val_eq]
        have hfs : (Std.Array.from_slice a s1).val = s1.val := Std.Array.from_slice_val a s1 hs1l'
        have hsj' : ∀ j < 128, s.val[j]!.bv = (c0.val[it.start.val]!).val[j]!.bv := by
          intro j hj
          rw [s_post, a_post, ← getElem!_pos ch.val it.start.val (by omega), hsj j hj]
        have hks : ∀ j < 128, s1.val[j]!.bv = (c0.val[it.start.val]!).val[j]!.bv ^^^
            ksByte alg kw J (128 * it.start.val + j) := by
          intro j hj
          rw [hs1 j (by simp only [Slice.length]; omega), hsj' j hj,
            show 16 * (8 * it.start.val) + j = 128 * it.start.val + j by ring]
        have hctr : (core.num.U32.wrapping_add ct 8#u32).bv =
            (y.val[12]!.bv ++ y.val[13]!.bv ++ y.val[14]!.bv ++ y.val[15]!.bv) +
              BitVec.ofNat 32 (8 * it'.start.val) := by
          rw [core.num.U32.wrapping_add_bv_eq, hc, hst']
          generalize y.val[12]!.bv ++ y.val[13]!.bv ++ y.val[14]!.bv ++ y.val[15]!.bv = b
          apply BitVec.eq_of_toNat_eq
          simp
          omega
        have htk : (C.take (128 * it.start.val)).length % 16 = 0 := by
          rw [List.length_take, Nat.min_eq_left (by omega)]; omega
        have hs2 : s2.val = s1.val := by
          rw [s2_post, Std.Array.val_to_slice, a2_post, ← getElem!_pos _ it.start.val (by simp [hfin]; omega), hfin,
            getElem!_pos (ch.val.set it.start.val (Std.Array.from_slice a s1)) it.start.val (by simp; omega),
            List.getElem_set_self, hfs]
        have hseg : s2.val = (C.drop (128 * it.start.val)).take 128 := by
          rw [hs2]
          apply eq_of_bv _ _ (by simp [hCl, hs1l']; omega)
          intro j hj
          have hj' : j < 128 := by omega
          rw [getElem!_take_drop _ _ _ _ hj', hC _ hst _ hj', hks j hj']
        refine ⟨by omega, by rw [hen]; omega, by simp [Slice.length, hfin] at hl ⊢; omega, by rw [ctr1_post, hctr],
          ?_, ?_, by omega⟩
        · intro q hq i hi
          rw [hfin]
          by_cases hqs : q = it.start.val
          · subst hqs
            rw [getElem!_pos (ch.val.set it.start.val (Std.Array.from_slice a s1)) it.start.val (by simp; omega),
              List.getElem_set_self, ite_eq_left (by omega), hfs, hks i hi]
          · rw [getElem!_set_of_ne _ _ (Ne.symm hqs), hd q hq i hi]
            by_cases hq2 : q < it.start.val
            · rw [ite_eq_left hq2, ite_eq_left (by omega)]
            · rw [ite_eq_right hq2, ite_eq_right (by omega)]
        · rw [hpy1, hx, hseg, ← ghashPoly_append, ← List.map_append, ← padBlocks_append _ _ htk, hst',
            show 128 * (it.start.val + 1) = 128 * it.start.val + 128 by ring, List.take_add]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      simp only [WP.spec_ok]
      have hst : it.start.val = c0.length := by omega
      refine ⟨trivial, by rw [hc, hst], hl, fun q hq i hi => ?_, ?_⟩
      · rw [hd q hq i hi, ite_eq_left (by omega)]
      · rw [hx, hst, ← hCl, List.take_of_length_le le_rfl]
  · exact ⟨hs, he, rfl, hl, hc, hd, hx⟩

/-! ## `composed` -/

/-- `try_into` of a slice of length `N` to an owned array holds its bytes. -/
theorem copy_try_from_len (N : Usize) (s : Slice U8) (h : s.length = N.val) :
    ∃ a : Std.Array U8 N, core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 s = ok (.Ok a) ∧
      a.val = s.val := by
  unfold core.array.TryFromArrayCopySlice.try_from
  rw [dite_eq_left h]
  exact ⟨_, rfl, by simp [Std.Array.from_val]⟩

/-- Four bytes read big-endian are the bytes concatenated. -/
theorem fromBE_four (l : List (BitVec 8)) (a b c d : BitVec 8) (hl : l = [a, b, c, d]) (h : 8 * l.length = 32) :
    (BitVec.fromBEBytes l).cast h = a ++ b ++ c ++ d := by
  subst hl
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_cast]
  show (BitVec.fromLEBytes [d, c, b, a]).getLsbD k = _
  simp only [BitVec.fromLEBytes, List.length_cons, List.length_nil]
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  interval_cases k <;> simp [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]

/-- GCTR from `J` on `l`, as bytes. -/
def gctrBytes (alg : Algorithm) (kw : List (BitVec 32)) (J : Quad32) (l : List U8) : List U8 :=
  (List.range l.length).map fun j => (⟨l[j]!.bv ^^^ ksByte alg kw J j⟩ : U8)

theorem length_gctrBytes (alg : Algorithm) (kw : List (BitVec 32)) (J : Quad32) (l : List U8) :
    (gctrBytes alg kw J l).length = l.length := by simp [gctrBytes]

theorem getElem!_gctrBytes (alg : Algorithm) (kw : List (BitVec 32)) (J : Quad32) (l : List U8) {j : Nat}
    (hj : j < l.length) : (gctrBytes alg kw J l)[j]!.bv = l[j]!.bv ^^^ ksByte alg kw J j := by
  rw [gctrBytes, getElem!_range_map _ hj]

/-- `composed` from the counter block `y` holding `J`, on a crypto-extension
key and a PMULL table: GCTR from `J`, and GHASH from `x` over the
ciphertext's padded blocks. -/
theorem composed_spec (ENC : Bool) (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (H : P) (hH : Small H) (t : low.aarch64.ghash.PmullTable) (ht : TableFor H t)
    (x : V) (J : Quad32) (y : Std.Array U8 16#usize) (hy : loadBytes y.val = reverseBytesQuad32 J)
    (inout : Slice U8) :
    low.aarch64.aes_gcm.composed ENC (.Hw hk) ⟨.Pmull t, x⟩ y inout ⦃ r =>
      r.1.table = .Pmull t ∧ r.2.length = inout.length ∧ bvs r.2.val = gctrEncrypt J (bvs inout.val) alg kw ∧
      toPoly r.1.current = ghashPoly H (toPoly x) ((padBlocks (if ENC then r.2.val else inout.val)).map toPoly) ⦄ := by
  unfold low.aarch64.aes_gcm.composed
  have hmax := Slice.length_ineq inout
  have e0 : inout.length = inout.val.length := rfl
  have hyl : y.val.length = 16 := by simp
  step*
  have hsv : s.val = y.val := by rw [s_post, Std.Array.val_to_slice]
  obtain ⟨nonce1, hn1, hn1v⟩ := try_from_len 12#usize nonce nonce_post
  have hctrl : ctr.length = (4#usize : Usize).val := by
    rw [nonce_post1]; simp [Slice.length, hsv, hyl]
  obtain ⟨a, ha, hav⟩ := copy_try_from_len 4#usize ctr hctrl
  rw [hn1, ha]
  simp only [bind_ok, core.result.Result.unwrap]
  step with core.num.U32.from_be_bytes.step_spec as ⟨ctr1, hctr1⟩
  have hab : a.val.map U8.bv = [y.val[12]!.bv, y.val[13]!.bv, y.val[14]!.bv, y.val[15]!.bv] := by
    rw [hav, nonce_post3, hsv]
    apply List.ext_getElem (by simp [hyl])
    intro i h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    interval_cases i <;> simp [hyl]
  rw [fromBE_four _ _ _ _ _ hab] at hctr1
  step with as_chunks_mut_spec 128#usize inout (by decide) as ⟨chunks, tail, back, hcl, hci, htl, hback⟩
  have hc : ∀ i (h : i < chunks.val.length), (chunks.val[i]).val = (inout.val.drop (i * (128#usize : Usize).val)).take
      (128#usize : Usize).val := fun i h => by rw [← getElem!_pos chunks.val i h]; exact hci i h
  -- The ciphertext GHASH reads.
  obtain ⟨Cf, hCfd⟩ : ∃ Cf : List U8, Cf = if ENC then gctrBytes alg kw J inout.val else inout.val :=
    ⟨_, rfl⟩
  have hCfl : Cf.length = inout.length := by
    rw [hCfd]; split <;> simp [length_gctrBytes, Slice.length]
  have hCf : ∀ j < inout.length, Cf[j]!.bv = if ENC then inout.val[j]!.bv ^^^ ksByte alg kw J j
      else inout.val[j]!.bv := by
    intro j hj
    rw [hCfd]; split
    · exact getElem!_gctrBytes _ _ _ _ (by omega)
    · rfl
  have e1 : chunks.length = chunks.val.length := rfl
  have hN : (128#usize : Usize).val = 128 := rfl
  have hchunk : ∀ q < chunks.length, ∀ i < 128, (chunks.val[q]!).val[i]!.bv = inout.val[128 * q + i]!.bv := by
    intro q hq i hi
    rw [hci q (by omega), getElem!_take_drop _ _ _ _ hi, Nat.mul_comm]
  have hLc : 128 * chunks.length ≤ inout.length := by
    rw [e1, hcl]; omega
  have hCt : (Cf.take (128 * chunks.length)).length = 128 * chunks.length := by
    rw [List.length_take]; omega
  have hCq : ∀ q < chunks.length, ∀ i < 128, (Cf.take (128 * chunks.length))[128 * q + i]!.bv =
      if ENC then (chunks.val[q]!).val[i]!.bv ^^^ ksByte alg kw J (128 * q + i)
      else (chunks.val[q]!).val[i]!.bv := by
    intro q hq i hi
    have hlt : 128 * q + i < 128 * chunks.length := by
      have := Nat.mul_le_mul_left 128 (show q + 1 ≤ chunks.length from hq); omega
    rw [getElem!_take_lt _ hlt, hCf _ (by omega), hchunk q hq i hi]
  have hnn : nonce1.val = y.val.take 12 := by rw [hn1v, nonce_post2, hsv]
  have hc0 : ctr1.bv = (y.val[12]!.bv ++ y.val[13]!.bv ++ y.val[14]!.bv ++ y.val[15]!.bv) +
      BitVec.ofNat 32 (8 * (0#usize : Usize).val) := by
    rw [hctr1]; simp
  have hd0 : ∀ q < chunks.length, ∀ i < 128, (chunks.val[q]!).val[i]!.bv = if q < (0#usize : Usize).val then
      (chunks.val[q]!).val[i]!.bv ^^^ ksByte alg kw J (128 * q + i) else (chunks.val[q]!).val[i]!.bv := by
    intro q _ i _; simp
  have hx0 : toPoly x = ghashPoly H (toPoly x)
      ((padBlocks ((Cf.take (128 * chunks.length)).take (128 * (0#usize : Usize).val))).map toPoly) := by
    simp [padBlocks_nil, ghashPoly_nil]
  step with loop_spec ENC alg kw hk hkey H hH t ht J y hy nonce1 hnn (toPoly x) chunks
    (Cf.take (128 * chunks.length)) hCt hCq { start := 0#usize, «end» := chunks.len } x ctr1 chunks
    (by simp) (by simp [Slice.len, Slice.length]) rfl hc0 hd0 hx0
    as ⟨gt, ux, ctr2, chunks1, hgt, hctr2, hl1, hd1, hx2⟩
  subst hgt
  -- The output, chunks and tail back together, is GCTR's.
  have e2 : tail.length = tail.val.length := rfl
  have htl2 : tail.val = inout.val.drop (128 * chunks.length) := by
    rw [htl, e1, hcl, Nat.mul_comm]
  have htll : tail.length = inout.length - 128 * chunks.length := by
    rw [e2, htl2, List.length_drop]
  have hbk : ∀ t1 : Slice U8, t1.length = tail.length →
      (back (chunks1, t1)).val = chunks1.val.flatMap (·.val) ++ t1.val := by
    intro t1 ht1l
    apply hback
    rw [List.length_append, length_flatMapN]
    have e3 : chunks1.length = chunks1.val.length := rfl
    have e4 : t1.length = t1.val.length := rfl
    rw [hN]; omega
  have hout : ∀ t1 : Slice U8, t1.length = tail.length →
      (∀ i < tail.length, t1.val[i]!.bv = tail.val[i]!.bv ^^^ ksByte alg kw J (16 * (8 * chunks.length) + i)) →
      (back (chunks1, t1)).length = inout.length ∧
        bvs (back (chunks1, t1)).val = gctrEncrypt J (bvs inout.val) alg kw ∧
        (back (chunks1, t1)).val = gctrBytes alg kw J inout.val := by
    intro t1 ht1l ht1
    obtain ⟨hrl, hr⟩ := chunks_assemble (N := 128#usize) (by decide) (ksByte alg kw J) inout chunks chunks1
      tail t1 hcl hc htl hl1 (fun q hq i hi => hd1 q hq i hi) ht1l
      (fun i hi => by rw [ht1 i hi, hN, show 16 * (8 * chunks.length) + i = 128 * chunks.length + i by ring])
      _ (hbk t1 ht1l)
    refine ⟨hrl, ?_, ?_⟩
    · apply eq_gctr _ _ _ _ _ (by simp [Slice.length] at hrl ⊢; omega)
      intro j hj
      simp only [bvs, List.length_map] at hj
      rw [bvs_getElem! _ _ (by simp [Slice.length] at hrl; omega), bvs_getElem! _ _ hj, hr j hj]
    · apply eq_of_bv _ _ (by rw [length_gctrBytes]; exact hrl)
      intro j hj
      have hj' : j < inout.val.length := by simp [Slice.length] at hrl; omega
      rw [hr j hj', getElem!_gctrBytes _ _ _ _ hj']
  have htk : (Cf.take (128 * chunks.length)).length % 16 = 0 := by rw [hCt]; omega
  cases ENC
  · simp only [Bool.false_eq_true, ↓reduceIte] at hCfd ⊢
    subst hCfd
    obtain ⟨y2, hy2, hpy2⟩ := ghash_add_spec H hH t ht ux tail
    rw [hy2]
    simp only [bind_ok]
    step with apply_ks alg kw hk hkey J y hy nonce1 hnn (8 * chunks.length) ctr2 hctr2 tail as ⟨t1, ht1l, ht1⟩
    obtain ⟨hrl, hrb, -⟩ := hout t1 ht1l ht1
    refine ⟨hrl, hrb, ?_⟩
    rw [hpy2, hx2, ← ghashPoly_append, ← List.map_append, ← padBlocks_append _ _ htk, htl2, List.take_append_drop]
  · simp only [↓reduceIte] at hCfd ⊢
    subst hCfd
    simp only [bind_ok]
    step with apply_ks alg kw hk hkey J y hy nonce1 hnn (8 * chunks.length) ctr2 hctr2 tail as ⟨t1, ht1l, ht1⟩
    obtain ⟨y2, hy2, hpy2⟩ := ghash_add_spec H hH t ht ux t1
    rw [hy2]
    simp only [bind_ok, WP.spec_ok]
    obtain ⟨hrl, hrb, hrg⟩ := hout t1 ht1l ht1
    refine ⟨trivial, hrl, hrb, ?_⟩
    have hfl : (chunks1.val.flatMap (·.val)).length = 128 * chunks.length := by
      rw [length_flatMapN, hN, ← hl1]
    have hd : t1.val = (gctrBytes alg kw J inout.val).drop (128 * chunks.length) := by
      rw [← hrg, hbk t1 ht1l, List.drop_left' hfl]
    rw [hpy2, hx2, ← ghashPoly_append, ← List.map_append, ← padBlocks_append _ _ htk, hd, List.take_append_drop,
      hrg]

end rind.aarch64.composed
