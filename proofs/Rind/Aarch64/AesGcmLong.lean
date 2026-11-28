import Rind.Aarch64.AesGcmComposed
import Rind.Aarch64.S2nBignum
import Rind.Aarch64.AesModesLow
open Aeneas Aeneas.Std Result rind.vale rind.simd Polynomial

/-!
# rind's AES-GCM on aarch64 past `short`'s lengths

`cipher` with the crypto extension's key and a PMULL table: for an AES-128
or AES-256 key, `stitched` runs s2n-bignum's kernel on the whole blocks,
whose theorems `Rind.Aarch64.S2nBignum` restates, and `partial` the last
partial block; for an AES-192 key on a table without `eight_way`, the cores
without SHA3, `composed` runs AES-CTR and GHASH in turn, which
`Rind.Aarch64.AesGcmComposed` proves. `Rind.S2nGcm` proves the kernels'
specs are Vale's, so `cipher` is Vale's GCTR from the block after the counter
block and GHASH over the AAD's and the ciphertext's padded blocks,
`tagged_from` is GCTR and `gcm_hash` at every length below `2 ^ 61` bytes,
and `tagged` with a 96-bit nonce is `gcm_encrypt_LE` and `gcm_decrypt_LE`.
On the cores with SHA3, `stitched` runs the `_alt` kernels only when the
blocks' address plus their length is below 2^63, as their theorems require,
and the four-way kernels otherwise; there each theorem also takes a key other
than AES-192, whose eight-way kernels, aws-lc's, no proof covers.
-/

local notation "P" => Polynomial (ZMod 2)
local notation "V" => core.core_arch.arm_shared.neon.uint64x2_t

namespace rind.aarch64.long

open rind.aarch64 rind.aarch64.pmull rind.s2n

/-! ## Byte order -/

theorem rev_leBytesToQuad32 (L : List (BitVec 8)) (hL : L.length = 16) :
    reverseBytesQuad32 (leBytesToQuad32 L) = leBytesToQuad32 L.reverse := by
  rw [reverseBytesQuad32, short.leQuad32ToBytes_leBytesToQuad32 L hL]

/-- `u128::from_be_bytes` of a block is its bytes loaded and reversed. -/
theorem from_be_eq (a : Std.Array U8 16#usize) :
    (core.num.U128.from_be_bytes a).bv = reverseBytesQuad32 (loadBytes a.val) := by
  rw [loadBytes, rev_leBytesToQuad32 _ (by simp), leBytesToQuad32]
  unfold core.num.U128.from_be_bytes
  apply BitVec.eq_of_toNat_eq
  have hb := (BitVec.fromLEBytes ((a.val.map (·.bv)).reverse)).isLt
  simp only [List.length_reverse, List.length_map, Std.Array.property] at hb
  simp only [BitVec.fromBEBytes, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by simpa using hb)]
  rfl

theorem load_to_be (u : Std.U128) : loadBytes (core.num.U128.to_be_bytes u).val = reverseBytesQuad32 u.bv := by
  rw [← short.rev_load_be u, reverseBytesQuad32_involutive]

theorem rev_rev (x : BitVec 128) : reverseBytesQuad32 (reverseBytesQuad32 x) = x := reverseBytesQuad32_involutive x

theorem mkfour_zero : mkfour 0 0 0 0 = 0 := rfl

/-! ## The key table -/

theorem zipm_eq (a b : BitVec 128) : zipm a b = karatsubaMid b ++ karatsubaMid a := by
  have h : ∀ x : BitVec 128, lo (swap x ^^^ x) = karatsubaMid x := fun x => by
    rw [lo_xor, swap, lo_append, karatsubaMid, BitVec.xor_comm]; rfl
  rw [zipm, h, h]

/-- The table rind's `PmullTable::new` builds for the key `h` is the one the
kernels' theorems name. -/
theorem htable8_eq (h : BitVec 128) (t : low.aarch64.ghash.PmullTable) (ht : TableFor (toPoly h) t) :
    t.htable.val = htable8 (ghashTwist h) := by
  obtain ⟨p, hp, hv⟩ := ht
  have e : ∀ i < 8, hPower (ghashTwist h) i = p[i]! := fun i hi =>
    toPoly_inj (by rw [toPoly_hPower, hp i hi])
  rw [hv, htable8, htable4, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
    e 5 (by omega), e 6 (by omega), e 7 (by omega), htableOf]
  simp only [zipm_eq, List.cons_append, List.nil_append]
  rfl

/-! ## `stitched` -/

/-- What `stitched` ensures, as Vale states GCTR and GHASH: each output block
the input block XORed with the keystream of the counter block `j` advanced
`i`, the counter block advanced past the blocks, and the hash `x` advanced
over the ciphertext's blocks, the output's sealing and the input's opening,
under the key `H`. -/
def StitchedPost (ENC : Bool) (alg : Algorithm) (kw : List (BitVec 32)) (H : P) (x j : BitVec 128)
    (blocks : Slice (Std.Array U8 16#usize))
    (r : Std.Array U8 16#usize × Std.Array U8 16#usize × Slice (Std.Array U8 16#usize)) : Prop :=
  r.2.2.length = blocks.length ∧
  (∀ i < blocks.length, loadBytes r.2.2.val[i]!.val =
    loadBytes blocks.val[i]!.val ^^^ aesEncrypt alg kw (reverseBytesQuad32 (inc32 j i))) ∧
  loadBytes r.2.1.val = reverseBytesQuad32 (inc32 j blocks.length) ∧
  toPoly (reverseBytesQuad32 (loadBytes r.1.val)) = ghashPoly H (toPoly x)
    ((List.range blocks.length).map fun i => polyLE (loadBytes (if ENC then r.2.2 else blocks).val[i]!.val))

/-- The cipher of zero under the kernels' round keys, rind's keys reversed, is
the hash key, bytes reversed. -/
theorem cipher_zero (enc : BitVec 128 → List (BitVec 128) → BitVec 128) (alg : Algorithm)
    (kw : List (BitVec 32)) (keys : List (BitVec 128)) (hkeys : keys = keyToRoundKeys alg kw)
    (henc : ∀ x rk, reverseBytesQuad32 (enc x rk) = evalCipher alg (reverseBytesQuad32 x) (rk.map reverseBytesQuad32)) :
    enc 0#128 (keys.map reverseBytesQuad32) = reverseBytesQuad32 (aesEncrypt alg kw (mkfour 0 0 0 0)) := by
  have hrk : (keys.map reverseBytesQuad32).map reverseBytesQuad32 = keyToRoundKeys alg kw := by
    rw [List.map_map, ← hkeys]; simp [Function.comp_def, rev_rev]
  have hz : reverseBytesQuad32 0#128 = 0 := rev_zero
  rw [← rev_rev (enc _ _), henc, hrk, hz, mkfour_zero, aesEncrypt]

/-- One kernel's theorem, as `StitchedPost`. -/
theorem kernel_post (ENC : Bool) (enc : BitVec 128 → List (BitVec 128) → BitVec 128) (alg : Algorithm)
    (kw : List (BitVec 32)) (keys : List (BitVec 128)) (hkeys : keys = keyToRoundKeys alg kw)
    (henc : ∀ x rk, reverseBytesQuad32 (enc x rk) = evalCipher alg (reverseBytesQuad32 x) (rk.map reverseBytesQuad32))
    (x j : BitVec 128) (blocks : Slice (Std.Array U8 16#usize)) (r : low.aarch64.aes_gcm.KernelOut)
    (hashed : Nat → BitVec 128)
    (hhashed : hashed = if ENC then nistCipherBlock enc (j.extractLsb' 0 32).toNat (j.extractLsb' 32 96)
        (keys.map reverseBytesQuad32) (fun i => loadBytes blocks.val[i]!.val)
      else nistInputBlock (fun i => loadBytes blocks.val[i]!.val))
    (hr : GcmKernelOut enc hashed blocks.length x (j.extractLsb' 32 96) (j.extractLsb' 0 32).toNat
      (keys.map reverseBytesQuad32) (fun i => loadBytes blocks.val[i]!.val) r) :
    StitchedPost ENC alg kw (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) x j blocks (r.2.1, r.2.2, r.1) := by
  obtain ⟨hl, hout, htag, hctr⟩ := hr
  have hrk : (keys.map reverseBytesQuad32).map reverseBytesQuad32 = keyToRoundKeys alg kw := by
    rw [List.map_map, ← hkeys]; simp [Function.comp_def, rev_rev]
  have hh : ∀ i < blocks.length,
      hashed i = reverseBytesQuad32 (loadBytes (if ENC then r.1 else blocks).val[i]!.val) := by
    intro i hi
    subst hhashed
    cases ENC
    · simp only [Bool.false_eq_true, ite_false, nistInputBlock, wordReversefields8]
    · simp only [ite_true, nistCipherBlock, cipherBlock, wordReversefields8, hout i hi]
  refine ⟨hl, fun i hi => ?_, ?_, ?_⟩
  · rw [hout i hi, aesCtrBlock_eq enc alg _ kw (henc · _) hrk j i, BitVec.xor_comm]
  · rw [hctr, wordReversefields8, ← inc32_ctrBlock, ctrBlock_split]
  · rw [htag, wordReversefields8, rev_rev, toPoly_nistGhash, cipher_zero enc alg kw keys hkeys henc, ← polyLE,
      listOfSeq, List.map_map]
    refine congrArg _ (List.map_congr_left fun i hi => ?_)
    rw [List.mem_range] at hi
    simp only [Function.comp_apply, hh i hi, polyLE]

/-- `stitched` with an AES-128 or AES-256 key and a table for its hash key:
s2n-bignum's kernels' theorems, as Vale states GCTR and GHASH. -/
theorem stitched_spec (ENC : Bool) (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (h192 : alg ≠ .AES_192) (t : low.aarch64.ghash.PmullTable)
    (ht : TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t)
    (tag counter : Std.Array U8 16#usize) (x j : BitVec 128) (htag : loadBytes tag.val = reverseBytesQuad32 x)
    (hctr : loadBytes counter.val = reverseBytesQuad32 j) (blocks : Slice (Std.Array U8 16#usize))
    (hn : blocks.length < 2 ^ 57) :
    low.aarch64.aes_gcm.stitched ENC hk t tag counter blocks ⦃ r =>
      StitchedPost ENC alg kw (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) x j blocks r ⦄ := by
  unfold low.aarch64.aes_gcm.stitched
  by_cases h0 : blocks.length = 0
  · simp only [h0, ite_true, WP.spec_ok]
    refine ⟨rfl, fun i hi => by omega, by rw [h0, inc32_zero, hctr], ?_⟩
    rw [h0, List.range_zero, List.map_nil, ghashPoly_nil, htag, rev_rev]
  simp only [h0, ite_false]
  have hin : ∀ keys : List (BitVec 128), GcmKernelIn blocks tag counter keys x (j.extractLsb' 32 96)
      (j.extractLsb' 0 32).toNat (keys.map reverseBytesQuad32) (fun i => loadBytes blocks.val[i]!.val) :=
    fun keys => ⟨by rw [htag, wordReversefields8], by rw [hctr, wordReversefields8, ctrBlock_split],
      by simp [List.map_map, Function.comp_def, wordReversefields8, rev_rev], fun _ _ => rfl⟩
  have htab : ∀ (enc : BitVec 128 → List (BitVec 128) → BitVec 128) (keys : List (BitVec 128)),
      keys = keyToRoundKeys alg kw →
      (∀ x rk, reverseBytesQuad32 (enc x rk) = evalCipher alg (reverseBytesQuad32 x) (rk.map reverseBytesQuad32)) →
      t.htable.val = htable8 (ghashTwist (enc 0#128 (keys.map reverseBytesQuad32))) := by
    intro enc keys hkeys henc
    rw [cipher_zero enc alg kw keys hkeys henc]
    rw [polyLE] at ht
    exact htable8_eq _ t ht
  have htab4 : ∀ (enc : BitVec 128 → List (BitVec 128) → BitVec 128) (keys : List (BitVec 128)),
      keys = keyToRoundKeys alg kw →
      (∀ x rk, reverseBytesQuad32 (enc x rk) = evalCipher alg (reverseBytesQuad32 x) (rk.map reverseBytesQuad32)) →
      (Std.Array.make 6#usize (t.htable.val.take 6) (by simp) : Std.Array V 6#usize).val =
        htable4 (ghashTwist (enc 0#128 (keys.map reverseBytesQuad32))) := by
    intro enc keys hkeys henc
    rw [Std.Array.make_val]
    rw [htab enc keys hkeys henc, htable8, List.take_left' (by rfl)]
  cases hk with
  | Aes192 k => obtain ⟨rfl, -⟩ := hkey; exact absurd rfl h192
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := hkey
    -- By `ENC`, `eight_way`, and the address compare: the `_alt` kernels run
    -- only with both, the four-way ones otherwise.
    cases ENC <;> rcases _he : t.eight_way with _ | s <;> rcases hl : low.aarch64.aes_gcm.KernelBuffersLow blocks <;>
      simp only
    iterate 3
      · apply WP.spec_bind (aes128_gcm_dec_spec blocks tag counter k.round_keys _ x _ _ _ _ hn (hin _)
          (htab4 aes128Cipher _ hrk aes128Cipher_eq))
        intro r hr; rw [WP.spec_ok]
        exact kernel_post false aes128Cipher .AES_128 kw _ hrk aes128Cipher_eq x j blocks r _ rfl hr
    · apply WP.spec_bind (aes128_gcm_dec_alt_spec blocks tag counter k.round_keys _ x _ _ _ _ hn hl (hin _)
        (htab aes128Cipher _ hrk aes128Cipher_eq))
      intro r hr; rw [WP.spec_ok]
      exact kernel_post false aes128Cipher .AES_128 kw _ hrk aes128Cipher_eq x j blocks r _ rfl hr
    iterate 3
      · apply WP.spec_bind (aes128_gcm_enc_spec blocks tag counter k.round_keys _ x _ _ _ _ hn (hin _)
          (htab4 aes128Cipher _ hrk aes128Cipher_eq))
        intro r hr; rw [WP.spec_ok]
        exact kernel_post true aes128Cipher .AES_128 kw _ hrk aes128Cipher_eq x j blocks r _ rfl hr
    · apply WP.spec_bind (aes128_gcm_enc_alt_spec blocks tag counter k.round_keys _ x _ _ _ _ hn hl (hin _)
        (htab aes128Cipher _ hrk aes128Cipher_eq))
      intro r hr; rw [WP.spec_ok]
      exact kernel_post true aes128Cipher .AES_128 kw _ hrk aes128Cipher_eq x j blocks r _ rfl hr
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := hkey
    -- By `ENC`, `eight_way`, and the address compare: the `_alt` kernels run
    -- only with both, the four-way ones otherwise.
    cases ENC <;> rcases _he : t.eight_way with _ | s <;> rcases hl : low.aarch64.aes_gcm.KernelBuffersLow blocks <;>
      simp only
    iterate 3
      · apply WP.spec_bind (aes256_gcm_dec_spec blocks tag counter k.round_keys _ x _ _ _ _ hn (hin _)
          (htab4 aes256Cipher _ hrk aes256Cipher_eq))
        intro r hr; rw [WP.spec_ok]
        exact kernel_post false aes256Cipher .AES_256 kw _ hrk aes256Cipher_eq x j blocks r _ rfl hr
    · apply WP.spec_bind (aes256_gcm_dec_alt_spec blocks tag counter k.round_keys _ x _ _ _ _ hn hl (hin _)
        (htab aes256Cipher _ hrk aes256Cipher_eq))
      intro r hr; rw [WP.spec_ok]
      exact kernel_post false aes256Cipher .AES_256 kw _ hrk aes256Cipher_eq x j blocks r _ rfl hr
    iterate 3
      · apply WP.spec_bind (aes256_gcm_enc_spec blocks tag counter k.round_keys _ x _ _ _ _ hn (hin _)
          (htab4 aes256Cipher _ hrk aes256Cipher_eq))
        intro r hr; rw [WP.spec_ok]
        exact kernel_post true aes256Cipher .AES_256 kw _ hrk aes256Cipher_eq x j blocks r _ rfl hr
    · apply WP.spec_bind (aes256_gcm_enc_alt_spec blocks tag counter k.round_keys _ x _ _ _ _ hn hl (hin _)
        (htab aes256Cipher _ hrk aes256Cipher_eq))
      intro r hr; rw [WP.spec_ok]
      exact kernel_post true aes256Cipher .AES_256 kw _ hrk aes256Cipher_eq x j blocks r _ rfl hr


/-! ## `partial` -/

theorem partial_loop_spec (ks : Std.Array U8 16#usize) (rem : Slice U8) (hr : rem.length ≤ 16) :
    low.aarch64.aes_gcm.partial_loop { start := 0#usize, «end» := Slice.len rem } rem ks ⦃ r =>
      r.length = rem.length ∧ ∀ k < rem.length, r.val[k]! = rem.val[k]! ^^^ ks.val[k]! ⦄ := by
  unfold low.aarch64.aes_gcm.partial_loop
  apply range_loop _ (Slice.len rem) (fun j (s : Slice U8) => s.length = rem.length ∧
    ∀ k < rem.length, s.val[k]! = if k < j then rem.val[k]! ^^^ ks.val[k]! else rem.val[k]!)
  · rintro it s0 he hlt ⟨hl, hP⟩
    have hlt' : it.start.val < rem.length := by simpa using hlt
    unfold low.aarch64.aes_gcm.partial_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
    subst ho
    step*
    refine ⟨it', s, rfl, hst, by rw [hen, he], by rw [s_post]; simp [hl], fun k hk => ?_⟩
    have hi3 : i3 = i2 ^^^ i1 := UScalar.eq_of_val_eq i3_post
    have hsl : it.start.val < s0.val.length := by rw [← Slice.length, hl]; exact hlt'
    rw [s_post, Slice.set_val_eq, getElem!_set _ _ _ hsl]
    by_cases hkj : it.start.val = k
    · subst hkj
      rw [ite_eq_left rfl, ite_eq_left (by omega), hi3, i2_post, i1_post, ← getElem!_pos s0.val _ hsl,
        ← getElem!_pos ks.val _ (by simp; omega), hP _ hk, ite_eq_right (by omega)]
    · rw [ite_eq_right hkj, hP k hk]
      by_cases hkl : k < it.start.val
      · rw [ite_eq_left hkl, ite_eq_left (by omega)]
      · rw [ite_eq_right hkl, ite_eq_right (by omega)]
  · rintro it s he hst ⟨hl, hP⟩
    unfold low.aarch64.aes_gcm.partial_loop.body
    step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
    subst ho
    simp only [WP.spec_ok]
    refine ⟨s, rfl, hl, fun k hk => ?_⟩
    have : it.start.val = rem.length := by simpa using hst
    rw [hP k hk, ite_eq_left (by omega)]
  · rfl
  · simp
  · exact ⟨rfl, fun k hk => by simp⟩

theorem ext_getElem! {α : Type} [Inhabited α] {l1 l2 : List α} (hl : l1.length = l2.length)
    (h : ∀ k < l1.length, l1[k]! = l2[k]!) : l1 = l2 :=
  List.ext_getElem hl fun k h1 h2 => by rw [← getElem!_pos l1 k h1, ← getElem!_pos l2 k h2]; exact h k h1

theorem store_load (a : Std.Array U8 16#usize) : (storeBytes (loadBytes a.val)).val = a.val := by
  rw [short.storeBytes_val, loadBytes, short.leQuad32ToBytes_leBytesToQuad32 _ (by simp), List.map_map]
  exact List.map_id _

/-- A byte of fewer than 16, XORed in a vector, is the byte XORed. -/
theorem store_xor_getElem! (c : List U8) (E : BitVec 128) {k : Nat} (hk : k < c.length) (hc : c.length ≤ 16) :
    (storeBytes (loadBytes c ^^^ E)).val[k]! = c[k]! ^^^ (storeBytes E).val[k]! := by
  rw [UScalar.eq_equiv_bv_eq, UScalar.bv_xor]
  have h1 := short.storeBytes_getElem! (loadBytes c ^^^ E) (show k < 16 by omega)
  have h2 := short.storeBytes_getElem! E (show k < 16 by omega)
  have h3 : byte (loadBytes c) k = c[k]!.bv := by
    rw [loadBytes, byte_leBytesToQuad32 _ (by omega)]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact h1.trans ((byte_xor _ _ _).trans (congrArg₂ (· ^^^ ·) h3 h2.symm))

/-- `partial` with the crypto extension's key and a PMULL table for `H`:
fewer than 16 bytes XORed with the keystream of counter `inc32 j0 i`, as
`short` would, and GHASH of the ciphertext. -/
theorem partial_spec (ENC : Bool) (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (H : P) (hH : Small H) (t : low.aarch64.ghash.PmullTable) (ht : TableFor H t)
    (y : V) (j0 : Quad32) (i : Nat) (counter : Std.Array U8 16#usize)
    (hctr : loadBytes counter.val = reverseBytesQuad32 (inc32 j0 i)) (rem : Slice U8) (hr : rem.length < 16) :
    low.aarch64.aes_gcm.partial ENC (.Hw hk) ⟨.Pmull t, y⟩ counter rem ⦃ r =>
      r.1.table = .Pmull t ∧ r.2.val = short.chunkOut alg kw j0 rem.val i ∧
      toPoly r.1.current = ghashPoly H (toPoly y) ((padBlocks (if ENC then r.2.val else rem.val)).map toPoly) ⦄ := by
  have hout : ∀ r : Slice U8, (r.length = rem.length ∧ ∀ k < rem.length,
      r.val[k]! = rem.val[k]! ^^^ (storeBytes (aesEncrypt alg kw (loadBytes counter.val))).val[k]!) →
      r.val = short.chunkOut alg kw j0 rem.val i := by
    rintro r ⟨hl, hk⟩
    apply ext_getElem! (by rw [short.length_chunkOut _ _ _ _ _ (by simp [Slice.length] at hr ⊢; omega)]; exact hl)
    intro k hkr
    have hkr' : k < rem.length := by rw [← hl]; exact hkr
    have htk : ∀ (l : List U8) (n : Nat), k < n → (l.take n)[k]! = l[k]! := fun l n h => by
      simp [List.getElem!_eq_getElem?_getD, h]
    rw [hk k hkr', short.chunkOut, htk _ _ hkr', store_xor_getElem! _ _ hkr' (by simp [Slice.length] at hr; omega),
      hctr]
  unfold low.aarch64.aes_gcm.partial
  by_cases h0 : rem.length = 0
  · have hn : rem.val = [] := List.eq_nil_of_length_eq_zero h0
    simp only [core.slice.Slice.is_empty, h0, decide_true, ite_true, bind_ok]
    rw [WP.spec_ok]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hn, short.chunkOut]; rfl
    · cases ENC <;> simp [hn, padBlocks_nil, ghashPoly]
  · simp only [core.slice.Slice.is_empty, h0, decide_false, hw_encrypt_block hk alg kw hkey]
    cases ENC
    · obtain ⟨y1, hy1, hp1⟩ := pmull.ghash_add_spec H hH t ht y rem
      simp only [Bool.false_eq_true, ite_false, hy1, bind_ok]
      apply WP.spec_bind (partial_loop_spec _ rem (by omega))
      intro r hr'
      rw [WP.spec_ok]
      exact ⟨rfl, hout r hr', hp1⟩
    · simp only [ite_true, bind_ok]
      apply WP.spec_bind (partial_loop_spec _ rem (by omega))
      intro r hr'
      obtain ⟨y1, hy1, hp1⟩ := pmull.ghash_add_spec H hH t ht y r
      rw [hy1, bind_ok, WP.spec_ok]
      exact ⟨rfl, hout r hr', hp1⟩

/-! ## `inc32` -/

/-- `inc32`: Vale's `inc32` by one, in memory order. -/
theorem inc32_spec (j : Quad32) (y : Std.Array U8 16#usize) (hy : loadBytes y.val = reverseBytesQuad32 j) :
    low.aarch64.aes_gcm.inc32 y ⦃ r => loadBytes r.val = reverseBytesQuad32 (inc32 j 1) ⦄ := by
  unfold low.aarch64.aes_gcm.inc32
  simp only [lift, bind_ok, WP.spec_ok]
  rw [load_to_be]
  refine congrArg reverseBytesQuad32 ?_
  have hb : (core.num.U128.from_be_bytes y).bv = j := by rw [from_be_eq, hy, rev_rev]
  generalize core.num.U128.from_be_bytes y = b at hb ⊢
  have h1 : (4294967295#u128).bv = 0xffffffff#128 := rfl
  have h2 : (1#u32).bv = 1#32 := rfl
  simp only [UScalar.bv_or, UScalar.bv_and, UScalar.bv_not, UScalar.cast_bv_eq, core.num.U32.wrapping_add_bv_eq,
    hb, h1, h2, inc32, UScalarTy.numBits]
  clear hy hb
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : (0xffffffff#128 : BitVec 128).getLsbD i = decide (i < 32) := by
    rw [BitVec.getLsbD_ofNat, show (0xffffffff : Nat) = 2 ^ 32 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [hi]
  have hlo : j.setWidth 32 = j.extractLsb' 0 32 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hm, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hlo, hi]
  by_cases h : i < 32
  · simp [h]
  · simp [h, show i - 32 < 96 by omega, show 32 + (i - 32) = i by omega,
      BitVec.getLsbD_of_ge (BitVec.extractLsb' 0 32 j + 1#32) i (by omega)]

/-! ## `cipher` -/

theorem range_map_getElem! {α β : Type} [Inhabited α] (l : List α) (f : α → β) :
    (List.range l.length).map (fun i => f l[i]!) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [getElem!_pos l i (by simpa using h1)]

theorem loopOuts_eq (alg : Algorithm) (kw : List (BitVec 32)) (j0 : Quad32) : ∀ (C : List (List U8)) (i : Nat),
    short.loopOuts alg kw j0 C i = (List.range C.length).map fun k => short.chunkOut alg kw j0 C[k]! (i + k)
  | [], _ => rfl
  | c :: C, i => by
    rw [short.loopOuts, loopOuts_eq alg kw j0 C (i + 1), List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    refine congrArg₂ List.cons (by rw [List.getElem!_cons_zero, Nat.add_zero]) (List.map_congr_left fun k _ => ?_)
    simp only [Function.comp_apply, Nat.succ_eq_add_one, List.getElem!_cons_succ]
    rw [show i + 1 + k = i + (k + 1) by omega]

/-- GHASH's blocks of whole blocks, then fewer than 16 bytes. -/
theorem padBlocks_blocks (L : List (List U8)) (R : List U8) (hL : ∀ c ∈ L, c.length = 16) (hR : R.length < 16) :
    padBlocks (L.flatten ++ R) = L.map blockBE ++ padBlocks R := by
  have h0 := short.chunksUpTo_flatten ([] : List (List U8)) R (by simp) hR
  rw [List.flatten_nil, List.nil_append, List.nil_append] at h0
  rw [← short.padBlocks_chunks (L.flatten ++ R), short.chunksUpTo_flatten L R hL hR, ← short.padBlocks_chunks R, h0,
    List.map_append]

/-- The kernels' blocks are `short`'s loop outputs from counter 1. -/
theorem blocks_out (alg : Algorithm) (kw : List (BitVec 32)) (j0 : Quad32) (W W' : List (Std.Array U8 16#usize))
    (hl : W'.length = W.length)
    (h : ∀ i < W.length, loadBytes W'[i]!.val =
      loadBytes W[i]!.val ^^^ aesEncrypt alg kw (reverseBytesQuad32 (inc32 (inc32 j0 1) i))) :
    W'.map (·.val) = short.loopOuts alg kw j0 (W.map (·.val)) 1 := by
  rw [loopOuts_eq, List.length_map]
  apply List.ext_getElem (by simp [hl])
  intro k h1 h2
  have hk : k < W.length := by simpa using h2
  simp only [List.getElem_map, List.getElem_range]
  rw [getElem!_pos (W.map (·.val)) k (by simpa using hk), List.getElem_map, short.chunkOut, ← getElem!_pos W k hk,
    ← getElem!_pos W' k (by omega), ← inc32_inc32, ← h k hk, store_load, List.take_of_length_le (by simp)]

/-- `cipher` with a key on the crypto extension and a PMULL table for its
hash key, AES-192 only without `eight_way`: GCTR from the block after `j0`, and GHASH
from `x` over the AAD's blocks, then the ciphertext's. -/
theorem cipher_spec (ENC : Bool) (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (t : low.aarch64.ghash.PmullTable)
    (ht : TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t)
    (h192 : t.eight_way.isSome → alg ≠ .AES_192) (x : V) (j0 : Quad32)
    (y0 : Std.Array U8 16#usize) (hy : loadBytes y0.val = reverseBytesQuad32 j0) (aad inout : Slice U8)
    (hin : inout.length < 2 ^ 61) :
    low.aarch64.aes_gcm.cipher ENC (.Hw hk) ⟨.Pmull t, x⟩ y0 aad inout ⦃ r =>
      r.1.table = .Pmull t ∧ r.2.length = inout.length ∧
      bvs r.2.val = gctrEncrypt (inc32 j0 1) (bvs inout.val) alg kw ∧
      toPoly r.1.current = ghashPoly (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) (toPoly x)
        ((padBlocks aad.val ++ padBlocks (if ENC then r.2.val else inout.val)).map toPoly) ⦄ := by
  set H := polyLE (aesEncrypt alg kw (mkfour 0 0 0 0)) with hH
  obtain ⟨x1, hx1, hp1⟩ := pmull.ghash_add_spec H (small_toPoly _) t ht x aad
  unfold low.aarch64.aes_gcm.cipher
  rw [hx1, bind_ok]
  apply WP.spec_bind (inc32_spec j0 y0 hy)
  intro c1 hc1
  rcases hk with k | k | k
  rotate_left
  · cases hew : t.eight_way with
    | some _ => exact absurd hkey.1 (h192 (by rw [hew]; rfl))
    | none =>
      simp only [hew]
      apply WP.spec_mono (composed.composed_spec ENC _ alg kw hkey H (small_toPoly _) t ht x1 (inc32 j0 1) c1 hc1
        inout)
      rintro ⟨g, out⟩ ⟨hgt, hl, hout, hg⟩
      refine ⟨hgt, hl, hout, ?_⟩
      rw [hg, hp1, ← ghashPoly_append, List.map_append]
  all_goals
    have h192 : alg ≠ .AES_192 := by rw [hkey.1]; decide
    simp only
    step with as_chunks_mut_spec 16#usize inout (by decide) as ⟨W, R, back, hWl, hWi, hR, hback⟩
    simp only [low.aarch64.ghash.Ghash.state, low.aarch64.ghash.to_u128, bind_ok]
    have hn : W.length < 2 ^ 57 := by
      simp only [Slice.length] at hin hWl ⊢; omega
    apply WP.spec_bind (stitched_spec ENC _ alg kw hkey h192 t ht _ c1 x1 (inc32 j0 1) (load_to_be _) hc1 W hn)
    rintro ⟨tag1, c2, W'⟩ ⟨hWl2, hW', hc2, hg2⟩
    dsimp only at hWl2 hW' hc2 hg2
    simp only [low.aarch64.ghash.Ghash.set_state, lift, low.aarch64.ghash.from_u128, bind_ok]
    have hRl : R.length < 16 := by
      have := congrArg List.length hR
      rw [List.length_drop] at this
      simp only [Slice.length] at this ⊢; omega
    apply WP.spec_bind (partial_spec ENC _ alg kw hkey H (small_toPoly _) t ht _ j0 (1 + W.length) c2
      (by rw [hc2, inc32_inc32]) R hRl)
    rintro ⟨g3, R'⟩ ⟨hg3t, hR', hg3⟩
    simp only [uncurry_apply_pair, WP.spec_ok]
    -- The input and the output, as whole blocks and the rest.
    have hL16 : ∀ (Vs : List (Std.Array U8 16#usize)), ∀ c ∈ Vs.map (·.val), c.length = 16 := by
      intro Vs c hc; obtain ⟨a, -, rfl⟩ := List.mem_map.1 hc; simp
    have hinv : inout.val = (W.val.map (·.val)).flatten ++ R.val := by
      have e16 : (16#usize : Usize).val = 16 := rfl
      rw [← List.flatMap_def, flatMap_chunks W.val inout.val hWi, hR, hWl, e16, List.take_append_drop]
    have hRl' : R'.val.length = R.val.length := by
      rw [hR', short.length_chunkOut _ _ _ _ _ (by simp only [Slice.length] at hRl; omega)]
    have hbl : (W'.val.flatMap (·.val) ++ R'.val).length ≤ Usize.max := by
      rw [List.length_append, length_flatMap_val, hRl']
      have h1 := inout.property
      have h2 := congrArg List.length hinv
      rw [List.length_append, ← List.flatMap_def, length_flatMap_val] at h2
      have e16 : (16#usize : Usize).val = 16 := rfl
      simp only [Slice.length, e16] at hWl2 h2 h1 ⊢
      omega
    have hout : (back (W', R')).val = (W'.val.map (·.val)).flatten ++ R'.val := by
      rw [hback W' R' hbl, List.flatMap_def]
    have hloop : (back (W', R')).val = (short.loopOuts alg kw j0 (chunksUpTo 16 inout.val) 1).flatten := by
      rw [hout, hinv, short.chunksUpTo_flatten _ _ (hL16 W) (by simpa using hRl), short.loopOuts_append,
        List.flatten_append, blocks_out alg kw j0 W.val W'.val hWl2 (fun i hi => by
          rw [hW' i hi]), List.length_map, hR']
      by_cases h0 : R.val = []
      · rw [ite_eq_left h0, h0]; rfl
      · rw [ite_eq_right h0]
        simp [short.loopOuts]
    have hbvs : bvs (back (W', R')).val = gctrEncrypt (inc32 j0 1) (bvs inout.val) alg kw := by
      rw [bvs, hloop, short.loop_gctr]
    refine ⟨hg3t, ?_, hbvs, ?_⟩
    · have := congrArg List.length hbvs
      simpa [bvs, length_gctrEncrypt] using this
    · rw [hg3, from_be_eq, hg2, hp1, ← ghashPoly_append]
      have hrange : ∀ (Vs : Slice (Std.Array U8 16#usize)), Vs.length = W.length →
          (List.range W.length).map (fun i => polyLE (loadBytes Vs.val[i]!.val)) =
            ((Vs.val.map (·.val)).map blockBE).map toPoly := by
        intro Vs hV
        rw [← hV, Slice.length, range_map_getElem! Vs.val (fun a => polyLE (loadBytes a.val))]
        simp [polyLE, blockBE, Function.comp_def]
      cases ENC
      · simp only [Bool.false_eq_true, ite_false]
        rw [hrange W rfl, hinv, padBlocks_blocks _ _ (hL16 W) (by simpa using hRl), List.map_append,
          List.map_append, ghashPoly_append H (toPoly x)]
      · simp only [ite_true]
        rw [hrange W' hWl2, hout, padBlocks_blocks _ _ (hL16 W') (by rw [hRl']; simpa using hRl), List.map_append,
          List.map_append, ghashPoly_append H (toPoly x)]

/-! ## `tagged_from` and `tagged` -/

theorem bvs_load (a : Std.Array U8 16#usize) : bvs a.val = leQuad32ToBytes (loadBytes a.val) := by
  rw [loadBytes, short.leQuad32ToBytes_leBytesToQuad32 _ (by simp)]

/-- The tag `tagged_from` assembles: the mask XORed with the GHASH state, both
big-endian. -/
theorem tag_load (m : Std.Array U8 16#usize) (y : V) :
    loadBytes (core.num.U128.to_be_bytes (core.num.U128.from_be_bytes m ^^^
      core.num.U128.from_be_bytes (core.num.U128.to_be_bytes ⟨y⟩))).val = loadBytes m.val ^^^ reverseBytesQuad32 y := by
  have h : (core.num.U128.from_be_bytes m ^^^ core.num.U128.from_be_bytes (core.num.U128.to_be_bytes ⟨y⟩)).bv =
      (reverseBytesQuad32 (loadBytes m.val) ^^^ y : BitVec 128) := by
    simp only [UScalar.bv_xor, from_be_eq, load_to_be, rev_rev]
  refine (load_to_be _).trans ((congrArg reverseBytesQuad32 h).trans ?_)
  rw [rev_xor, rev_rev]

/-- `tagged_from` with a key on the crypto extension and a PMULL table,
AES-192 only without `eight_way`, at any length: GCTR from the block after `j0`, and the tag
GCTR from `j0` on `gcm_hash` of the AAD and the ciphertext. -/
theorem tagged_from_spec (ENC : Bool) (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (t : low.aarch64.ghash.PmullTable)
    (ht : TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t)
    (h192 : t.eight_way.isSome → alg ≠ .AES_192) (j0 : Quad32)
    (y0 : Std.Array U8 16#usize)
    (hy : loadBytes y0.val = reverseBytesQuad32 j0) (aad inout : Slice U8) (hin : inout.length < 2 ^ 61) :
    low.aarch64.aes_gcm.tagged_from ENC (.Hw hk) (.Pmull t) y0 aad inout ⦃ r =>
      r.2.length = inout.length ∧
      bvs r.2.val = gctrEncrypt (inc32 j0 1) (bvs inout.val) alg kw ∧
      bvs r.1.val = gctrEncrypt j0 (leQuad32ToBytes (gcmHash (aesEncrypt alg kw (mkfour 0 0 0 0)) (bvs aad.val)
        (bvs (if ENC then r.2.val else inout.val)))) alg kw ⦄ := by
  by_cases hshort : (aad.length + 15) / 16 + (inout.length + 15) / 16 ≤ if ENC then 15 else 31
  · exact tagged_from_short_spec ENC hk alg kw hkey t ht j0 y0 hy aad inout hshort
  set hLE := aesEncrypt alg kw (mkfour 0 0 0 0) with hhLE
  have h16 : ¬ (16#usize : Usize).val = 0 := by decide
  have hsb : (if ENC then ok low.aarch64.aes_gcm.SHORT_SEAL_BLOCKS else ok low.aarch64.aes_gcm.SHORT_OPEN_BLOCKS) =
      (ok (if ENC then low.aarch64.aes_gcm.SHORT_SEAL_BLOCKS else low.aarch64.aes_gcm.SHORT_OPEN_BLOCKS) :
        Result Usize) := by
    cases ENC <;> rfl
  unfold low.aarch64.aes_gcm.tagged_from
  simp only [hsb, bind_ok, core.num.Usize.div_ceil, h16, _root_.dite_false]
  step as ⟨i4, hi4⟩
  simp only [Slice.len_val] at hi4
  rw [ite_eq_right (by
    cases ENC <;> simp only [Bool.false_eq_true, ite_false, ite_true, low.aarch64.aes_gcm.SHORT_SEAL_BLOCKS,
      low.aarch64.aes_gcm.SHORT_OPEN_BLOCKS] at hshort ⊢ <;> scalar_tac)]
  simp only [low.aarch64.ghash.Ghash.new, pmull.zero_eq, bind_ok]
  apply WP.spec_bind (cipher_spec ENC hk alg kw hkey t ht h192 0 j0 y0 hy aad inout hin)
  rintro ⟨⟨gt, gc⟩, out⟩ ⟨hgt, hl, hout, hgh⟩
  dsimp only at hgt hl hout hgh ⊢
  subst hgt
  have hl' : (Slice.len out).val < 2 ^ 61 := by rw [Slice.len_val, hl]; exact hin
  apply WP.spec_bind (lengths_spec (Slice.len aad) (Slice.len out) hl')
  intro lb hlb
  obtain ⟨y', hy', hyp'⟩ := pmull.ghash_add_spec (polyLE hLE) (small_toPoly _) t ht gc lb.to_slice
  simp only [lift, bind_ok, hy', hw_encrypt_block hk alg kw hkey, low.aarch64.ghash.Ghash.into_bytes,
    low.aarch64.ghash.Ghash.state, low.aarch64.ghash.to_u128, WP.spec_ok]
  refine ⟨hl, hout, ?_⟩
  have hpb : padBlocks lb.to_slice.val = [blockBE lb.val] := by
    have hl : lb.to_slice.val = lb.val := by simp [Std.Array.to_slice]
    have hr : chunksRest 16 lb.val = [] := List.eq_nil_of_length_eq_zero (by rw [chunksRest_length]; simp)
    rw [hl, padBlocks, chunksOf_self _ (by omega) (by simp), hr]
    rfl
  have hc : (if ENC then out.val else inout.val).length = (Slice.len out).val := by
    rw [Slice.len_val]; cases ENC
    · exact hl.symm
    · rfl
  have hg := gcmHash_eq hLE aad.val (if ENC then out.val else inout.val) y' (by
    rw [hyp', hpb, List.map_singleton, ghashPoly_cons, ghashPoly_nil, blockBE, hlb, hgh, toPoly_zero, Slice.len_val,
      hc])
  rw [gctr_block, ← hg, ← hy, bvs_load, tag_load, load_store, BitVec.xor_comm]

/-- `tagged` sealing with a 96-bit nonce, a key on the crypto extension, and a
PMULL table, AES-192 only without `eight_way`, is Vale's `gcm_encrypt_LE`. -/
theorem tagged_seal_spec (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (t : low.aarch64.ghash.PmullTable)
    (ht : TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t)
    (h192 : t.eight_way.isSome → alg ≠ .AES_192)
    (nonce : Std.Array U8 12#usize)
    (aad inout : Slice U8) (hin : inout.length < 2 ^ 61) :
    low.aarch64.aes_gcm.tagged true (.Hw hk) (.Pmull t) nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧ (bvs r.2.val, bvs r.1.val) =
        gcmEncrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val) ⦄ := by
  unfold low.aarch64.aes_gcm.tagged
  apply WP.spec_bind (counter_block_eq (aesEncrypt alg kw (mkfour 0 0 0 0)) nonce)
  intro y0 hy
  apply WP.spec_mono (tagged_from_spec true hk alg kw hkey t ht h192 _ y0 hy aad inout hin)
  rintro r ⟨hl, ho, htag⟩
  refine ⟨hl, ?_⟩
  simp only [ite_true] at htag
  simp only [gcmEncrypt, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE]
  rw [← ho, ← htag]

/-- `tagged` opening with a 96-bit nonce, a key on the crypto extension, and a
PMULL table, AES-192 only without `eight_way`, is Vale's `gcm_decrypt_LE`,
its tag the one `open` compares. -/
theorem tagged_open_spec (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (t : low.aarch64.ghash.PmullTable)
    (ht : TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t)
    (h192 : t.eight_way.isSome → alg ≠ .AES_192)
    (nonce : Std.Array U8 12#usize)
    (aad inout : Slice U8) (hin : inout.length < 2 ^ 61) :
    low.aarch64.aes_gcm.tagged false (.Hw hk) (.Pmull t) nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧ ∀ tag : List (BitVec 8),
        gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val) tag =
          (bvs r.2.val, bvs r.1.val == tag) ⦄ := by
  unfold low.aarch64.aes_gcm.tagged
  apply WP.spec_bind (counter_block_eq (aesEncrypt alg kw (mkfour 0 0 0 0)) nonce)
  intro y0 hy
  apply WP.spec_mono (tagged_from_spec false hk alg kw hkey t ht h192 _ y0 hy aad inout hin)
  rintro r ⟨hl, ho, htag⟩
  refine ⟨hl, fun tag => ?_⟩
  simp only [Bool.false_eq_true, ite_false] at htag
  simp only [gcmDecrypt, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE]
  rw [← ho, ← htag]

end rind.aarch64.long
