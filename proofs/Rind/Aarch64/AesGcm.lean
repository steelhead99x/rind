import Rind.Aarch64.AesGcmShort
import Rind.Aarch64.AesKey
open Aeneas Aeneas.Std Result rind.vale rind.simd Polynomial

/-!
# rind's AES-GCM on aarch64 with the crypto extension, short messages

`low::aarch64::aes_gcm` with a crypto-extension key and a PMULL table: the
counter block of a 96-bit nonce and of any other IV under 2^61 bytes is Vale's
`compute_iv_BE`, and `tagged_from`, which takes `short` when the AAD's and
the message's blocks, each rounded up, number at most 15 sealing or 31
opening, is Vale's GCTR and `gcm_hash` from the counter block it is given,
so `tagged` with a 96-bit nonce is `gcm_encrypt_LE` and `gcm_decrypt_LE`.
Longer messages, which run `cipher`'s s2n-bignum kernels or, for AES-192,
aws-lc's stitched kernels or rind's AES-CTR and GHASH in turn, are not yet
covered here.
-/

namespace rind.aarch64

theorem counter_block_val (nonce : Std.Array U8 12#usize) :
    low.aarch64.aes_gcm.counter_block nonce ⦃ y0 => y0.val = nonce.val ++ [0#u8, 0#u8, 0#u8, 1#u8] ⦄ := by
  unfold low.aarch64.aes_gcm.counter_block
  step*
  subst_vars
  simp [s_post2, List.setSlice!]

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

/-- `counter_block` is Vale's counter block for a 96-bit IV, in memory order. -/
theorem counter_block_eq (hLE : Quad32) (nonce : Std.Array U8 12#usize) :
    low.aarch64.aes_gcm.counter_block nonce ⦃ y0 =>
      loadBytes y0.val = reverseBytesQuad32 (computeIvBE hLE (bvs nonce.val)) ⦄ := by
  apply WP.spec_mono (counter_block_val nonce)
  intro y0 hy
  rw [hy]
  exact load_counter hLE nonce.val (by simp)

/-- `tagged_from` on a message short enough for `short`, with the
crypto extension's key and a PMULL table: GCTR from the block after `j0`, and
the tag GCTR from `j0` on `gcm_hash` of the AAD and the ciphertext. -/
theorem tagged_from_short_spec (ENC : Bool) (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (t : low.aarch64.ghash.PmullTable)
    (ht : pmull.TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t) (j0 : Quad32) (y0 : Std.Array U8 16#usize)
    (hy : loadBytes y0.val = reverseBytesQuad32 j0) (aad inout : Slice U8)
    (hshort : (aad.length + 15) / 16 + (inout.length + 15) / 16 ≤ if ENC then 15 else 31) :
    low.aarch64.aes_gcm.tagged_from ENC (.Hw hk) (.Pmull t) y0 aad inout ⦃ r =>
      r.2.length = inout.length ∧
      bvs r.2.val = gctrEncrypt (inc32 j0 1) (bvs inout.val) alg kw ∧
      bvs r.1.val = gctrEncrypt j0 (leQuad32ToBytes (gcmHash (aesEncrypt alg kw (mkfour 0 0 0 0)) (bvs aad.val)
        (bvs (if ENC then r.2.val else inout.val)))) alg kw ⦄ := by
  have hS : ∀ {N : Usize} (rk : Std.Array (BitVec 128) N), rk.val = keyToRoundKeys alg kw → N.val = nr alg + 1 →
      low.aarch64.aes_gcm.short ENC rk t y0 aad inout ⦃ r =>
        r.2.length = inout.length ∧
        bvs r.2.val = gctrEncrypt (inc32 j0 1) (bvs inout.val) alg kw ∧
        bvs r.1.val = gctrEncrypt j0 (leQuad32ToBytes (gcmHash (aesEncrypt alg kw (mkfour 0 0 0 0)) (bvs aad.val)
          (bvs (if ENC then r.2.val else inout.val)))) alg kw ⦄ := by
    intro N rk hrk hN
    obtain ⟨tag, out, h, hl, ho, htag⟩ := short.short_spec ENC alg kw rk hrk hN t ht j0 y0 hy aad inout hshort
    rw [h, WP.spec_ok]; exact ⟨hl, ho, htag⟩
  have h16 : ¬ (16#usize : Usize).val = 0 := by decide
  unfold low.aarch64.aes_gcm.tagged_from
  cases ENC <;> simp only [Bool.false_eq_true, ite_false, ite_true, bind_ok, core.num.Usize.div_ceil, h16,
    _root_.dite_false] at hshort hS ⊢
  all_goals
    step as ⟨i4, hi4⟩
    simp only [Slice.len_val] at hi4
    rw [ite_eq_left (by simp only [low.aarch64.aes_gcm.SHORT_SEAL_BLOCKS, low.aarch64.aes_gcm.SHORT_OPEN_BLOCKS]; scalar_tac)]
    cases hk <;> obtain ⟨rfl, hrk⟩ := hkey <;>
      simp only [low.aarch64.aes.AesKey128.impl.round_keys, low.aarch64.aes.AesKey192.impl.round_keys,
        low.aarch64.aes.AesKey256.impl.round_keys, bind_ok] <;>
      exact hS _ hrk rfl

/-! ## `tagged` -/

/-- `tagged` sealing a short message with a 96-bit nonce is Vale's
`gcm_encrypt_LE`. -/
theorem tagged_seal_short_spec (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (t : low.aarch64.ghash.PmullTable)
    (ht : pmull.TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t) (nonce : Std.Array U8 12#usize)
    (aad inout : Slice U8) (hshort : (aad.length + 15) / 16 + (inout.length + 15) / 16 ≤ 15) :
    low.aarch64.aes_gcm.tagged true (.Hw hk) (.Pmull t) nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧ (bvs r.2.val, bvs r.1.val) =
        gcmEncrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val) ⦄ := by
  unfold low.aarch64.aes_gcm.tagged
  apply WP.spec_bind (counter_block_eq (aesEncrypt alg kw (mkfour 0 0 0 0)) nonce)
  intro y0 hy
  apply WP.spec_mono (tagged_from_short_spec true hk alg kw hkey t ht _ y0 hy aad inout hshort)
  rintro r ⟨hl, ho, htag⟩
  refine ⟨hl, ?_⟩
  simp only [ite_true] at htag
  simp only [gcmEncrypt, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE]
  rw [← ho, ← htag]

/-- `tagged` opening a short message with a 96-bit nonce is Vale's
`gcm_decrypt_LE`, its tag the one `open` compares. -/
theorem tagged_open_short_spec (hk : low.aarch64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (hkey : HwKeyIs alg kw hk) (t : low.aarch64.ghash.PmullTable)
    (ht : pmull.TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t) (nonce : Std.Array U8 12#usize)
    (aad inout : Slice U8) (hshort : (aad.length + 15) / 16 + (inout.length + 15) / 16 ≤ 31) :
    low.aarch64.aes_gcm.tagged false (.Hw hk) (.Pmull t) nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧ ∀ tag : List (BitVec 8),
        gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val) tag =
          (bvs r.2.val, bvs r.1.val == tag) ⦄ := by
  unfold low.aarch64.aes_gcm.tagged
  apply WP.spec_bind (counter_block_eq (aesEncrypt alg kw (mkfour 0 0 0 0)) nonce)
  intro y0 hy
  apply WP.spec_mono (tagged_from_short_spec false hk alg kw hkey t ht _ y0 hy aad inout hshort)
  rintro r ⟨hl, ho, htag⟩
  refine ⟨hl, fun tag => ?_⟩
  simp only [Bool.false_eq_true, ite_false] at htag
  simp only [gcmDecrypt, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE]
  rw [← ho, ← htag]

/-! ## The counter block of any IV -/

/-- `try_into` of a slice of length `N` to an array holds the slice's bytes. -/
theorem try_from_len (N : Usize) (s : Slice U8) (h : s.length = N.val) :
    ∃ a : Std.Array U8 N, core.array.TryFromSharedArraySlice.try_from N s = ok (.Ok a) ∧
      a.val = s.val := by
  have hs : s.len = N := by scalar_tac
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dite_eq_left hs]
  refine ⟨_, rfl, ?_⟩
  simp [Std.Array.from_val]

/-- `try_into` of a slice of another length fails. -/
theorem try_from_ne (N : Usize) (s : Slice U8) (h : s.length ≠ N.val) :
    core.array.TryFromSharedArraySlice.try_from N s = ok (.Err ()) := by
  have hs : ¬ s.len = N := by intro he; apply h; rw [← he]; scalar_tac
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dite_eq_right hs]

/-- `lengths` is the model's `lengthsBytes`, which `short` hashes, so a change
to the Rust breaks this. -/
theorem lengths_bytes (a m : Usize) (hm : m.val < 2 ^ 61) :
    low.aarch64.aes_gcm.lengths a m ⦃ r => r.val = low.aarch64.aes_gcm.lengthsBytes a.val m.val ⦄ := by
  unfold low.aarch64.aes_gcm.lengths
  step*
  case hmax =>
    subst i_post
    simp only [UScalar.cast_val_eq, UScalarTy.numBits]
    have ha : a.val < 2 ^ 64 := by
      have := a.hBounds
      rcases System.Platform.numBits_eq with h | h <;>
        simp only [UScalarTy.numBits, h] at this <;> omega
    rw [Nat.mod_eq_of_lt (by omega : a.val < 2 ^ 128)]
    have e8 : (8#u128).val = 8 := rfl
    have em : U128.max = 2 ^ 128 - 1 := by rw [U128.max_eq]; norm_num
    rw [e8, em]; omega
  have h1 : i1.bv = BitVec.ofNat 128 (8 * a.val) := by
    apply BitVec.eq_of_toNat_eq
    subst i_post
    simp only [UScalar.bv_toNat, BitVec.toNat_ofNat, i1_post, UScalar.cast_val_eq]
    scalar_tac
  have h4 : i4.bv = BitVec.ofNat 128 (8 * m.val) := by
    apply BitVec.eq_of_toNat_eq
    subst i3_post
    simp only [UScalar.bv_toNat, BitVec.toNat_ofNat, i4_post, UScalar.cast_val_eq]
    scalar_tac
  have h5 : i5 = ⟨(BitVec.ofNat 128 (a.val * 8) <<< 64) ||| BitVec.ofNat 128 (m.val * 8)⟩ := by
    rw [UScalar.eq_equiv_bv_eq]
    simp only [i5_post1, i2_post1, h1, h4, Nat.mul_comm a.val 8, Nat.mul_comm m.val 8]
  rw [h5, low.aarch64.aes_gcm.lengthsBytes]

/-- `lengths`: the length block, its bytes in memory order. -/
theorem lengths_spec (a m : Usize) (hm : m.val < 2 ^ 61) :
    low.aarch64.aes_gcm.lengths a m ⦃ r =>
      reverseBytesQuad32 (loadBytes r.val) = insertNat64 (insertNat64 (mkfour 0 0 0 0) (8 * a.val) 1) (8 * m.val) 0 ⦄ := by
  apply WP.spec_mono (lengths_bytes a m hm)
  intro r hr
  rw [hr]; exact short.lengthsBytes_load _ _ hm

/-- `initial_counter` on a PMULL table is `compute_iv_BE`'s counter block, in
memory order. -/
theorem initial_counter_spec (hLE : Quad32) (t : low.aarch64.ghash.PmullTable) (ht : pmull.TableFor (polyLE hLE) t)
    (iv : Slice U8) (hiv : iv.length < 2 ^ 61) :
    low.aarch64.aes_gcm.initial_counter (.Pmull t) iv ⦃ y0 =>
      loadBytes y0.val = reverseBytesQuad32 (computeIvBE hLE (bvs iv.val)) ⦄ := by
  unfold low.aarch64.aes_gcm.initial_counter
  by_cases h12 : iv.length = 12
  · obtain ⟨a, ha, hav⟩ := try_from_len 12#usize iv h12
    rw [ha, bind_ok]
    apply WP.spec_mono (counter_block_eq hLE a)
    intro y0 hy
    rw [hy, hav]
  · rw [try_from_ne 12#usize iv h12, bind_ok]
    obtain ⟨y, hy, hyp⟩ := pmull.ghash_add_spec (polyLE hLE) (small_toPoly _) t ht 0 iv
    simp only [low.aarch64.ghash.Ghash.new, pmull.zero_eq, bind_ok, hy]
    apply WP.spec_bind (lengths_spec 0#usize iv.len (by rw [Slice.len_val]; exact hiv))
    intro lb hlb
    obtain ⟨y', hy', hyp'⟩ := pmull.ghash_add_spec (polyLE hLE) (small_toPoly _) t ht y lb.to_slice
    simp only [lift, bind_ok, hy', low.aarch64.ghash.Ghash.into_bytes, low.aarch64.ghash.Ghash.state,
      low.aarch64.ghash.to_u128, WP.spec_ok]
    have hpb : padBlocks lb.to_slice.val = [blockBE lb.val] := by
      have hl : lb.to_slice.val = lb.val := by simp [Std.Array.to_slice]
      have hr : chunksRest 16 lb.val = [] := List.eq_nil_of_length_eq_zero (by rw [chunksRest_length]; simp)
      rw [hl, padBlocks, chunksOf_self _ (by omega) (by simp), hr]
      rfl
    have e0 : (0#usize).val = 0 := rfl
    have hg := gcmHash_eq hLE [] iv.val y' (by
      rw [hyp', hpb, List.map_singleton, ghashPoly_cons, ghashPoly_nil, blockBE, hlb, hyp, padBlocks_nil,
        List.nil_append, toPoly_zero, Slice.len_val, List.length_nil, e0])
    rw [List.map_nil] at hg
    rw [computeIvBE_other _ _ (by simpa [bvs] using h12), reverseBytesQuad32_involutive, ← hg]
    conv_lhs => rw [← reverseBytesQuad32_involutive (loadBytes _), short.rev_load_be]

end rind.aarch64
