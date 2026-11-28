import Rind.Aarch64.AesGcmAead
open Aeneas Aeneas.Std Result rind.vale rind.simd

/-!
# AES-GCM under any IV, with tags of any length

`AesGcm::encrypt_any` and `decrypt_any`, which `aead::gcm::Key` seals with
for an IV other than 96 bits, and opens with for such an IV or a tag shorter
than 16 bytes, on a key `GcmReady` holds of: the counter block is
`compute_iv_BE`'s, the GHASH of the IV's padded blocks and its bit length
unless the IV is 96 bits, the rest is `tagged_from`, and a tag of `t` bytes
is the first `t` of Vale's, as SP 800-38D's `MSB_t` truncates it. Both refuse
what `check_gcm_iv` and `check_gcm_lengths` do, leaving the buffer as it was.
-/

namespace rind.aarch64

/-! ## The refusals -/

theorem usize_lt (n : Usize) : n.val < 2 ^ 64 := by
  have := n.hmax
  rcases System.Platform.numBits_eq with h | h
  · simp_all [UScalarTy.Usize_numBits_eq]; omega
  · simp_all [UScalarTy.Usize_numBits_eq]

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

/-! ## `encrypt_any` and `decrypt_any` -/

/-- A slice of `tag` up to `n`, at most 16, is its first `n` bytes. -/
theorem index_tag (tag : Std.Array U8 16#usize) (n : Usize) (hn : n.val ≤ 16) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8)) tag
      { «end» := n } ⦃ s => s.val = tag.val.take n.val ∧ s.length = n.val ⦄ := by
  rw [Array.index_SliceIndexRangeToUsizeSlice]
  apply WP.spec_mono (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec _ _
    (by simp [Std.Array.to_slice, Slice.length]; exact hn))
  rintro s ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  rw [h1]; simp [Std.Array.to_slice, List.slice]

/-- `AesGcm::encrypt_any`: an empty IV, or an IV or AAD of
2^61 bytes or more, or a message past 2^36 - 32 bytes, is refused, and the
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
  obtain ⟨e, he⟩ := he
  obtain ⟨hk, t, hkey, hhk, hgt, ht, hsha⟩ := hg
  obtain ⟨key, gh⟩ := g
  simp only at hkey hgt
  subst hkey hgt
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
  have hiv' : iv.length < 2 ^ 61 := by omega
  apply WP.spec_bind (initial_counter_spec (aesEncrypt alg kw (mkfour 0 0 0 0)) t ht iv hiv')
  intro y0 hy
  apply WP.spec_bind (long.tagged_from_spec true hk alg kw hhk t ht hsha _ y0 hy
    aad inout (by omega))
  rintro ⟨tag, out⟩ ⟨hlen, hout, htag⟩
  simp only [ite_true] at htag
  apply WP.spec_bind (index_tag tag tag_out.len (by rw [Slice.len_val]; exact htl))
  rintro s ⟨hs1, hs2⟩
  apply WP.spec_bind (core.slice.Slice.copy_from_slice.step_spec _ tag_out s (by rw [hs2, Slice.len_val]))
  rintro s' rfl
  simp only [low.ct.public_slice, bind_ok, WP.spec_ok]
  simp only [hiv, or_false, ite_false]
  have ht' : bvs (tag.val.take tag_out.length) = (bvs tag.val).take tag_out.length := List.map_take ..
  refine ⟨trivial, hlen, by rw [hs2, Slice.len_val], ?_, ?_⟩
  · rw [hout]; simp only [gcmEncrypt, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE]
  · rw [hs1, Slice.len_val, ht', htag]
    simp only [gcmEncrypt, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE, ← hout]

/-- `AesGcm::decrypt_any`: refused as `encrypt_any` is, the
buffer left as it was; otherwise it succeeds exactly when `tag`, of at most 16
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
        let out := gcmDecryptTrunc alg (seqNat32ToSeqNat8LE kw) (bvs iv.val) (bvs inout.val) (bvs aad.val)
          (bvs tag.val)
        if out.2 then r.1 = .Ok () ∧ bvs r.2.val = out.1
        else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate inout.length 0#u8 ⦄ := by
  obtain ⟨e, he⟩ := he
  obtain ⟨hk, t, hkey, hhk, hgt, ht, hsha⟩ := hg
  obtain ⟨key, gh⟩ := g
  simp only at hkey hgt
  subst hkey hgt
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
  have hiv' : iv.length < 2 ^ 61 := by omega
  apply WP.spec_bind (initial_counter_spec (aesEncrypt alg kw (mkfour 0 0 0 0)) t ht iv hiv')
  intro y0 hy
  apply WP.spec_bind (long.tagged_from_spec false hk alg kw hhk t ht hsha _ y0 hy
    aad inout (by omega))
  rintro ⟨want, out⟩ ⟨hlen, hout, htag⟩
  simp only [Bool.false_eq_true, ite_false] at htag
  apply WP.spec_bind (index_tag want tag.len (by rw [Slice.len_val]; exact htl))
  rintro s ⟨hs1, hs2⟩
  apply WP.spec_bind (ct_equal_spec hheld s tag)
  rintro b rfl
  simp only [hiv, or_false, ite_false]
  have ht' : bvs (want.val.take tag.length) = (bvs want.val).take tag.length := List.map_take ..
  have hb : ((gcmTag alg (seqNat32ToSeqNat8LE kw) (bvs iv.val) (bvs inout.val) (bvs aad.val)).take
      (bvs tag.val).length == bvs tag.val) = decide (s.val = tag.val) := by
    rw [← bvs_beq, hs1, Slice.len_val, ht', htag, List.length_map]
    simp only [gcmTag, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE, Slice.length]
  have hp : (gcmDecryptTrunc alg (seqNat32ToSeqNat8LE kw) (bvs iv.val) (bvs inout.val) (bvs aad.val)
      (bvs tag.val)).1 = bvs out.val := by
    rw [hout]; simp only [gcmDecryptTrunc, gcmDecrypt, seqNat8ToSeqNat32LE_seqNat32ToSeqNat8LE]
  have h2 : (gcmDecryptTrunc alg (seqNat32ToSeqNat8LE kw) (bvs iv.val) (bvs inout.val) (bvs aad.val)
      (bvs tag.val)).2 = decide (s.val = tag.val) := hb
  rw [h2, hp]
  simp only [low.ct.into_public, bind_ok]
  by_cases hc : s.val = tag.val
  · simp only [hc, decide_true, ite_true, low.ct.public_slice, bind_ok, WP.spec_ok]
    exact ⟨trivial, trivial⟩
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false]
    step*

end rind.aarch64
