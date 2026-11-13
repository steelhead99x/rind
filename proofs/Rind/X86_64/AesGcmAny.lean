import Rind.X86_64.AesGcmAead
open Aeneas Aeneas.Std Result rind.vale rind.simd

/-!
# AES-GCM under any IV, with tags of any length

`AesGcm::encrypt_any` and `decrypt_any`, which `aead::gcm::Key` seals with
for an IV other than 96 bits, and opens with for such an IV or a tag shorter
than 16 bytes, on either tier
`AesGcmAead` covers: the counter block is `compute_iv_BE`'s, the GHASH of the
IV's padded blocks and its bit length unless the IV is 96 bits, the rest is
`tagged_from`, and a tag of `t` bytes is the first `t` of Vale's, as SP
800-38D's `MSB_t` truncates it. Both refuse what `check_gcm_iv` and
`check_gcm_lengths` do, leaving the buffer as it was.
-/

local notation "P" => Polynomial (ZMod 2)

namespace rind.x86_64

/-! ## The spec -/

/-- AES-GCM's tag over the ciphertext `cipher`, as `gcm_encrypt_LE_def` and
`gcm_decrypt_LE_def` compute it. -/
noncomputable def gcmTag (alg : Algorithm) (key iv cipher auth : List (BitVec 8)) : List (BitVec 8) :=
  let keyLE := seqNat8ToSeqNat32LE key
  let hLE := aesEncrypt alg keyLE (mkfour 0 0 0 0)
  gctrEncrypt (computeIvBE hLE iv) (leQuad32ToBytes (gcmHash hLE auth cipher)) alg keyLE

/-- SP 800-38D's authenticated decryption under a tag of `tag.length` bytes,
at most 16: `gcm_decrypt_LE`'s plaintext, and whether `tag` is the first
bytes of the tag, `MSB_t` of it. -/
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

/-- An IV other than 96 bits hashes as `gcm_hash` does with no AAD. -/
theorem computeIvBE_other (hLE : Quad32) (iv : List (BitVec 8)) (h : iv.length ≠ 12) :
    computeIvBE hLE iv = reverseBytesQuad32 (gcmHash hLE [] iv) := by
  have hz : insertNat64 (mkfour 0 0 0 0) (8 * ([] : List (BitVec 8)).length) 1 = mkfour 0 0 0 0 := by decide
  rw [computeIvBE, ite_eq_right (by omega), gcmHash, hz]
  simp [padTo128Bits, leBytesToSeqQuad32, seqNat8ToSeqNat32LE, seqToSeqFourLE]

/-! ## Slices -/

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

/-! ## The counter block -/

/-- `initial_counter` on a table that hashes by PCLMULQDQ is `compute_iv_BE`'s
counter block, as `by8` loads it. -/
theorem initial_counter_spec (hLE : Quad32) (table : low.x86_64.ghash.GhashTable)
    (t : low.x86_64.ghash.ClmulTable) (hg : ClmulOf table t) (ht : TableFor (polyLE hLE) t)
    (iv : Slice U8) (hiv : iv.length < 2 ^ 61) :
    low.x86_64.aes_gcm.initial_counter table iv ⦃ y0 =>
      loadBytes y0.val = reverseBytesQuad32 (computeIvBE hLE (bvs iv.val)) ⦄ := by
  unfold low.x86_64.aes_gcm.initial_counter
  by_cases h12 : iv.length = 12
  · obtain ⟨a, ha, hav⟩ := try_from_len 12#usize iv h12
    obtain ⟨y0, hcb, hy⟩ := counter_block_eq hLE a
    simp only [ha, bind_ok, hcb, WP.spec_ok]
    rw [hy, hav]
  · rw [try_from_ne 12#usize iv h12, bind_ok]
    obtain ⟨y, hy, hyp⟩ := clmul_add_spec (polyLE hLE) (small_toPoly _) t ht iv.val 0
    simp only [low.x86_64.ghash.Ghash.new, low.x86_64.ghash.zero, core.core_arch.x86.sse2._mm_setzero_si128,
      bind_ok, low.x86_64.ghash.Ghash.add, addBytes_clmul ⟨table, 0⟩ t hg, hy]
    apply WP.spec_bind (add_lengths_spec ⟨table, y⟩ t (polyLE hLE) (small_toPoly _) ht hg 0#usize iv.len
      (by rw [Slice.len_val]; exact hiv))
    rintro g' ⟨-, hg'⟩
    simp only [low.x86_64.ghash.Ghash.tag, byte_reverse_eq, core.core_arch.x86.sse2._mm_xor_si128, load_zero,
      bind_ok, WP.spec_ok]
    have hz : mkfour 0 0 0 0 = (0 : BitVec 128) := by decide
    have hx : ∀ x : BitVec 128, x ^^^ 0 = x := fun x => by simp
    rw [load_store, hz, hx, computeIvBE_other _ _ (by simpa [bvs] using h12),
      reverseBytesQuad32_involutive]
    have := gcmHash_eq hLE [] iv.val g'.current (by
      have e0 : (0#usize).val = 0 := rfl
      rw [hg', hyp, toPoly_zero, padBlocks_nil, List.nil_append, Slice.len_val, List.length_nil,
        Nat.mul_zero, e0, Nat.mul_zero, Slice.length])
    exact this

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

/-- `AesGcm::encrypt_any` on either tier: an empty IV, or an IV or AAD of
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
  obtain ⟨hk, t, hkey, hhk, hgt, ht, -⟩ := hg
  obtain ⟨key, gh⟩ := g
  simp only at hkey hgt
  subst hkey
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
  apply WP.spec_bind (initial_counter_spec (aesEncrypt alg kw (mkfour 0 0 0 0)) gh t hgt.clmulOf ht iv hiv')
  intro y0 hy
  apply WP.spec_bind (tagged_from_spec true hk alg kw hhk t ht gh hgt _ y0 hy aad inout (by omega))
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

/-- `AesGcm::decrypt_any` on either tier: refused as `encrypt_any` is, the
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
  obtain ⟨hk, t, hkey, hhk, hgt, ht, -⟩ := hg
  obtain ⟨key, gh⟩ := g
  simp only at hkey hgt
  subst hkey
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
  apply WP.spec_bind (initial_counter_spec (aesEncrypt alg kw (mkfour 0 0 0 0)) gh t hgt.clmulOf ht iv hiv')
  intro y0 hy
  apply WP.spec_bind (tagged_from_spec false hk alg kw hhk t ht gh hgt _ y0 hy aad inout (by omega))
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

end rind.x86_64
