import Rind.X86_64.AesGcmClmul
open Aeneas Aeneas.Std Result rind.vale

/-!
# AES-GCM's key setup, seal, and open on x86_64

On CPUs with AVX and MOVBE but no VAES, rind seals and opens with Vale's
routines, but hands `by8` what they do not take: seals under 129 bytes, and
AAD or messages of 2^32 bytes or more. On CPUs with AES-NI and PCLMULQDQ but
no AVX, it runs `by8` alone. Both tiers are AES-GCM for every AAD and message
length rind takes, which this file states for `AesGcm` and its AEAD API.
-/

namespace rind.x86_64

/-- rind runs Vale's tier or its SSE tier of AES-GCM on this CPU. -/
def RunsAesGcm : Prop := RunsValeAesGcm ∨ RunsClmulAesGcm

/-- An AES-GCM key for the AES key `kw` and `alg`, on Vale's tier or the SSE
tier. -/
def GcmReady (alg : Algorithm) (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) : Prop :=
  ReadyClmul alg kw g ∨ (Ready alg kw g ∧ ∃ t kernel, g.gh = .Avx t kernel ∧
    TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t)

/-- `AesGcm::new` on Vale's tier sets up Vale's AES-GCM: FIPS 197's round
keys and the GHASH key powers `hkeys_reqs_pub` requires, which `by8`'s table
holds too. -/
theorem aes_gcm_new_vale_spec (h : RunsValeAesGcm) (alg : Algorithm) (key : Slice U8)
    (hk : KeyLen alg key.length) :
    mid.aes_gcm.AesGcm.new key ⦃ g => Ready alg (seqNat8ToSeqNat32LE (bvs key.val)) g ∧
      ∃ t kernel, g.gh = .Avx t kernel ∧
        TableFor (polyLE (aesEncrypt alg (seqNat8ToSeqNat32LE (bvs key.val)) (mkfour 0 0 0 0))) t ⦄ := by
  have h' := h
  obtain ⟨⟨e, he⟩, ⟨hw, hhw⟩, -, h512, hvaes, ⟨tok, htok⟩⟩ := h'
  set kw := seqNat8ToSeqNat32LE (bvs key.val)
  have hkey : mid.aes.expand_key key ⦃ k => ∃ hwk, k = .Hw hwk ∧ HwKeyIs alg kw hwk ⦄ := by
    rcases hk with ⟨rfl, hl⟩ | ⟨rfl, hl⟩
    · exact WP.spec_mono (expand_key128_spec h.aesNi key hl) fun k ⟨k128, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
    · exact WP.spec_mono (expand_key256_spec h.aesNi key hl) fun k ⟨k256, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
  unfold mid.aes_gcm.AesGcm.new
  rw [he, bind_ok]
  apply WP.spec_bind hkey
  rintro _ ⟨hwk, rfl, hwk_is⟩
  simp only [encrypt_zero hwk alg kw hwk_is, bind_ok, lift, low.x86_64.ghash.GhashTable.new, hhw, h512,
    hvaes, htok]
  obtain ⟨px, hpx⟩ := clmul_new_eq (core.num.U128.from_be_bytes
    (low.x86_64.aes.store (aesEncrypt alg kw (mkfour 0 0 0 0)))) hw
  obtain ⟨t, ht, htf⟩ := clmul_new_spec (core.num.U128.from_be_bytes
    (low.x86_64.aes.store (aesEncrypt alg kw (mkfour 0 0 0 0)))) hw
  rw [hpx] at ht
  have ht' := Result.ok_injective ht
  subst ht'
  rw [from_be_bytes_store] at htf
  simp only [hpx, bind_ok, kernel_new_eq, WP.spec_ok]
  refine ⟨⟨hwk, _, _, rfl, rfl, ?_, hwk_is, ?_⟩, _, _, rfl, htf⟩
  · rcases hk with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ <;> simp [kw, seqNat8ToSeqNat32LE_length, hl, nk]
  · simp only [Std.Array.make_val]
    have := valeHkeys_spec (core.num.U128.from_be_bytes
      (low.x86_64.aes.store (aesEncrypt alg kw (mkfour 0 0 0 0)))).bv
    rw [from_be_bytes_store] at this ⊢; assumption

/-- `AesGcm::new` sets up AES-GCM on either tier. -/
theorem aes_gcm_new_spec (h : RunsAesGcm) (alg : Algorithm) (key : Slice U8) (hk : KeyLen alg key.length) :
    mid.aes_gcm.AesGcm.new key ⦃ g => GcmReady alg (seqNat8ToSeqNat32LE (bvs key.val)) g ⦄ := by
  rcases h with h | h
  · exact WP.spec_mono (aes_gcm_new_vale_spec h alg key hk) fun g hg => Or.inr hg
  · exact WP.spec_mono (aes_gcm_new_clmul_spec h alg key hk) fun g hg => Or.inl hg

/-- `AesGcm::encrypt` on either tier, for AAD under 2^61 bytes and messages
rind takes: the ciphertext in place and the tag are AES-GCM's. -/
theorem aes_gcm_encrypt_spec (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) (hg : GcmReady alg kw g)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (haad : aad.length < 2 ^ 61) (hin : inout.length ≤ 2 ^ 36 - 32) :
    mid.aes_gcm.AesGcm.encrypt g nonce aad inout tag ⦃ r =>
      r.1 = .Ok () ∧ r.2.1.length = inout.length ∧ (bvs r.2.1.val, bvs r.2.2.val) =
        gcmEncrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val) ⦄ := by
  rcases hg with ⟨hk, t, hkey, hhk, hgt, ht⟩ | ⟨hr, t, kernel, hgt, ht⟩
  · refine aes_gcm_encrypt_by8 he alg kw g hk t hkey hhk (Or.inl hgt) ht nonce aad inout tag ?_ haad hin
    rw [hkey, hgt]; exact vale_clmul _ _ _ _ _
  · by_cases hv : aad.length < 2 ^ 32 ∧ inout.length < 2 ^ 32 ∧ 129 ≤ inout.length
    · exact aes_gcm_encrypt_vale he alg kw g hr nonce aad inout tag hv.1 hv.2.1 hv.2.2
    · obtain ⟨hk, table, kernel', hkey, hgh, hkk⟩ := hr
      have hhk : HwKeyIs alg kw hk := by cases hk <;> exact hkk.2.1
      refine aes_gcm_encrypt_by8 he alg kw g hk t hkey hhk (Or.inr ⟨kernel, hgt⟩) ht nonce aad inout tag ?_ haad hin
      rw [hkey, hgt]
      exact vale_avx_none true alg kw hk hhk t kernel aad inout fun h => hv ⟨h.1, h.2.1, h.2.2 rfl⟩

/-- `AesGcm::decrypt` on either tier, for AAD under 2^61 bytes and messages
rind takes: it succeeds exactly when the tag is AES-GCM's, leaving the
plaintext in place, and otherwise fails, leaving zeros. -/
theorem aes_gcm_decrypt_spec (he : ∃ e, low.entry.Entry.new_secret = ok e)
    (hheld : low.entry.Entry.assert_held = ok ()) (alg : Algorithm)
    (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) (hg : GcmReady alg kw g)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (haad : aad.length < 2 ^ 61) (hin : inout.length ≤ 2 ^ 36 - 32) :
    mid.aes_gcm.AesGcm.decrypt g nonce aad inout tag ⦃ r =>
      let out := gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val)
        (bvs tag.val)
      if out.2 then r.1 = .Ok () ∧ bvs r.2.val = out.1
      else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate inout.length 0#u8 ⦄ := by
  rcases hg with ⟨hk, t, hkey, hhk, hgt, ht⟩ | ⟨hr, t, kernel, hgt, ht⟩
  · refine aes_gcm_decrypt_by8 he hheld alg kw g hk t hkey hhk (Or.inl hgt) ht nonce aad inout tag ?_ haad hin
    rw [hkey, hgt]; exact vale_clmul _ _ _ _ _
  · by_cases hv : aad.length < 2 ^ 32 ∧ inout.length < 2 ^ 32
    · exact aes_gcm_decrypt_vale he alg kw g hr nonce aad inout tag hv.1 hv.2
    · obtain ⟨hk, table, kernel', hkey, hgh, hkk⟩ := hr
      have hhk : HwKeyIs alg kw hk := by cases hk <;> exact hkk.2.1
      refine aes_gcm_decrypt_by8 he hheld alg kw g hk t hkey hhk (Or.inr ⟨kernel, hgt⟩) ht nonce aad inout tag ?_
        haad hin
      rw [hkey, hgt]
      exact vale_avx_none false alg kw hk hhk t kernel aad inout fun h => hv ⟨h.1, h.2.1⟩

/-! ## The AEAD API -/

/-- An AEAD key holding AES-GCM for the key bytes `key` and `alg`. -/
def KeyReady (alg : Algorithm) (key : List (BitVec 8)) (k : aead.Key) : Prop :=
  key.length = 4 * nk alg ∧ ∃ g, k = .AesGcm g ∧ GcmReady alg (seqNat8ToSeqNat32LE key) g

theorem aes_gcm_new (h : RunsAesGcm) (alg : Algorithm) (algorithm : aead.Algorithm)
    (halg : (algorithm = aead.AES_128_GCM ∧ alg = .AES_128) ∨ (algorithm = aead.AES_256_GCM ∧ alg = .AES_256))
    (key : Slice U8) :
    aead.Key.new algorithm key ⦃ r =>
      if key.length = 4 * nk alg then ∃ k, r = .Ok k ∧ KeyReady alg (bvs key.val) k
      else r = .Err .WrongLength ⦄ := by
  have hlen : algorithm.key_len.val = 4 * nk alg := by
    rcases halg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  unfold aead.Key.new
  by_cases hk : key.length = 4 * nk alg
  · have hne : ¬ key.len ≠ algorithm.key_len := by
      intro hne; apply hne; scalar_tac
    rw [ite_eq_right hne]
    have hexp : algorithm.expand = aead.Sealer.expand mid.aes_gcm.AesGcm.Insts.RindAeadCipher := by
      rcases halg with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
    have hkl : KeyLen alg key.length := by
      rcases halg with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp_all [nk, KeyLen]
    have hx : aead.Sealer.expand mid.aes_gcm.AesGcm.Insts.RindAeadCipher key ⦃ i =>
        ∃ g, i = .AesGcm g ∧ GcmReady alg (seqNat8ToSeqNat32LE (bvs key.val)) g ⦄ := by
      unfold aead.Sealer.expand
      apply WP.spec_bind (aes_gcm_new_spec h alg key hkl)
      intro g hg
      exact (WP.spec_ok _).2 ⟨g, rfl, hg⟩
    rw [hexp]
    apply WP.spec_bind hx
    rintro _ ⟨g, rfl, hg⟩
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_left hk]
    exact ⟨_, rfl, by simp [hk, bvs], g, rfl, hg⟩
  · have hne : key.len ≠ algorithm.key_len := by intro he; apply hk; rw [← hlen, ← he]; simp
    rw [ite_eq_left hne]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_right hk]

theorem key_bytes (alg : Algorithm) (key : List (BitVec 8)) (h : key.length = 4 * nk alg) :
    seqNat32ToSeqNat8LE (seqNat8ToSeqNat32LE key) = key :=
  seqNat32ToSeqNat8LE_seqNat8ToSeqNat32LE key (by omega)

theorem aes_gcm_seal (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (key : List (BitVec 8)) (k : aead.Key) (hk : KeyReady alg key k) (nonce : aead.Nonce) (aad in_out : Slice U8)
    (haad : aad.length < 2 ^ 61) (hin : in_out.length ≤ 2 ^ 36 - 32) :
    k.seal_in_place_separate_tag nonce aad in_out ⦃ r =>
      ∃ tag, r.1 = .Ok tag ∧ r.2.length = in_out.length ∧
        (bvs r.2.val, bvs tag.bytes.val) = gcmEncrypt alg key (bvs nonce.bytes.val) (bvs in_out.val) (bvs aad.val) ⦄ := by
  obtain ⟨hkl, g, rfl, hg⟩ := hk
  unfold aead.Key.seal_in_place_separate_tag aead.Sealer.seal
  simp only [mid.aes_gcm.AesGcm.Insts.RindAeadCipher.seal]
  apply WP.spec_bind (aes_gcm_encrypt_spec he alg _ g hg nonce.bytes aad in_out _ haad hin)
  rintro ⟨r, out, tag⟩ ⟨rfl, hlen, hout⟩
  rw [key_bytes alg key hkl] at hout
  exact (WP.spec_ok _).2 ⟨⟨tag⟩, rfl, hlen, hout⟩

/-- Sealing through any buffer `InOut`: for the view its `as_mut` gives, the
call returns what its `extend` makes of the buffer holding the view's
ciphertext, handed the tag, both Vale's `gcm_encrypt_LE` of the view. -/
theorem aes_gcm_seal_append_tag (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (key : List (BitVec 8)) (k : aead.Key) (hk : KeyReady alg key k) (nonce : aead.Nonce) (aad : Slice U8)
    {InOut : Type} (AsMutInst : core.convert.AsMut InOut (Slice U8))
    (ExtendInst : core.iter.traits.collect.Extend InOut U8) (in_out : InOut) (view : Slice U8)
    (back : Slice U8 → InOut) (hview : AsMutInst.as_mut in_out = ok (view, back))
    (haad : aad.length < 2 ^ 61) (hin : view.length ≤ 2 ^ 36 - 32)
    (Q : (core.result.Result Unit error.Error) × InOut → Prop)
    (hext : ∀ (ct : Slice U8) (tag : Std.Array U8 16#usize), ct.length = view.length →
      (bvs ct.val, bvs tag.val) = gcmEncrypt alg key (bvs nonce.bytes.val) (bvs view.val) (bvs aad.val) →
      ExtendInst.extend (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U8) (back ct)
        tag.to_slice ⦃ out => Q (.Ok (), out) ⦄) :
    k.seal_in_place_append_tag AsMutInst ExtendInst nonce aad in_out ⦃ Q ⦄ := by
  unfold aead.Key.seal_in_place_append_tag
  simp only [hview, bind_ok]
  apply WP.spec_bind (aes_gcm_seal he alg key k hk nonce aad view haad hin)
  rintro ⟨r, ct⟩ ⟨tag, hr, hlen, henc⟩
  dsimp only at hr
  subst hr
  exact WP.spec_bind (hext ct tag.bytes hlen henc) fun out h => (WP.spec_ok _).2 h

/-- `Vec<u8>`'s `AsMut<[u8]>` impl views the whole vector. -/
def VecAsMut (AsMutInst : core.convert.AsMut (alloc.vec.Vec U8) (Slice U8)) : Prop :=
  ∀ v, AsMutInst.as_mut v = ok (alloc.vec.Vec.deref_mut v)

/-- `Vec<u8>`'s `Extend<&u8>` impl appends a slice's bytes, as its
`extend_from_slice` does. -/
def VecExtend (ExtendInst : core.iter.traits.collect.Extend (alloc.vec.Vec U8) U8) : Prop :=
  ∀ v s, ExtendInst.extend (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U8) v s =
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s

/-- Sealing a `Vec<u8>` with room for the tag: the vector becomes the
ciphertext followed by the tag, Vale's `gcm_encrypt_LE` of the message. -/
theorem aes_gcm_seal_append_tag_vec (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (key : List (BitVec 8)) (k : aead.Key) (hk : KeyReady alg key k) (nonce : aead.Nonce) (aad : Slice U8)
    (AsMutInst : core.convert.AsMut (alloc.vec.Vec U8) (Slice U8))
    (ExtendInst : core.iter.traits.collect.Extend (alloc.vec.Vec U8) U8) (hasmut : VecAsMut AsMutInst)
    (hextend : VecExtend ExtendInst) (in_out : alloc.vec.Vec U8) (haad : aad.length < 2 ^ 61)
    (hin : in_out.length ≤ 2 ^ 36 - 32) (hroom : in_out.length + 16 ≤ Usize.max) :
    k.seal_in_place_append_tag AsMutInst ExtendInst nonce aad in_out ⦃ r =>
      r.1 = .Ok () ∧ r.2.length = in_out.length + 16 ∧
        (bvs (r.2.val.take in_out.length), bvs (r.2.val.drop in_out.length)) =
          gcmEncrypt alg key (bvs nonce.bytes.val) (bvs in_out.val) (bvs aad.val) ⦄ := by
  have hl : in_out.slice.length = in_out.length := rfl
  apply aes_gcm_seal_append_tag he alg key k hk nonce aad AsMutInst ExtendInst in_out in_out.slice
    (fun s => ⟨s⟩) (hasmut in_out) haad (by rw [hl]; exact hin)
  intro ct tag hlen henc
  have hct : ct.val.length = in_out.length := hlen
  have htag : tag.to_slice.val = tag.val := by simp [Std.Array.to_slice]
  have htl : tag.val.length = 16 := by simp
  rw [hextend]
  unfold alloc.vec.Vec.extend_from_slice
  have hfit : (⟨ct⟩ : alloc.vec.Vec U8).length + tag.to_slice.length ≤ Usize.max := by
    change ct.val.length + tag.to_slice.val.length ≤ Usize.max
    rw [htag, htl, hct]; exact hroom
  rw [dite_eq_left hfit]
  apply WP.spec_bind (List.clone_spec fun _ _ => rfl)
  rintro s' ⟨hs', -⟩
  have hv : ∀ h, (alloc.vec.Vec.from ((⟨ct⟩ : alloc.vec.Vec U8).val ++ s'.val) h).val = ct.val ++ tag.val := by
    intro h; rw [alloc.vec.Vec.from_val, hs', htag]; rfl
  refine (WP.spec_ok _).2 ⟨rfl, ?_, ?_⟩
  · rw [alloc.vec.Vec.length, hv, List.length_append, hct, htl]
  · rw [hv, List.take_left' hct, List.drop_left' hct]
    exact henc

theorem aes_gcm_open_separate_tag (he : ∃ e, low.entry.Entry.new_secret = ok e)
    (hheld : low.entry.Entry.assert_held = ok ()) (alg : Algorithm)
    (key : List (BitVec 8)) (k : aead.Key) (hk : KeyReady alg key k) (nonce : aead.Nonce) (aad : Slice U8)
    (tag : aead.Tag) (in_out : Slice U8) (haad : aad.length < 2 ^ 61) (hin : in_out.length ≤ 2 ^ 36 - 32) :
    k.open_in_place_separate_tag nonce aad tag in_out ⦃ r =>
      let out := gcmDecrypt alg key (bvs nonce.bytes.val) (bvs in_out.val) (bvs aad.val) (bvs tag.bytes.val)
      if out.2 then r.1 = .Ok r.2 ∧ bvs r.2.val = out.1
      else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate in_out.length 0#u8 ⦄ := by
  obtain ⟨hkl, g, rfl, hg⟩ := hk
  unfold aead.Key.open_in_place_separate_tag aead.Sealer.open
  simp only [mid.aes_gcm.AesGcm.Insts.RindAeadCipher.open]
  apply WP.spec_bind (aes_gcm_decrypt_spec he hheld alg _ g hg nonce.bytes aad in_out tag.bytes haad hin)
  rintro ⟨r, out⟩ hr
  rw [key_bytes alg key hkl] at hr
  dsimp only at hr
  split at hr
  · obtain ⟨rfl, hout⟩ := hr
    refine (WP.spec_ok _).2 ?_
    simp_all
  · obtain ⟨rfl, hout⟩ := hr
    refine (WP.spec_ok _).2 ?_
    simp_all

theorem aes_gcm_open (he : ∃ e, low.entry.Entry.new_secret = ok e)
    (hheld : low.entry.Entry.assert_held = ok ()) (alg : Algorithm)
    (key : List (BitVec 8)) (k : aead.Key) (hk : KeyReady alg key k) (nonce : aead.Nonce) (aad in_out : Slice U8)
    (haad : aad.length < 2 ^ 61) (hin : in_out.length ≤ 2 ^ 36 - 16) :
    k.open_in_place nonce aad in_out ⦃ r =>
      if in_out.length < 16 then r.1 = .Err .DecryptFailed else
      let out := gcmDecrypt alg key (bvs nonce.bytes.val) (bvs (in_out.val.take (in_out.length - 16)))
        (bvs aad.val) (bvs (in_out.val.drop (in_out.length - 16)))
      if out.2 then r.1 = .Ok r.2 ∧ bvs r.2.val = out.1
      else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate (in_out.length - 16) 0#u8 ⦄ := by
  unfold aead.Key.open_in_place
  by_cases hs : in_out.length < 16
  · rw [ite_eq_left hs]
    exact (WP.spec_ok _).2 (by rw [ite_eq_left hs])
  · rw [ite_eq_right hs]
    have hd : (in_out.val.drop (in_out.length - 16)).length = 16 := by simp [Slice.length] at *; omega
    rw [dite_eq_left hd]
    apply WP.spec_mono (aes_gcm_open_separate_tag he hheld alg key k hk nonce aad _ _ haad (by
      rw [Slice.length, Slice.from_val, List.length_take]; omega))
    intro r hr
    rw [ite_eq_right hs]
    simp only [Slice.from_val, Std.Array.from_val] at hr
    have hl : ∀ h, (Slice.from (List.take (in_out.length - 16) in_out.val) h).length = in_out.length - 16 := by
      intro h; rw [Slice.length, Slice.from_val, List.length_take]; simp only [Slice.length] at *; omega
    rw [hl] at hr
    exact hr

end rind.x86_64
