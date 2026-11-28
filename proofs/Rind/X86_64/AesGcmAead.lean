import Rind.X86_64.AesGcmClmul
open Aeneas Aeneas.Std Result rind.vale rind.simd

/-!
# AES-GCM's key setup, seal, and open on x86_64

On CPUs with AVX and MOVBE but no VAES, rind seals and opens with Vale's
routines, but hands `by8` what they do not take: seals under 129 bytes, and
AAD or messages of 2^32 bytes or more. On CPUs with AES-NI and PCLMULQDQ but
no AVX, it runs `by8` alone. Both tiers are AES-GCM for every AAD and message
length rind takes, which this file states for `AesGcm`, and
`Rind.X86_64.AesGcmApi` for its AEAD API.
-/

namespace rind.x86_64

/-- rind runs Vale's tier or its SSE tier of AES-GCM on this CPU. -/
def RunsAesGcm : Prop := RunsValeAesGcm ∨ RunsClmulAesGcm

/-- An AES-GCM key for the AES key `kw` and `alg`, on Vale's tier or the SSE
tier: FIPS 197's round keys, by-8's table of the GHASH key's powers, and, on
Vale's tier, the GHASH key powers `hkeys_reqs_pub` requires, unless the key is
AES-192, which Vale's routines do not take. -/
def GcmReady (alg : Algorithm) (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) : Prop :=
  ∃ hk t, g.key = .Hw hk ∧ HwKeyIs alg kw hk ∧ By8Of g.gh t ∧
    TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t ∧
    ∀ kernel, g.gh = .Avx t kernel → alg = .AES_192 ∨ KernelKeys alg hk kw kernel

/-- `AesGcm::new` on Vale's tier sets up Vale's AES-GCM: FIPS 197's round
keys, `by8`'s table of the GHASH key's powers, and, unless the key is AES-192,
which Vale's routines do not take, the powers `hkeys_reqs_pub` requires. -/
theorem aes_gcm_new_vale_spec (h : RunsValeAesGcm) (alg : Algorithm) (key : Slice U8)
    (hk : KeyLen alg key.length) :
    mid.aes_gcm.AesGcm.new key ⦃ g => GcmReady alg (seqNat8ToSeqNat32LE (bvs key.val)) g ⦄ := by
  have h' := h
  obtain ⟨⟨e, he⟩, ⟨hw, hhw⟩, -, h512, hvaes, ⟨tok, htok⟩⟩ := h'
  set kw := seqNat8ToSeqNat32LE (bvs key.val)
  have hkey : mid.aes.expand_key key ⦃ k => ∃ hwk, k = .Hw hwk ∧ HwKeyIs alg kw hwk ⦄ := by
    rcases hk with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩
    · exact WP.spec_mono (expand_key128_spec h.aesNi key hl) fun k ⟨k128, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
    · exact WP.spec_mono (expand_key192_spec h.aesNi key hl) fun k ⟨k192, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
    · exact WP.spec_mono (expand_key256_spec h.aesNi key hl) fun k ⟨k256, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
  unfold mid.aes_gcm.AesGcm.new
  rw [he, bind_ok]
  apply WP.spec_bind hkey
  rintro _ ⟨hwk, rfl, hwk_is⟩
  simp only [encrypt_zero hwk alg kw hwk_is, bind_ok, lift, low.x86_64.ghash.GhashTable.new, hhw, h512,
    hvaes, htok]
  obtain ⟨px, hpx⟩ := clmul_new_eq (core.num.U128.from_be_bytes
    (storeBytes (aesEncrypt alg kw (mkfour 0 0 0 0)))) hw
  obtain ⟨t, ht, htf⟩ := clmul_new_spec (core.num.U128.from_be_bytes
    (storeBytes (aesEncrypt alg kw (mkfour 0 0 0 0)))) hw
  rw [hpx] at ht
  have ht' := Result.ok_injective ht
  subst ht'
  rw [from_be_bytes_store] at htf
  simp only [hpx, bind_ok, kernel_new_eq, WP.spec_ok]
  refine ⟨hwk, _, rfl, hwk_is, Or.inr ⟨_, rfl⟩, htf, ?_⟩
  rintro kernel hkernel
  cases hkernel
  cases hwk with
  | Aes192 k => exact Or.inl hwk_is.1
  | Aes128 k | Aes256 k =>
    refine Or.inr ⟨?_, hwk_is, ?_⟩
    · rcases hk with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ <;>
        first
        | exact absurd hwk_is.1 (by decide)
        | simp [kw, seqNat8ToSeqNat32LE_length, hl, nk]
    · simp only [Std.Array.make_val]
      have := valeHkeys_spec (core.num.U128.from_be_bytes
        (storeBytes (aesEncrypt alg kw (mkfour 0 0 0 0)))).bv
      rw [from_be_bytes_store] at this ⊢; assumption

/-- `AesGcm::new` sets up AES-GCM on either tier. -/
theorem aes_gcm_new_spec (h : RunsAesGcm) (alg : Algorithm) (key : Slice U8) (hk : KeyLen alg key.length) :
    mid.aes_gcm.AesGcm.new key ⦃ g => GcmReady alg (seqNat8ToSeqNat32LE (bvs key.val)) g ⦄ := by
  rcases h with h | h
  · exact aes_gcm_new_vale_spec h alg key hk
  · refine WP.spec_mono (aes_gcm_new_clmul_spec h alg key hk) ?_
    rintro g ⟨hk, t, hkey, hhk, hgt, ht⟩
    exact ⟨hk, t, hkey, hhk, Or.inl hgt, ht, fun kernel h => by rw [hgt] at h; cases h⟩

/-- `aes_gcm::seal` and `open` never run Vale's routines for an AES-192 key,
which they do not take. -/
theorem vale_192_none (enc : Bool) (k : low.x86_64.aes.AesKey192) (gh : low.x86_64.ghash.GhashTable)
    (aad inout : Slice U8) :
    low.x86_64.aes_gcm.vale enc (.Hw (.Aes192 k)) gh aad inout ⦃ o => o = none ⦄ := by
  unfold low.x86_64.aes_gcm.vale
  cases enc <;> step*

/-- On a key `GcmReady` holds of, `seal` or `open` runs Vale's routine, on its
tier, or else hands `by8` its key and table. -/
theorem GcmReady.cases {alg : Algorithm} {kw : List (BitVec 32)} {g : mid.aes_gcm.AesGcm}
    (hg : GcmReady alg kw g) (enc : Bool) (aad inout : Slice U8) :
    (Ready alg kw g ∧ aad.length < 2 ^ 32 ∧ inout.length < 2 ^ 32 ∧ (enc = true → 129 ≤ inout.length)) ∨
    ∃ hk t, g.key = .Hw hk ∧ HwKeyIs alg kw hk ∧ By8Of g.gh t ∧
      TableFor (polyLE (aesEncrypt alg kw (mkfour 0 0 0 0))) t ∧
      low.x86_64.aes_gcm.vale enc g.key g.gh aad inout ⦃ o => o = none ⦄ := by
  obtain ⟨hk, t, hkey, hhk, hgt, ht, hkern⟩ := hg
  rcases hgt with hgt | ⟨kernel, hgt⟩
  · refine Or.inr ⟨hk, t, hkey, hhk, Or.inl hgt, ht, ?_⟩
    rw [hkey, hgt]; exact vale_clmul _ _ _ _ _
  · rcases hkern kernel hgt with h192 | hkk
    · refine Or.inr ⟨hk, t, hkey, hhk, Or.inr ⟨kernel, hgt⟩, ht, ?_⟩
      cases hk with
      | Aes192 k => rw [hkey]; exact vale_192_none _ _ _ _ _
      | Aes128 k | Aes256 k => exact absurd (hhk.1.symm.trans h192) (by decide)
    · by_cases hv : aad.length < 2 ^ 32 ∧ inout.length < 2 ^ 32 ∧ (enc = true → 129 ≤ inout.length)
      · exact Or.inl ⟨⟨hk, t, kernel, hkey, hgt, hkk⟩, hv⟩
      · refine Or.inr ⟨hk, t, hkey, hhk, Or.inr ⟨kernel, hgt⟩, ht, ?_⟩
        rw [hkey, hgt]
        exact vale_avx_none enc alg kw hk hhk t kernel aad inout hv

/-- `AesGcm::encrypt` on either tier, for AAD under 2^61 bytes and messages
rind takes: the ciphertext in place and the tag are AES-GCM's. -/
theorem aes_gcm_encrypt_spec (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) (hg : GcmReady alg kw g)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (haad : aad.length < 2 ^ 61) (hin : inout.length ≤ 2 ^ 36 - 32) :
    mid.aes_gcm.AesGcm.encrypt g nonce aad inout tag ⦃ r =>
      r.1 = .Ok () ∧ r.2.1.length = inout.length ∧ (bvs r.2.1.val, bvs r.2.2.val) =
        gcmEncrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val) ⦄ := by
  rcases hg.cases true aad inout with ⟨hr, h1, h2, h3⟩ | ⟨hk, t, hkey, hhk, hgt, ht, hv⟩
  · exact aes_gcm_encrypt_vale he alg kw g hr nonce aad inout tag h1 h2 (h3 rfl)
  · exact aes_gcm_encrypt_by8 he alg kw g hk t hkey hhk hgt ht nonce aad inout tag hv haad hin

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
  rcases hg.cases false aad inout with ⟨hr, h1, h2, -⟩ | ⟨hk, t, hkey, hhk, hgt, ht, hv⟩
  · exact aes_gcm_decrypt_vale he alg kw g hr nonce aad inout tag h1 h2
  · exact aes_gcm_decrypt_by8 he hheld alg kw g hk t hkey hhk hgt ht nonce aad inout tag hv haad hin

end rind.x86_64
