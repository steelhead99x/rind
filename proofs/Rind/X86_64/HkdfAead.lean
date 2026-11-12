import Rind.X86_64.Hkdf
import Rind.X86_64.AesGcmAead
import Rind.X86_64.ChaCha20Poly1305
open Aeneas Aeneas.Std Result rind.vale rind.spec

/-!
# HKDF's conversions to AES-GCM, ChaCha20-Poly1305, and AES header-protection keys

`From<Okm<&'static aead::Algorithm>> for aead::Key` fills the algorithm's key
length of HKDF-Expand into a buffer, then keys the algorithm with it through
`Key::new`. This file composes that with `AesGcm`'s `aes_gcm_new`, so the key
holds AES-GCM for the HKDF bytes, and with
`ChaCha20Poly1305`'s `chacha20_poly1305_new`, so it holds ChaCha20-Poly1305
for them. The same conversion to an AES `aead::quic::HeaderProtectionKey`
composes with `AesCipher`'s `aes_header_new`. It lives apart from `Hkdf`
because these proofs are x86_64's, and so `admin/prove` writes no aarch64
copy of it.
-/

namespace rind.x86_64.kdf

/-- `Key::new` of the AES-GCM algorithm `alg` names, for key bytes of its length,
through the translation's wrapper: the key holds AES-GCM for the
bytes, as `aes_gcm_new` states, and the wrapper refuses only what `new` does. -/
theorem aead_key_new_spec (h : RunsAesGcm) (alg : Algorithm) (algorithm : aead.Algorithm)
    (halg : (algorithm = aead.AES_128_GCM ∧ alg = .AES_128) ∨
      (algorithm = aead.AES_256_GCM ∧ alg = .AES_256))
    (key : Slice U8) (hk : key.length = 4 * nk alg) :
    aead.Key.new algorithm key ⦃ r => ∃ k, r = .Ok k ∧ KeyReady alg (bv key.val) k ⦄ := by
  unfold aead.Key.new
  apply WP.spec_bind (rind.x86_64.aes_gcm_new h alg algorithm halg key)
  intro r hr
  rw [if_pos hk] at hr
  obtain ⟨k, rfl, hk'⟩ := hr
  exact (WP.spec_ok _).mpr ⟨k, rfl, hk'⟩

/-- `aead::Key`'s conversion from `Okm` holds AES-GCM for the `4 * nk` bytes
of HKDF-Expand, for AES-128-GCM and AES-256-GCM. -/
theorem aead_key_from_spec (h : RunsAesGcm) (a : high.hmac.Algorithm) (hr : RunsHmac a)
    (prk : List Byte) (k : high.hmac.Key) (hk : KeyOf a prk k) (info : Slice (Slice U8))
    (hinfo : hmacBlock a + tagLen a + (infoBytes info).length + 1 ≤ maxInput)
    (alg : Algorithm) (algorithm : aead.Algorithm)
    (halg : (algorithm = aead.AES_128_GCM ∧ alg = .AES_128) ∨
      (algorithm = aead.AES_256_GCM ∧ alg = .AES_256)) :
    aead.Key.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
      { prk := k, info := info, len := algorithm } ⦃ key =>
      KeyReady alg (hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) (4 * nk alg)) key ⦄ := by
  have hkl : (rind.x86_64.aead.Algorithm.key_len algorithm).val = 4 * nk alg := by
    rcases halg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hnk : nk alg ≤ 8 := by cases alg <;> decide
  have hpos := tagLen_pos a
  unfold aead.Key.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
  unfold aead.Algorithm.key_len
  simp only [bind_ok]
  apply WP.spec_bind (Array.index_mut_SliceIndexRangeToUsizeSlice (Array.repeat 64#usize 0#u8)
    { «end» := rind.x86_64.aead.Algorithm.key_len algorithm } (by scalar_tac))
  rintro ⟨bytes, back⟩ ⟨hb1, hb2, -⟩
  have hblen : bytes.length = 4 * nk alg := by rw [hb2]; exact hkl
  apply WP.spec_bind (expand_into_spec a hr prk k hk info hinfo bytes (by rw [hblen]; omega))
  rintro bytes1 ⟨hl1, hl2⟩
  have hbv : bv bytes1.val = hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) (4 * nk alg) := by
    rw [hl2, hblen]
  apply WP.spec_bind (aead_key_new_spec h alg algorithm halg bytes1 (by rw [hl1, hblen]))
  rintro r ⟨k', rfl, hk'⟩
  unfold core.result.Result.expect
  rw [hbv] at hk'
  exact (WP.spec_ok _).mpr hk'

/-- `Key::new` of ChaCha20-Poly1305 for 32 key bytes, through the
translation's wrapper: the key holds ChaCha20-Poly1305 for the bytes, as
`chacha20_poly1305_new` states. -/
theorem aead_key_new_chacha20_poly1305_spec (key : Slice U8) (hk : key.length = 32) :
    aead.Key.new aead.CHACHA20_POLY1305 key ⦃ r => ∃ k, r = .Ok k ∧ ChaChaKeyHolds (bvs key.val) k ⦄ := by
  unfold aead.Key.new
  apply WP.spec_bind (rind.x86_64.chacha20_poly1305_new key)
  intro r hr
  rw [ite_eq_left hk] at hr
  obtain ⟨k, rfl, hk'⟩ := hr
  exact (WP.spec_ok _).mpr ⟨k, rfl, hk'⟩

/-- `HeaderProtectionKey::new` of an AES algorithm, for key bytes of its length,
through the translation's wrapper: the key holds FIPS 197's round keys for the
bytes, as `aes_header_new` states, and the wrapper refuses only what `new`
does. -/
theorem aes_header_new_spec (h : RunsAesNi) (alg : Algorithm) (algorithm : aead.quic.Algorithm)
    (halg : (algorithm = aead.quic.AES_128 ∧ alg = .AES_128) ∨
      (algorithm = aead.quic.AES_256 ∧ alg = .AES_256))
    (key : Slice U8) (hk : key.length = 4 * nk alg) :
    aead.quic.HeaderProtectionKey.new algorithm key ⦃ r =>
      ∃ k, r = .Ok (.Aes k) ∧ AesIs alg (bv key.val) k ⦄ := by
  unfold aead.quic.HeaderProtectionKey.new
  apply WP.spec_bind (rind.x86_64.aes_header_new h alg algorithm halg key)
  intro r hr
  rw [ite_eq_left hk] at hr
  obtain ⟨k, rfl, hk'⟩ := hr
  exact (WP.spec_ok _).mpr ⟨k, rfl, hk'⟩

/-- `aead::Key`'s conversion from `Okm` holds ChaCha20-Poly1305 for the 32
bytes of HKDF-Expand. -/
theorem aead_key_from_chacha20_poly1305_spec (a : high.hmac.Algorithm) (hr : RunsHmac a)
    (prk : List Byte) (k : high.hmac.Key) (hk : KeyOf a prk k) (info : Slice (Slice U8))
    (hinfo : hmacBlock a + tagLen a + (infoBytes info).length + 1 ≤ maxInput) :
    aead.Key.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
      { prk := k, info := info, len := aead.CHACHA20_POLY1305 } ⦃ key =>
      ChaChaKeyHolds (hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) 32) key ⦄ := by
  have hkl : (rind.x86_64.aead.Algorithm.key_len aead.CHACHA20_POLY1305).val = 32 := rfl
  have hpos := tagLen_pos a
  unfold aead.Key.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
  unfold aead.Algorithm.key_len
  simp only [bind_ok]
  apply WP.spec_bind (Array.index_mut_SliceIndexRangeToUsizeSlice (Array.repeat 64#usize 0#u8)
    { «end» := rind.x86_64.aead.Algorithm.key_len aead.CHACHA20_POLY1305 } (by scalar_tac))
  rintro ⟨bytes, back⟩ ⟨hb1, hb2, -⟩
  have hblen : bytes.length = 32 := by rw [hb2]; exact hkl
  apply WP.spec_bind (expand_into_spec a hr prk k hk info hinfo bytes (by rw [hblen]; omega))
  rintro bytes1 ⟨hl1, hl2⟩
  have hbv : bvs bytes1.val = hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) 32 := by
    show bv bytes1.val = _
    rw [hl2, hblen]
  apply WP.spec_bind (aead_key_new_chacha20_poly1305_spec bytes1 (by rw [hl1, hblen]))
  rintro r ⟨k', rfl, hk'⟩
  unfold core.result.Result.expect
  rw [hbv] at hk'
  exact (WP.spec_ok _).mpr hk'

/-- `aead::quic::HeaderProtectionKey`'s conversion from `Okm` keys AES-128 or
AES-256 header protection with the `4 * nk` bytes of HKDF-Expand. -/
theorem aes_header_key_from_spec (h : RunsAesNi) (a : high.hmac.Algorithm) (hr : RunsHmac a)
    (prk : List Byte) (k : high.hmac.Key) (hk : KeyOf a prk k) (info : Slice (Slice U8))
    (hinfo : hmacBlock a + tagLen a + (infoBytes info).length + 1 ≤ maxInput)
    (alg : Algorithm) (algorithm : aead.quic.Algorithm)
    (halg : (algorithm = aead.quic.AES_128 ∧ alg = .AES_128) ∨
      (algorithm = aead.quic.AES_256 ∧ alg = .AES_256)) :
    aead.quic.HeaderProtectionKey.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
      { prk := k, info := info, len := algorithm } ⦃ key =>
      ∃ c, key = .Aes c ∧
        AesIs alg (hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) (4 * nk alg)) c ⦄ := by
  have hkl : (rind.x86_64.aead.quic.Algorithm.key_len algorithm).val = 4 * nk alg := by
    rcases halg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hnk : nk alg ≤ 8 := by cases alg <;> decide
  have hpos := tagLen_pos a
  unfold aead.quic.HeaderProtectionKey.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
  unfold aead.quic.Algorithm.key_len
  simp only [bind_ok]
  apply WP.spec_bind (Array.index_mut_SliceIndexRangeToUsizeSlice (Array.repeat 64#usize 0#u8)
    { «end» := rind.x86_64.aead.quic.Algorithm.key_len algorithm } (by scalar_tac))
  rintro ⟨bytes, back⟩ ⟨hb1, hb2, -⟩
  have hblen : bytes.length = 4 * nk alg := by rw [hb2]; exact hkl
  apply WP.spec_bind (expand_into_spec a hr prk k hk info hinfo bytes (by rw [hblen]; omega))
  rintro bytes1 ⟨hl1, hl2⟩
  have hbv : bv bytes1.val = hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) (4 * nk alg) := by
    rw [hl2, hblen]
  apply WP.spec_bind (aes_header_new_spec h alg algorithm halg bytes1 (by rw [hl1, hblen]))
  rintro r ⟨c, rfl, hc⟩
  unfold core.result.Result.expect
  rw [hbv] at hc
  exact (WP.spec_ok _).mpr ⟨c, rfl, hc⟩

end rind.x86_64.kdf
