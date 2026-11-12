import Rind.X86_64.Hkdf
import Rind.X86_64.AesCipher
open Aeneas Aeneas.Std Result rind.vale rind.spec

/-!
# HKDF's conversion to an AES header-protection key

`From<Okm<&'static aead::quic::Algorithm>> for aead::quic::HeaderProtectionKey`
fills the algorithm's key length of HKDF-Expand into a buffer, then keys the
algorithm with it through `HeaderProtectionKey::new`. This file composes that
with `AesCipher`'s `aes_header_new`, so the key holds FIPS 197's round keys
for the HKDF bytes. `admin/prove` writes the aarch64 copy of this file.
-/

namespace rind.x86_64.kdf

/-- `HeaderProtectionKey::new` of an AES algorithm, for key bytes of its length,
through the translation's wrapper: the key holds FIPS 197's round keys for the
bytes, as `aes_header_new` states, and the wrapper refuses only what `new`
does. -/
theorem aes_header_new_spec (h : RunsAesHw) (alg : Algorithm) (algorithm : aead.quic.Algorithm)
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

/-- `aead::quic::HeaderProtectionKey`'s conversion from `Okm` keys AES-128 or
AES-256 header protection with the `4 * nk` bytes of HKDF-Expand. -/
theorem aes_header_key_from_spec (h : RunsAesHw) (a : high.hmac.Algorithm) (hr : RunsHmac a)
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
