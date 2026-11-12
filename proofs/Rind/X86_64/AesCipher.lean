import Rind.X86_64.AesKey
import Rind.X86_64.Dispatch
open Aeneas Aeneas.Std Result rind.vale rind.simd

/-!
# `cipher::Aes` and AES header protection on the AES instructions

`Aes::new` expands a key with rind's key expansion on the CPU's AES
instructions, which `Rind.X86_64.AesKey` proves computes FIPS 197's round keys
as Vale's AES spec lays them out, and `encrypt_block` and
`header_protection_mask` run its block cipher, which the same file proves is
Vale's `aes_encrypt_LE`. These theorems compose the two through `mid::aes`,
for AES-128, AES-192, and AES-256, and, for header protection, which RFC 9001
defines for AES-128 and AES-256 alone, through `Rind.X86_64.Dispatch`'s model
of `aead::quic`'s dispatch. `admin/prove` writes the aarch64 copy of this
file, as it does `Dispatch`'s.
-/

namespace rind.x86_64

theorem store_bytes (q : BitVec 128) : bvs (storeBytes q).val = leQuad32ToBytes q := by
  simp [storeBytes, Std.Array.from_val, Function.comp_def, bvs]

/-- An AES key holding FIPS 197's round keys for the key bytes `key`, which
`alg` sizes, on the AES instructions. -/
def AesIs (alg : Algorithm) (key : List (BitVec 8)) (k : mid.aes.Aes) : Prop :=
  key.length = 4 * nk alg ∧ ∃ hk, k = .Hw hk ∧ HwKeyIs alg (seqNat8ToSeqNat32LE key) hk

theorem aes_encrypt (alg : Algorithm) (key : List (BitVec 8)) (k : mid.aes.Aes) (hk : AesIs alg key k)
    (b : Std.Array U8 16#usize) :
    low.x86_64.aes.AesKey.encrypt_block k b =
      ok (storeBytes (aesEncrypt alg (seqNat8ToSeqNat32LE key) (leBytesToQuad32 (bvs b.val)))) := by
  obtain ⟨-, hwk, rfl, hwk_is⟩ := hk
  exact hw_encrypt_block hwk alg _ hwk_is b

/-- A `cipher::Aes` key is refused unless it is the algorithm's length, and
otherwise holds FIPS 197's round keys for its bytes. -/
theorem aes_new (h : RunsAesHw) (alg : Algorithm) (algorithm : cipher.Algorithm)
    (hlen : algorithm.key_len.val = 4 * nk alg) (key : Slice U8) :
    mid.aes.Aes.new algorithm key ⦃ r =>
      if key.length = 4 * nk alg then ∃ k, r = .Ok k ∧ AesIs alg (bvs key.val) k
      else r = .Err .WrongLength ⦄ := by
  have he := h.1
  obtain ⟨e, he⟩ := he
  unfold mid.aes.Aes.new
  rw [he, bind_ok]
  by_cases hk : key.length = 4 * nk alg
  · have hne : ¬ (Slice.len key != algorithm.key_len) = true := by
      simp only [bne_iff_ne, ne_eq, not_not]; scalar_tac
    simp only [hne, ite_eq_left hk]
    have hx : mid.aes.expand_key key ⦃ k => ∃ hwk, k = .Hw hwk ∧
        HwKeyIs alg (seqNat8ToSeqNat32LE (bvs key.val)) hwk ⦄ := by
      cases alg
      · exact WP.spec_mono (expand_key128_spec h key (by simpa [nk] using hk))
          fun k ⟨k128, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
      · exact WP.spec_mono (expand_key192_spec h key (by simpa [nk] using hk))
          fun k ⟨k192, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
      · exact WP.spec_mono (expand_key256_spec h key (by simpa [nk] using hk))
          fun k ⟨k256, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
    apply WP.spec_bind hx
    rintro _ ⟨hwk, rfl, hwk_is⟩
    exact (WP.spec_ok _).2 ⟨_, rfl, by simp [bvs, hk], hwk, rfl, hwk_is⟩
  · have hne : (Slice.len key != algorithm.key_len) = true := by
      simp only [bne_iff_ne, ne_eq]; intro he; apply hk; rw [← hlen, ← he]; simp
    simp only [hne, ite_true, ite_eq_right hk, WP.spec_ok]

/-- `cipher::Aes::encrypt_block` replaces the block with FIPS 197's cipher of
it under the key. -/
theorem aes_encrypt_block (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (key : List (BitVec 8)) (k : mid.aes.Aes) (hk : AesIs alg key k) (block : Std.Array U8 16#usize) :
    mid.aes.Aes.encrypt_block k block ⦃ out => bvs out.val = aesBlock alg key (bvs block.val) ⦄ := by
  obtain ⟨e, he⟩ := he
  unfold mid.aes.Aes.encrypt_block
  simp only [he, bind_ok, lift, low.ct.secret_slice, low.ct.public_slice, aes_encrypt alg key k hk,
    WP.spec_ok]
  rw [store_bytes, aesBlock]

/-! ## The header-protection API, through the modelled dispatch -/

/-- An AES header-protection key is refused unless it is the algorithm's
length, and otherwise holds FIPS 197's round keys for its bytes. -/
theorem aes_header_new (h : RunsAesHw) (alg : Algorithm) (algorithm : aead.quic.Algorithm)
    (halg : (algorithm = aead.quic.AES_128 ∧ alg = .AES_128) ∨
      (algorithm = aead.quic.AES_256 ∧ alg = .AES_256))
    (key : Slice U8) :
    aead.quic.HeaderProtectionKey.new algorithm key ⦃ r =>
      if key.length = 4 * nk alg then ∃ k, r = .Ok (.Aes k) ∧ AesIs alg (bvs key.val) k
      else r = .Err .WrongLength ⦄ := by
  have hnew : ∃ c : cipher.Algorithm, c.key_len.val = 4 * nk alg ∧ algorithm.new = (fun key => do
      let r ← mid.aes.Aes.new c key
      match r with
      | .Ok a =>
        let m ← aead.quic.Masker.new a
        ok (.Ok (.Aes m))
      | .Err e => ok (.Err e)) := by
    rcases halg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨cipher.AES_128, rfl, rfl⟩
    · exact ⟨cipher.AES_256, rfl, rfl⟩
  obtain ⟨c, hc, hn⟩ := hnew
  have hx : algorithm.new key ⦃ r =>
      if key.length = 4 * nk alg then ∃ k, r = .Ok (.Aes k) ∧ AesIs alg (bvs key.val) k
      else r = .Err .WrongLength ⦄ := by
    rw [hn]
    apply WP.spec_bind (aes_new h alg c hc key)
    intro r hr
    by_cases hk : key.length = 4 * nk alg
    · rw [ite_eq_left hk] at hr
      obtain ⟨k, rfl, hk'⟩ := hr
      simp [aead.quic.Masker.new, WP.spec_ok, hk, hk']
    · rw [ite_eq_right hk] at hr
      subst hr
      simp [WP.spec_ok, hk]
  unfold aead.quic.HeaderProtectionKey.new
  apply WP.spec_bind hx
  intro r hr
  rcases r with k | e <;> exact (WP.spec_ok _).2 hr

/-- An AES header-protection key's mask for a sample: RFC 9001's, the first
five bytes of FIPS 197's cipher of the sample under the key. -/
theorem aes_header_mask (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (key : List (BitVec 8)) (k : mid.aes.Aes) (hk : AesIs alg key k) (sample : Std.Array U8 16#usize) :
    aead.quic.HeaderProtectionKey.mask (.Aes k) sample ⦃ mask =>
      bvs mask.val = aesHeaderMask alg key (bvs sample.val) ⦄ := by
  obtain ⟨e, he⟩ := he
  unfold aead.quic.HeaderProtectionKey.mask aead.quic.Masker.mask
  simp only [mid.aes.Aes.Insts.RindAeadQuicMask.mask]
  unfold mid.aes.Aes.header_protection_mask low.ct.public_slice
  simp only [he, bind_ok, aes_encrypt alg key k hk]
  have hl : (storeBytes (aesEncrypt alg (seqNat8ToSeqNat32LE key)
      (leBytesToQuad32 (bvs sample.val)))).val.length = 16 := (storeBytes _).property
  step*
  rw [aesHeaderMask, aesBlock, ← store_bytes]
  apply List.ext_getElem (by simp [Std.Array.make, bvs, hl])
  intro j hj _
  have hj5 : j < 5 := by simpa [Std.Array.make, bvs] using hj
  obtain rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  all_goals simp [Std.Array.make, bvs, i_post, i1_post, i2_post, i3_post, i4_post]

end rind.x86_64
