import Rind.X86_64.AesKey
import Rind.X86_64.Dispatch
import Rind.X86_64.ValeAesGcm
open Aeneas Aeneas.Std Result rind.vale

/-!
# `cipher::Aes` and AES header protection on AES-NI

`Aes::new` expands a key with rind's AES-NI key expansion, which
`Rind.X86_64.AesKey` proves computes FIPS 197's round keys as Vale's AES spec
lays them out, and `encrypt_block` and `header_protection_mask` run its AES-NI
block cipher, which the same file proves is Vale's `aes_encrypt_LE`. These
theorems compose the two through `mid::aes` and, for header protection, through
`Rind.X86_64.Dispatch`'s model of `aead::quic`'s dispatch. AES-128 and AES-256
alone: AES-192's key expansion and block cipher stay opaque.
-/

namespace rind.x86_64

/-- FIPS 197's cipher of the 16 bytes `block` under the key bytes `key`, as
Vale's `aes_encrypt_LE` reads both, little-endian. -/
def aesBlock (alg : Algorithm) (key block : List (BitVec 8)) : List (BitVec 8) :=
  leQuad32ToBytes (aesEncrypt alg (seqNat8ToSeqNat32LE key) (leBytesToQuad32 block))

/-- RFC 9001's AES header-protection mask: the first five bytes of the sample's
AES cipher under the header-protection key. -/
def aesHeaderMask (alg : Algorithm) (key sample : List (BitVec 8)) : List (BitVec 8) :=
  (aesBlock alg key sample).take 5

-- RFC 9001's appendix A.2: the client's Initial header-protection mask. Lean
-- evaluates the S-box and `MixColumns` that proofs keep opaque, so these check
-- the specs above against known answers.
#guard aesHeaderMask .AES_128
  ([0x9f, 0x50, 0x44, 0x9e, 0x04, 0xa0, 0xe8, 0x10, 0x28, 0x3a, 0x1e, 0x99, 0x33, 0xad, 0xed, 0xd2] : List (BitVec 8))
  [0xd1, 0xb1, 0xc9, 0x8d, 0xd7, 0x68, 0x9f, 0xb8, 0xec, 0x11, 0xd2, 0x42, 0xb1, 0x23, 0xdc, 0x9b] ==
  [0x43, 0x7b, 0x9a, 0xec, 0x36]

-- FIPS 197's appendix C.3: AES-256 of `00112233...ff`.
#guard aesBlock .AES_256 ((List.range 32).map fun i => BitVec.ofNat 8 i)
  ((List.range 16).map fun i => BitVec.ofNat 8 (17 * i)) ==
  [0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60, 0x89]

/-- rind runs its AES-NI key expansion and block cipher on this CPU: its entry
guard passes, and its CPU-feature checks find AES-NI, PCLMULQDQ, SSSE3, and
SSE4.1. None reads an input. -/
def RunsAesNi : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧
  (∃ hw, low.x86_64.cpu.HaveAesHardware.check = ok (some hw)) ∧
  (∃ s, low.x86_64.cpu.HaveSsse3.check = ok s)

@[step]
theorem aes128_expand_step (key : Std.Array U8 16#usize) (out : Std.Array core.core_arch.x86.__m128i 11#usize) :
    low.x86_64.aes.aes128_expand key out ⦃ rk =>
      rk.val = keyToRoundKeys .AES_128 (seqNat8ToSeqNat32LE (bvs key.val)) ⦄ := by
  obtain ⟨rk, h, hv⟩ := aes128_expand_spec key out
  rw [h, WP.spec_ok]; exact hv

@[step]
theorem aes256_expand_step (key : Std.Array U8 32#usize) (out : Std.Array core.core_arch.x86.__m128i 15#usize) :
    low.x86_64.aes.aes256_expand key out ⦃ rk =>
      rk.val = keyToRoundKeys .AES_256 (seqNat8ToSeqNat32LE (bvs key.val)) ⦄ := by
  obtain ⟨rk, h, hv⟩ := aes256_expand_spec key out
  rw [h, WP.spec_ok]; exact hv

theorem expand_key128_spec (h : RunsAesNi) (key : Slice U8) (hk : key.length = 16) :
    mid.aes.expand_key key ⦃ k => ∃ k128, k = .Hw (.Aes128 k128) ∧
      k128.round_keys.val = keyToRoundKeys .AES_128 (seqNat8ToSeqNat32LE (bvs key.val)) ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩, ⟨ss, hss⟩⟩ := h
  unfold mid.aes.expand_key low.x86_64.aes.AesKey.new low.x86_64.aes.AesKey128.new
  step*
  have hl : copy_key1.len.val = 16 := by rw [Slice.len_val, copy_key1_post]; exact hk
  have hl' : copy_key1.len = 16#usize := by scalar_tac
  simp only [low.ct.secret_slice, hhw, hss, bind_ok, core.array.TryFromSharedArraySlice.try_from,
    hl', ↓reduceDIte, core.result.Result.unwrap, low.x86_64.aes.zero,
    core.core_arch.x86.sse2._mm_setzero_si128]
  apply WP.spec_bind (aes128_expand_step _ _)
  intro rk hrk
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [hrk, Std.Array.from_val, copy_key1_post]

theorem expand_key256_spec (h : RunsAesNi) (key : Slice U8) (hk : key.length = 32) :
    mid.aes.expand_key key ⦃ k => ∃ k256, k = .Hw (.Aes256 k256) ∧
      k256.round_keys.val = keyToRoundKeys .AES_256 (seqNat8ToSeqNat32LE (bvs key.val)) ⦄ := by
  obtain ⟨-, ⟨hw, hhw⟩, ⟨ss, hss⟩⟩ := h
  unfold mid.aes.expand_key low.x86_64.aes.AesKey.new low.x86_64.aes.AesKey256.new
  step*
  have hl : copy_key1.len.val = 32 := by rw [Slice.len_val, copy_key1_post]; exact hk
  have hl' : copy_key1.len = 32#usize := by scalar_tac
  simp only [low.ct.secret_slice, hhw, hss, bind_ok, core.array.TryFromSharedArraySlice.try_from,
    hl', ↓reduceDIte, core.result.Result.unwrap, low.x86_64.aes.zero,
    core.core_arch.x86.sse2._mm_setzero_si128]
  apply WP.spec_bind (aes256_expand_step _ _)
  intro rk hrk
  rw [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [hrk, Std.Array.from_val, copy_key1_post]

/-- The AES-NI key holds Vale's round keys of the AES key `kw` for `alg`. -/
def HwKeyIs (alg : Algorithm) (kw : List (BitVec 32)) : low.x86_64.aes.HwKey → Prop
  | .Aes128 k => alg = .AES_128 ∧ k.round_keys.val = keyToRoundKeys .AES_128 kw
  | .Aes192 _ => False
  | .Aes256 k => alg = .AES_256 ∧ k.round_keys.val = keyToRoundKeys .AES_256 kw

/-- The key length `alg` takes, which rind's AES supports. -/
def KeyLen (alg : Algorithm) (n : Nat) : Prop :=
  (alg = .AES_128 ∧ n = 16) ∨ (alg = .AES_256 ∧ n = 32)


theorem hw_encrypt_block (hk : low.x86_64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (h : HwKeyIs alg kw hk) (b : Std.Array U8 16#usize) :
    low.x86_64.aes.AesKey.encrypt_block (.Hw hk) b =
      ok (low.x86_64.aes.store (aesEncrypt alg kw (low.x86_64.aes.load b.val))) := by
  cases hk with
  | Aes128 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.x86_64.aes.AesKey.encrypt_block, low.x86_64.aes.HwKey.encrypt_block,
      low.x86_64.aes.AesKey128.encrypt_block, aes128_block_spec, hrk, aesEncrypt]
  | Aes192 k => exact h.elim
  | Aes256 k =>
    obtain ⟨rfl, hrk⟩ := h
    simp only [low.x86_64.aes.AesKey.encrypt_block, low.x86_64.aes.HwKey.encrypt_block,
      low.x86_64.aes.AesKey256.encrypt_block, aes256_block_spec, hrk, aesEncrypt]

theorem store_bytes (q : BitVec 128) : bvs (low.x86_64.aes.store q).val = leQuad32ToBytes q := by
  simp [low.x86_64.aes.store, Std.Array.from_val, Function.comp_def, bvs]

/-- An AES key holding FIPS 197's round keys for the key bytes `key`, which
`alg` sizes, on AES-NI. -/
def AesIs (alg : Algorithm) (key : List (BitVec 8)) (k : mid.aes.Aes) : Prop :=
  key.length = 4 * nk alg ∧ ∃ hk, k = .Hw hk ∧ HwKeyIs alg (seqNat8ToSeqNat32LE key) hk

theorem aes_encrypt (alg : Algorithm) (key : List (BitVec 8)) (k : mid.aes.Aes) (hk : AesIs alg key k)
    (b : Std.Array U8 16#usize) :
    low.x86_64.aes.AesKey.encrypt_block k b =
      ok (low.x86_64.aes.store (aesEncrypt alg (seqNat8ToSeqNat32LE key) (leBytesToQuad32 (bvs b.val)))) := by
  obtain ⟨-, hwk, rfl, hwk_is⟩ := hk
  exact hw_encrypt_block hwk alg _ hwk_is b

/-- A `cipher::Aes` key is refused unless it is the algorithm's length, and
otherwise holds FIPS 197's round keys for its bytes. -/
theorem aes_new (h : RunsAesNi) (alg : Algorithm) (algorithm : cipher.Algorithm)
    (halg : KeyLen alg algorithm.key_len.val) (key : Slice U8) :
    mid.aes.Aes.new algorithm key ⦃ r =>
      if key.length = 4 * nk alg then ∃ k, r = .Ok k ∧ AesIs alg (bvs key.val) k
      else r = .Err .WrongLength ⦄ := by
  have hlen : algorithm.key_len.val = 4 * nk alg := by
    rcases halg with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp [h, nk]
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
      rcases halg with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact WP.spec_mono (expand_key128_spec h key (by simpa [nk] using hk))
          fun k ⟨k128, hk1, hk2⟩ => ⟨_, hk1, rfl, hk2⟩
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
theorem aes_header_new (h : RunsAesNi) (alg : Algorithm) (algorithm : aead.quic.Algorithm)
    (halg : (algorithm = aead.quic.AES_128 ∧ alg = .AES_128) ∨
      (algorithm = aead.quic.AES_256 ∧ alg = .AES_256))
    (key : Slice U8) :
    aead.quic.HeaderProtectionKey.new algorithm key ⦃ r =>
      if key.length = 4 * nk alg then ∃ k, r = .Ok (.Aes k) ∧ AesIs alg (bvs key.val) k
      else r = .Err .WrongLength ⦄ := by
  have hnew : ∃ c : cipher.Algorithm, KeyLen alg c.key_len.val ∧ algorithm.new = (fun key => do
      let r ← mid.aes.Aes.new c key
      match r with
      | .Ok a =>
        let m ← aead.quic.Masker.new a
        ok (.Ok (.Aes m))
      | .Err e => ok (.Err e)) := by
    rcases halg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨cipher.AES_128, Or.inl ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨cipher.AES_256, Or.inr ⟨rfl, rfl⟩, rfl⟩
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
  have hl : (low.x86_64.aes.store (aesEncrypt alg (seqNat8ToSeqNat32LE key)
      (leBytesToQuad32 (bvs sample.val)))).val.length = 16 := (low.x86_64.aes.store _).property
  step*
  rw [aesHeaderMask, aesBlock, ← store_bytes]
  apply List.ext_getElem (by simp [Std.Array.make, bvs, hl])
  intro j hj _
  have hj5 : j < 5 := by simpa [Std.Array.make, bvs] using hj
  obtain rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  all_goals simp [Std.Array.make, bvs, i_post, i1_post, i2_post, i3_post, i4_post]

end rind.x86_64
