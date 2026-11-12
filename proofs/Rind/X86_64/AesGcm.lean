import Rind.X86_64.AesGcmGlue
import Rind.X86_64.AesCipher
import Rind.X86_64.Ghash
import Rind.X86_64.AeadDispatch
open Aeneas Aeneas.Std Result rind.vale rind.simd

namespace rind.x86_64

/-- rind runs Vale's AES-GCM on this CPU: its entry guard passes, and its
CPU-feature checks find AES-NI, PCLMULQDQ, AVX, and MOVBE, but neither tier
with VAES. None reads an input. -/
def RunsValeAesGcm : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧
  (∃ hw, low.x86_64.cpu.HaveAesHardware.check = ok (some hw)) ∧
  (∃ s, low.x86_64.cpu.HaveSsse3.check = ok s) ∧
  low.x86_64.cpu.HaveAvx512ForAesGcm.check = ok none ∧
  low.x86_64.cpu.HaveVaesAvx2ForAesGcm.check = ok none ∧
  (∃ t, low.x86_64.cpu.HaveAvxMovbeForAesGcm.check = ok (some t))

theorem RunsValeAesGcm.aesNi (h : RunsValeAesGcm) : RunsAesHw :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- An AES-GCM key on Vale's tier, for the AES key `kw` and `alg`. -/
def Ready (alg : Algorithm) (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) : Prop :=
  ∃ hk table kernel, g.key = .Hw hk ∧ g.gh = .Avx table kernel ∧ KernelKeys alg hk kw kernel

theorem encrypt_zero (hk : low.x86_64.aes.HwKey) (alg : Algorithm) (kw : List (BitVec 32))
    (h : HwKeyIs alg kw hk) :
    low.x86_64.aes.AesKey.encrypt_block (.Hw hk) (Std.Array.repeat 16#usize 0#u8) =
      ok (storeBytes (aesEncrypt alg kw (mkfour 0 0 0 0))) := by
  rw [hw_encrypt_block hk alg kw h, load_zero]

@[step]
theorem public_slice_spec {T : Type} (s : Slice T) : low.ct.public_slice s ⦃ _ => True ⦄ := by
  simp [low.ct.public_slice, WP.spec_ok]

@[step]
theorem check_gcm_lengths_spec (aad msg : Usize) (haad : aad.val < 2 ^ 61) (hmsg : msg.val ≤ 2 ^ 36 - 32) :
    mid.aes.check_gcm_lengths aad msg ⦃ r => r = .Ok () ⦄ := by
  unfold mid.aes.check_gcm_lengths mid.aes.check_counter core.num.Usize.div_ceil
  step*
  rw [dite_eq_right (by decide)]
  simp only [lift, bind_ok]
  step*

/-- `aes_gcm::seal` and `open` run Vale's routines for a key on its tier and
lengths under 2^32, and `seal` only for messages of at least 129 bytes. -/
theorem vale_some (enc : Bool) (alg : Algorithm) (kw : List (BitVec 32)) (key : low.x86_64.aes.AesKey)
    (gh : low.x86_64.ghash.GhashTable) (hg : Ready alg kw ⟨key, gh⟩)
    (aad inout : Slice U8) (haad : aad.length < 2 ^ 32) (hin : inout.length < 2 ^ 32)
    (hlong : enc = true → 129 ≤ inout.length) :
    low.x86_64.aes_gcm.vale enc key gh aad inout ⦃ o =>
      ∃ hk kernel, o = some (hk, kernel) ∧ KernelKeys alg hk kw kernel ⦄ := by
  obtain ⟨hk, table, kernel, hkey, hgh, hkk⟩ := hg
  simp only at hkey hgh
  subst hkey hgh
  unfold low.x86_64.aes_gcm.vale
  cases hk with
  | Aes128 k =>
    cases enc <;> step*
    simp_all [low.x86_64.aes_gcm.AVX_VALE_SEAL_FROM]
  | Aes192 k => exact hkk.2.1.elim
  | Aes256 k =>
    cases enc <;> step*
    simp_all [low.x86_64.aes_gcm.AVX_VALE_SEAL_FROM]

/-- `AesGcm::encrypt` on Vale's tier, for AAD under 2^32 bytes and messages
of 129 bytes to 2^32: the ciphertext in place and the tag are AES-GCM's. -/
theorem aes_gcm_encrypt_vale (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) (hg : Ready alg kw g)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (haad : aad.length < 2 ^ 32) (hin : inout.length < 2 ^ 32) (hlong : 129 ≤ inout.length) :
    mid.aes_gcm.AesGcm.encrypt g nonce aad inout tag ⦃ r =>
      r.1 = .Ok () ∧ r.2.1.length = inout.length ∧ (bvs r.2.1.val, bvs r.2.2.val) =
        gcmEncrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val) ⦄ := by
  obtain ⟨e, he⟩ := he
  obtain ⟨key, gh⟩ := g
  unfold mid.aes_gcm.AesGcm.encrypt low.x86_64.aes_gcm.seal
  rw [he, bind_ok]
  step*
  · apply WP.spec_bind (vale_some true alg kw key gh hg aad inout haad hin fun _ => hlong)
    rintro _ ⟨hk, kernel, rfl, hkk⟩
    simp only [low.x86_64.aes_gcm_avx.AvxKernel.seal]
    step with cipher_encrypt_spec alg hk kw kernel hkk nonce aad inout _ haad hin as ⟨res, hres⟩
    obtain ⟨_, out, t⟩ := res
    step*

/-- `AesGcm::decrypt` on Vale's tier, for AAD and messages under 2^32 bytes:
it succeeds exactly when the tag is AES-GCM's, leaving the plaintext in place,
and otherwise fails, leaving zeros. -/
theorem aes_gcm_decrypt_vale (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (kw : List (BitVec 32)) (g : mid.aes_gcm.AesGcm) (hg : Ready alg kw g)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (haad : aad.length < 2 ^ 32) (hin : inout.length < 2 ^ 32) :
    mid.aes_gcm.AesGcm.decrypt g nonce aad inout tag ⦃ r =>
      let out := gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val)
        (bvs tag.val)
      if out.2 then r.1 = .Ok () ∧ bvs r.2.val = out.1
      else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate inout.length 0#u8 ⦄ := by
  obtain ⟨e, he⟩ := he
  obtain ⟨key, gh⟩ := g
  unfold mid.aes_gcm.AesGcm.decrypt low.x86_64.aes_gcm.open
  rw [he, bind_ok]
  step*
  · apply WP.spec_bind (vale_some false alg kw key gh hg aad inout haad hin nofun)
    rintro _ ⟨hk, kernel, rfl, hkk⟩
    simp only [low.x86_64.aes_gcm_avx.AvxKernel.open]
    step with cipher_decrypt_spec alg hk kw kernel hkk nonce aad inout tag haad hin as ⟨res, hlen, hout, hok⟩
    obtain ⟨i, out, t⟩ := res
    simp only at hlen hout hok
    simp only [low.ct.into_public, bind_ok]
    by_cases hi : i = 0#u64
    · have h2 : (gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val)
          (bvs tag.val)).2 = true := hok.1 (by rw [hi]; rfl)
      simp only [hi, ite_true, h2]
      step*
    · have h2 : (gcmDecrypt alg (seqNat32ToSeqNat8LE kw) (bvs nonce.val) (bvs inout.val) (bvs aad.val)
          (bvs tag.val)).2 = false := by
        rw [Bool.eq_false_iff]; intro h; exact hi (by scalar_tac)
      simp only [Bool.false_eq_true, ite_false, h2]
      step*

end rind.x86_64
