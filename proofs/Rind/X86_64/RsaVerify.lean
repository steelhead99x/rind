import Rind.X86_64.RsaBytes
import Rind.X86_64.Hmac
import Rind.X86_64.Sha512
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# RSA signature verification on x86_64

`VerifyingKey`'s PKCS#1 v1.5 and PSS verification are RFC 8017's
RSASSA-PKCS1-V1_5-VERIFY and RSASSA-PSS-VERIFY, as `Rind.Rsa` transliterates
them, for a key `RsaPublicKey::new` accepted (`PubKeyInv`) and Montgomery
products that return their results (`MontProducts`).
-/

namespace rind.x86_64

theorem len_bits_spec (p : RsaInt) (hu : p.used.val ≤ 128) :
    low.posint.PosInt.len_bits p ⦃ r => r.val = (wordsNat (lowWords p p.used)).size ⦄ := by
  unfold low.posint.PosInt.len_bits low.posint.PosInt.as_words
  step*
  rw [r_post, s_post]
  simp [lowWords, List.slice, Array.val_to_slice]

/-- The modulus's length in bytes is RFC 8017's `k`. -/
theorem modulus_len_bytes_spec (key : mid.rsa_pub.RsaPublicKey) (hinv : PubKeyInv key) :
    mid.rsa_pub.RsaPublicKey.modulus_len_bytes key ⦃ r =>
      r.val = octetLen (wordsNat (lowWords key.n key.n.used)) ⦄ := by
  obtain ⟨-, hk, -, -, -, -, -, -, hs2⟩ := hinv
  unfold mid.rsa_pub.RsaPublicKey.modulus_len_bytes low.posint.PosInt.len_bytes
  step with len_bits_spec key.n hk as ⟨b, hb⟩
  step*
  rw [r_post, i1_post, core.num.Usize.wrapping_add_val_eq, hb, octetLen]
  congr 1
  rw [Nat.mod_eq_of_lt]
  · rfl
  rw [← hb] at hs2 ⊢
  have : (7#usize).val = 7 := rfl
  have : 2 ^ 32 ≤ UScalar.size UScalarTy.Usize := by
    simp only [UScalar.size, UScalarTy.numBits]
    cases System.Platform.numBits_eq <;> simp_all
  omega

theorem rsa_slice_eq_spec (s t : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s t ⦃ b => b ↔ s.val = t.val ⦄ := by
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec _ s t
    (fun x y => by simp [liftFun2]))
  intro b hb
  rw [hb, Slice.eq_iff]

/-- `k` bytes hold any number below the modulus. -/
theorem lt_octetLen (N x : Nat) (hx : x < N) : x < 256 ^ octetLen N := by
  calc x < N := hx
    _ < 2 ^ N.size := Nat.lt_size_self N
    _ ≤ 2 ^ (8 * octetLen N) := Nat.pow_le_pow_right (by norm_num) (by unfold octetLen; omega)
    _ = 256 ^ octetLen N := by rw [pow_mul]; norm_num

theorem bv_pkcs1 (n : Nat) (di h : List U8) :
    bv ([0#u8, 1#u8] ++ List.replicate n 255#u8 ++ [0#u8] ++ di ++ h) =
      [0x00, 0x01] ++ List.replicate n 0xff ++ [0x00] ++ (bv di ++ bv h) := by
  simp [bv, List.map_replicate]

/-- RSASSA-PKCS1-V1_5-VERIFY of a signature of the right length below the
modulus: whether its representative's encoding is the expected one. -/
theorem pkcs1_verify_iff (N e : Nat) (H : List Byte → List Byte) (di M : List Byte) (sig : List U8)
    (hlen : sig.length = octetLen N) (hCN : beNat sig < N) (mb : List U8) (hmb : mb.length = octetLen N)
    (hmv : beNat mb = beNat sig ^ e % N) (EM : List U8)
    (hEM : emsaPkcs1v15Encode H di M (octetLen N) = some (bv EM)) :
    rsassaPkcs1v15Verify N e H di M (bv sig) ↔ EM = mb := by
  have hi : i2osp (beNat sig ^ e % N) (octetLen N) = some (bv mb) := by rw [← hmv, ← hmb, i2osp_beNat]
  unfold rsassaPkcs1v15Verify rsavp1
  dsimp only
  rw [os2ip_bv, ite_cond_eq_true _ _ (eq_true hCN)]
  simp only [Option.some.injEq, exists_eq_left']
  rw [hi, hEM]
  have hl : (bv sig).length = octetLen N := by simp [bv, hlen]
  simp only [hl, Option.some.injEq, exists_eq_left', true_and]
  rw [bv_inj]

/-- A signature representative at or above the modulus verifies nothing. -/
theorem pkcs1_verify_out_of_range (N e : Nat) (H : List Byte → List Byte) (di M : List Byte)
    (sig : List U8) (hCN : N ≤ beNat sig) : ¬ rsassaPkcs1v15Verify N e H di M (bv sig) := by
  unfold rsassaPkcs1v15Verify rsavp1
  rw [os2ip_bv, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  simp

/-- RSASSA-PKCS1-V1_5-VERIFY, given the message's hash and its `DigestInfo`
prefix: `_verify_pkcs1` accepts exactly the signatures RFC 8017 does. -/
theorem verify_pkcs1_core_spec (key : high.rsa.VerifyingKey) (hinv : PubKeyInv key)
    (hP : MontProducts key.n.used.val) (signature digest_info hash : Slice U8)
    (hT : digest_info.length + hash.length + 11 ≤ 128) (H : List Byte → List Byte) (M : List Byte)
    (hH : H M = bv hash.val) :
    high.rsa.VerifyingKey._verify_pkcs1 key signature digest_info hash ⦃ r =>
      r = .Ok () ↔ rsassaPkcs1v15Verify (wordsNat (lowWords key.n key.n.used)) key.e.val H
        (bv digest_info.val) M (bv signature.val) ⦄ := by
  have hinv' := hinv
  obtain ⟨hk2, hk, hodd, hn0, hmont, he, he3, hs1, hs2⟩ := hinv'
  unfold high.rsa.VerifyingKey._verify_pkcs1
  step with modulus_len_bytes_spec key hinv as ⟨k, hkv⟩
  have hk128 : 128 ≤ k.val := by rw [hkv, octetLen]; omega
  have hk1024 : k.val ≤ 1024 := by rw [hkv, octetLen]; omega
  have hsL : signature.length = signature.val.length := rfl
  split
  · rename_i hne
    simp only [WP.spec_ok]
    refine ⟨by simp, fun h => ?_⟩
    obtain ⟨hl, -⟩ := h
    simp only [bv, List.length_map] at hl
    have : signature.len = k := by
      rw [UScalar.eq_equiv, hkv, ← hl]; rfl
    simp [this] at hne
  · rename_i heq
    have hlen : signature.length = k.val := by simpa [UScalar.eq_equiv] using heq
    step with posint_from_bytes_spec signature (beNat_lt_8192 _ (by omega)) as ⟨r, c, hr, hcu, hcz, hcv, _⟩
    subst hr
    simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have hC : wordsNat (lowWords c c.used) = beNat signature.val := hcv
    step with public_op_spec key hinv hP c hcu hcz as ⟨r2, hr2⟩
    cases r2 with
    | Err e =>
      simp only at hr2
      rw [hC] at hr2
      simp [high.rsa.VerifyingKey._verify_pkcs1.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      exact pkcs1_verify_out_of_range _ _ _ _ _ _ hr2
    | Ok m =>
      obtain ⟨hCN, hmu, hmv⟩ := hr2
      rw [hC] at hCN hmv
      step as ⟨mb1, _b1, hmb1, hmb1l, _⟩
      have hX : wordsNat (lowWords m m.used) < 256 ^ mb1.length := by
        rw [hmu, hmv, hmb1l, hkv]; exact lt_octetLen _ _ (Nat.mod_lt _ (by omega))
      step with i2osp_spec m mb1 (by rw [hmu]; exact hk) as ⟨r4, mb2, hi, _⟩
      obtain ⟨hr4, hmb2l, hmb2v⟩ := hi hX
      subst hr4
      simp only [bind_ok]
      step as ⟨am1, _b2, ham1, ham1l, _⟩
      step with encode_pkcs1_sig_spec am1 digest_info hash (by omega) as ⟨am2, ham2⟩
      simp only [Mut1A.Insts.CoreCmpPartialEqMut0B.eq]
      step with rsa_slice_eq_spec am2 mb2 as ⟨b, hb⟩
      have hiff := pkcs1_verify_iff (wordsNat (lowWords key.n key.n.used)) key.e.val H (bv digest_info.val) M
        signature.val (by rw [← hsL, hlen, hkv]) hCN mb2.val (by rw [← Slice.length, hmb2l, hmb1l, hkv])
        (by rw [hmb2v, hmu, hmv]) am2.val (by
          unfold emsaPkcs1v15Encode
          have hTl : (bv digest_info.val ++ H M).length = digest_info.length + hash.length := by
            simp [hH, bv]
          dsimp only
          rw [hTl, ← hkv, ite_cond_eq_false _ _ (eq_false (by omega)), ham2, ham1l, hH, bv_pkcs1])
      split
      · rename_i hbt
        simp only [WP.spec_ok, true_iff]
        rw [hiff]; exact hb.mp hbt
      · rename_i hbf
        simp only [WP.spec_ok, reduceCtorEq, false_iff]
        rw [hiff]; intro h; exact hbf (hb.mpr h)

/-! ## Over each hash -/

section
variable {Self C S : Type} {inst : high.hash.Hash Self C S} {H : List Byte → List Byte}
  {B L max : Nat} {Abs : List U8 → S → Prop} {CAbs : List U8 → C → Prop}

/-- RSASSA-PKCS1-V1_5-VERIFY over a hash meeting `HashSpec`, as each
`verify_pkcs1_*` runs it after taking the entry guard. -/
theorem verify_pkcs1_hash_spec (hs : HashSpec inst H B L max Abs CAbs) (key : high.rsa.VerifyingKey)
    (hinv : PubKeyInv key) (hP : MontProducts key.n.used.val) (signature message di : Slice U8)
    (hm : message.length ≤ max) (hdi : di.length + L + 11 ≤ 128) :
    (do
      let hash ← high.hash.Hash.hash.default inst message
      let s ← high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref hash
      high.rsa.VerifyingKey._verify_pkcs1 key signature di s) ⦃ r =>
      r = .Ok () ↔ rsassaPkcs1v15Verify (wordsNat (lowWords key.n key.n.used)) key.e.val H
        (bv di.val) (bv message.val) (bv signature.val) ⦄ := by
  have hh := hs.hash_spec message hm
  rw [hs.hash_default] at hh
  step with hh as ⟨d, hdl, hdv⟩
  step with digest_as_ref_spec d as ⟨s, hsl, hsv⟩
  exact verify_pkcs1_core_spec key hinv hP signature di s (by omega) H (bv message.val) (by rw [hsv, hdv])

end

theorem digestinfo_sha1 : bv high.pkcs1.DIGESTINFO_SHA1.val = digestInfoSha1 ∧
    high.pkcs1.DIGESTINFO_SHA1.length = 15 := by
  unfold high.pkcs1.DIGESTINFO_SHA1
  simp [bv, digestInfoSha1, Array.val_to_slice, Slice.length]

theorem digestinfo_sha256 : bv high.pkcs1.DIGESTINFO_SHA256.val = digestInfoSha256 ∧
    high.pkcs1.DIGESTINFO_SHA256.length = 19 := by
  unfold high.pkcs1.DIGESTINFO_SHA256
  simp [bv, digestInfoSha256, Array.val_to_slice, Slice.length]

theorem digestinfo_sha384 : bv high.pkcs1.DIGESTINFO_SHA384.val = digestInfoSha384 ∧
    high.pkcs1.DIGESTINFO_SHA384.length = 19 := by
  unfold high.pkcs1.DIGESTINFO_SHA384
  simp [bv, digestInfoSha384, Array.val_to_slice, Slice.length]

theorem digestinfo_sha512 : bv high.pkcs1.DIGESTINFO_SHA512.val = digestInfoSha512 ∧
    high.pkcs1.DIGESTINFO_SHA512.length = 19 := by
  unfold high.pkcs1.DIGESTINFO_SHA512
  simp [bv, digestInfoSha512, Array.val_to_slice, Slice.length]

/-- RSASSA-PKCS1-V1_5-VERIFY with SHA-256. -/
theorem verify_pkcs1_sha256_spec (h : Runs) (hb : Sha256Blocks) (key : high.rsa.VerifyingKey)
    (hinv : PubKeyInv key) (hP : MontProducts key.n.used.val) (signature message : Slice U8)
    (hm : message.length ≤ maxInput) :
    high.rsa.VerifyingKey.verify_pkcs1_sha256 key signature message ⦃ r =>
      r = .Ok () ↔ rsassaPkcs1v15Verify (wordsNat (lowWords key.n key.n.used)) key.e.val sha256.hash
        digestInfoSha256 (bv message.val) (bv signature.val) ⦄ := by
  unfold high.rsa.VerifyingKey.verify_pkcs1_sha256
  step with new_public_spec h
  rw [← digestinfo_sha256.1]
  exact verify_pkcs1_hash_spec (sha256_hashSpec hb) key hinv hP signature message _ hm
    (by rw [digestinfo_sha256.2]; norm_num)

/-- RSASSA-PKCS1-V1_5-VERIFY with SHA-1. -/
theorem verify_pkcs1_sha1_spec (h : Runs) (hb : Sha1Blocks) (key : high.rsa.VerifyingKey)
    (hinv : PubKeyInv key) (hP : MontProducts key.n.used.val) (signature message : Slice U8)
    (hm : message.length ≤ maxInput) :
    high.rsa.VerifyingKey.verify_pkcs1_sha1 key signature message ⦃ r =>
      r = .Ok () ↔ rsassaPkcs1v15Verify (wordsNat (lowWords key.n key.n.used)) key.e.val sha1.hash
        digestInfoSha1 (bv message.val) (bv signature.val) ⦄ := by
  unfold high.rsa.VerifyingKey.verify_pkcs1_sha1
  step with new_public_spec h
  rw [← digestinfo_sha1.1]
  exact verify_pkcs1_hash_spec (sha1_hashSpec hb) key hinv hP signature message _ hm
    (by rw [digestinfo_sha1.2]; norm_num)

/-- RSASSA-PKCS1-V1_5-VERIFY with SHA-384. -/
theorem verify_pkcs1_sha384_spec (h : Runs) (hs : RunsSha512) (key : high.rsa.VerifyingKey)
    (hinv : PubKeyInv key) (hP : MontProducts key.n.used.val) (signature message : Slice U8)
    (hm : message.length ≤ maxInput) :
    high.rsa.VerifyingKey.verify_pkcs1_sha384 key signature message ⦃ r =>
      r = .Ok () ↔ rsassaPkcs1v15Verify (wordsNat (lowWords key.n key.n.used)) key.e.val sha384Bytes
        digestInfoSha384 (bv message.val) (bv signature.val) ⦄ := by
  unfold high.rsa.VerifyingKey.verify_pkcs1_sha384
  step with new_public_spec h
  rw [← digestinfo_sha384.1]
  exact verify_pkcs1_hash_spec (sha384_hashSpec hs) key hinv hP signature message _ hm
    (by rw [digestinfo_sha384.2]; norm_num)

/-- RSASSA-PKCS1-V1_5-VERIFY with SHA-512. -/
theorem verify_pkcs1_sha512_spec (h : Runs) (hs : RunsSha512) (key : high.rsa.VerifyingKey)
    (hinv : PubKeyInv key) (hP : MontProducts key.n.used.val) (signature message : Slice U8)
    (hm : message.length ≤ maxInput) :
    high.rsa.VerifyingKey.verify_pkcs1_sha512 key signature message ⦃ r =>
      r = .Ok () ↔ rsassaPkcs1v15Verify (wordsNat (lowWords key.n key.n.used)) key.e.val sha512Bytes
        digestInfoSha512 (bv message.val) (bv signature.val) ⦄ := by
  unfold high.rsa.VerifyingKey.verify_pkcs1_sha512
  step with new_public_spec h
  rw [← digestinfo_sha512.1]
  exact verify_pkcs1_hash_spec (sha512_hashSpec hs) key hinv hP signature message _ hm
    (by rw [digestinfo_sha512.2]; norm_num)

end rind.x86_64
