import Rind.X86_64.P256KeyCheck
import Rind.X86_64.Ed25519
import Rind.X86_64.Hmac
open Aeneas Aeneas.Std Result rind.spec

/-!
# P-256 ECDSA through the signature API

The `p256_ecdsa_*` theorems state what the signature API returns for
`ECDSA_P256_SHA256_FIXED`, in terms of `Rind.Spec`'s ECDSA, through the
dispatch `Rind.X86_64.EcdsaDispatch` models, with SHA-256 as
`Rind.X86_64.Hmac` states it. A signing key checks its public key as
`Rind.X86_64.P256KeyCheck` states. `admin/prove` writes the aarch64 proof
from this file by renaming the target.
-/

namespace rind.x86_64

open P256

/-- A signing key whose private scalar is `d`, in [1, n). -/
def SigningKeyOf (key : P256SigningKey) (d : Nat) : Prop :=
  scNat key.private_key.scalar = d ∧ 0 < d ∧ d < n256

namespace P256

theorem static_public_key_uncompressed_spec (h : Runs) (k : mid.p256.StaticPrivateKey)
    (hk0 : 0 < scNat k.scalar) (hk : scNat k.scalar < n256) :
    mid.p256.StaticPrivateKey.public_key_uncompressed k ⦃ b => p256PublicKey (scNat k.scalar) b.val ⦄ := by
  obtain ⟨x, y, hq, hc⟩ := g_mult _ hk0 hk
  have := public_key_uncompressed_spec h k hk x y hq hc
  refine WP.spec_mono this fun b ⟨h4, hxy⟩ => ⟨b.property, h4, ?_⟩
  rw [hq, hxy]

/-- The build of a signing key's cached public key: X9.62's uncompressed
encoding of its scalar times G, in the first 65 bytes. -/
theorem point_build_spec (h : Runs) (key : P256SigningKey) (d : Nat) (hs : SigningKeyOf key d) :
    high.ecdsa.SigningKey.public_key_uncompressed.closure.Insts.CoreOpsFunctionFnOnceTupleEncodedPoint.call_once
      P256C key () ⦃ ep => ep.len.val = 65 ∧ p256PublicKey d (ep.bytes.val.take 65) ⦄ := by
  obtain ⟨hsd, hd0, hd⟩ := hs
  unfold high.ecdsa.SigningKey.public_key_uncompressed.closure.Insts.CoreOpsFunctionFnOnceTupleEncodedPoint.call_once
    high.ecdsa.EncodedPoint.Insts.CoreDefaultDefault.default
  simp only [mid.p256.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.public_key_encode_uncompressed]
  step*
  have hsl : s.length = 133 := by simp [Slice.length, s_post, Array.repeat]
  simp only [mid.p256.PublicKey.BYTES, mid.p256.FieldElement.BYTES, core.slice.Slice.get_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.get_mut]
  step*
  rw [ite_eq_left (by simp [hsl]; scalar_tac)]
  simp only [bind_ok]
  step with static_public_key_uncompressed_spec h key.private_key (hsd ▸ hd0) (hsd ▸ hd) as ⟨a, ha⟩
  have hx : x.val = 65 := by scalar_tac
  have ha65 : a.val.length = 65 := a.property
  have hcp : core.slice.Slice.copy_from_slice core.marker.CopyU8
      (Slice.from (List.slice (0#usize).val x.val s.val) (by simp [List.slice])) a.to_slice =
      ok a.to_slice := by
    simp [core.slice.Slice.copy_from_slice, Slice.len, List.slice, hx, hsl, ha65]
  simp only [lift, bind_ok, hcp, core.result.Result.expect, WP.spec_ok]
  have hl : a.to_slice.length = x.val - (0#usize).val := by simp [Slice.length, hx, ha65]
  simp only [hl, ↓reduceDIte, to_slice_mut_back_post]
  refine ⟨by simp [Slice.len, ha65], ?_⟩
  have hs : s.val.length = 133 := hsl
  rw [Array.from_slice_val _ _ (by simp [hs])]
  have := take_setSlice! s.val a.val 0 (by omega)
  simp only [Nat.zero_add, List.take_zero, List.nil_append, ha65] at this
  rw [← hsd]
  simpa [this] using ha

theorem signing_new_spec (hc : Cached) (k : mid.p256.StaticPrivateKey)
    (hk0 : 0 < scNat k.scalar) (hk : scNat k.scalar < n256) :
    high.ecdsa.SigningKey.new P256C k ⦃ key => SigningKeyOf key (scNat k.scalar) ⦄ := by
  unfold high.ecdsa.SigningKey.new
  obtain ⟨c, hcn⟩ := hc.point_new
  simp only [hcn, bind_ok, WP.spec_ok]
  exact ⟨rfl, hk0, hk⟩

/-- A signing key's public key: X9.62's uncompressed encoding of its scalar
times G, in the first 65 bytes, built on the first read and kept. -/
theorem public_key_bytes_spec (h : Runs) (hc : Cached) (key : P256SigningKey) (d : Nat)
    (hs : SigningKeyOf key d) :
    high.ecdsa.SigningKey.public_key_uncompressed P256C key ⦃ ep =>
      ep.len.val = 65 ∧ p256PublicKey d (ep.bytes.val.take 65) ⦄ := by
  unfold high.ecdsa.SigningKey.public_key_uncompressed
  exact hc.point_get_or_build_now key _ (point_build_spec h key d hs)

/-- An encoded point's bytes. -/
theorem encoded_point_as_ref_spec (ep : high.ecdsa.EncodedPoint) (h : ep.len.val ≤ 133) :
    high.ecdsa.EncodedPoint.Insts.CoreConvertAsRefSliceU8.as_ref ep ⦃ s =>
      s.val = ep.bytes.val.take ep.len.val ⦄ := by
  unfold high.ecdsa.EncodedPoint.Insts.CoreConvertAsRefSliceU8.as_ref
  step*
  simp [s_post, List.slice, Array.val_to_slice]

/-- The system source's draws: `getrandom::fill`'s failure is `RngFailed`. -/
theorem system_draws (hfill : Fills) : Draws mid.rng.SystemRandom.Insts.RindMidRngRandomSource := by
  intro rng s
  obtain ⟨⟨fr, fs⟩, hf⟩ := hfill s
  simp only [
    mid.rng.SystemRandom.Insts.RindMidRngRandomSource.fill, hf, bind_ok]
  rcases fr with _ | e <;>
    simp [core.result.Result.map_err,
      
      mid.rng.RandomSourceSystemRandom.fill.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once]

theorem signing_generate_spec (h : Runs) (hc : Cached) (hfill : Fills) :
    high.ecdsa.SigningKey.generate P256C ⦃ r =>
      (∀ key, r = .Ok key → ∃ d, SigningKeyOf key d) ∧ ∀ e, r = .Err e → e = .RngFailed ⦄ := by
  unfold high.ecdsa.SigningKey.generate
  step with new_secret_spec h
  step with static_generate_spec h _ (system_draws hfill) () as ⟨rr, hrr⟩
  obtain ⟨hok, herr⟩ := hrr
  rcases rr with k | e
  · obtain ⟨hk0, hk⟩ := hok k rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with signing_new_spec hc k hk0 hk as ⟨key, hkey⟩
    exact ⟨fun key' h' => by cases h'; exact ⟨_, hkey⟩, fun e h => nomatch h⟩
  · simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      using herr e rfl

theorem split_first_spec {T : Type} (s : Slice T) :
    core.slice.Slice.split_first s ⦃ o =>
      match s.val with
      | [] => o = none
      | x :: rest => ∃ t : Slice T, o = some (x, t) ∧ t.val = rest ⦄ := by
  unfold core.slice.Slice.split_first
  split <;> rename_i h <;> simp [h]

end P256

theorem compress_tag (b : U8) : (2#u8 ||| (b &&& 1#u8)) = 2#u8 ∨ (2#u8 ||| (b &&& 1#u8)) = 3#u8 := by
  have : ∀ v : BitVec 8, (2#8 ||| (v &&& 1#8)) = 2#8 ∨ (2#8 ||| (v &&& 1#8)) = 3#8 := by decide
  rcases this b.bv with h | h
  · left; exact (UScalar.eq_equiv_bv_eq _ _).mpr h
  · right; exact (UScalar.eq_equiv_bv_eq _ _).mpr h

/-- X9.62's compressed encoding of the point whose uncompressed encoding is
`b`: 2 or 3 by the parity of y's last byte, then x. -/
def x962Compress (b : List U8) : List U8 :=
  (2#u8 ||| (b.getLastD 0#u8 &&& 1#u8)) :: b.slice 1 33

namespace P256

/-- `sec1::is_public_key` against an uncompressed point `s`. -/
theorem sec1_is_public_key_spec (s enc : Slice U8) (xy : List U8) (hs : s.val = 4#u8 :: xy)
    (hxyl : xy.length = 64) :
    high.sec1.is_public_key s enc ⦃ b =>
      b ↔ enc.val = 4#u8 :: xy ∨ enc.val = x962Compress (4#u8 :: xy) ⦄ := by
  unfold high.sec1.is_public_key
  step with split_first_spec s as ⟨o, ho⟩
  rw [hs] at ho
  obtain ⟨t, rfl, ht⟩ := ho
  simp only
  step*
  have hi1 : i1.val = 32 := by
    rw [i1_post]; simp only [Slice.len_val]; rw [Slice.length, ht, hxyl]
  rw [hi1, ht] at x_post2 x_post3
  have hyne : (xy.drop 32) ≠ [] := by simp [hxyl]
  have hlast : (4#u8 :: xy).getLastD 0#u8 = (xy.drop 32).getLast hyne := by
    have hxne : xy ≠ [] := by intro h; simp [h] at hxyl
    rw [List.getLastD_eq_getLast?, List.getLast?_cons, List.getLast_drop, List.getLast?_eq_some_getLast hxne]
    rfl
  have hcomp : x962Compress (4#u8 :: xy) = (2#u8 ||| ((xy.drop 32).getLast hyne &&& 1#u8)) :: x.val := by
    rw [x962Compress, hlast, x_post2]; simp [List.slice]
  rw [hcomp]
  step with split_first_spec enc as ⟨o1, ho1⟩
  rcases he : enc.val with _ | ⟨tag, rest⟩
  · rw [he] at ho1
    subst ho1
    simp only
    step with slice_eq_spec enc s as ⟨b, hb⟩
    rw [hb, he, hs]; simp
  · rw [he] at ho1
    obtain ⟨cs, rfl, hcs⟩ := ho1
    simp only
    have hy : y.val.getLast? = some ((xy.drop 32).getLast hyne) := by
      rw [x_post3, List.getLast?_eq_some_getLast hyne]
    have h4ne2 : (4#u8 : U8) ≠ 2#u8 := by decide
    have h4ne3 : (4#u8 : U8) ≠ 3#u8 := by decide
    generalize (4#u8 : U8) = four at hs h4ne2 h4ne3 ⊢
    generalize hc : (2#u8 ||| (List.drop 32 xy).getLast hyne &&& 1#u8) = c
    have hcase : ∀ t : U8, t ≠ four →
        (do
          let b ← core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 cs x
          if b = true then do
              let o2 ← core.slice.Slice.last y
              core.option.Option.is_some_and
                high.sec1.is_public_key.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U8Bool
                o2 t
            else ok false) ⦃ b => b = true ↔ t :: rest = four :: xy ∨ t :: rest = c :: x.val ⦄ := by
      intro t ht
      step with slice_eq_spec cs x as ⟨b, hb⟩
      rw [hcs] at hb
      split
      · have hr : rest = x.val := hb.mp ‹_›
        simp only [core.slice.Slice.last, bind_ok, hy, core.option.Option.is_some_and,
          
          high.sec1.is_public_key.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U8Bool.call_once,
          Shared0U8.Insts.CoreOpsBitBitAndU8U8.bitand, lift, WP.spec_ok, hc]
        simp [hr, ht]
      · have hr : rest ≠ x.val := fun h => ‹¬b = true› (hb.mpr h)
        simp [hr, ht]
    have hc23 : c = 2#u8 ∨ c = 3#u8 := hc ▸ compress_tag _
    conv => lhs; whnf
    split
    · exact hcase _ (fun h => h4ne2 (h ▸ UScalar.eq_of_val_eq rfl))
    · exact hcase _ (fun h => h4ne3 (h ▸ UScalar.eq_of_val_eq rfl))
    · rename_i hn2 hn3
      step with slice_eq_spec enc s as ⟨b, hb⟩
      rw [hb, he, hs]
      have hnc : tag ≠ c := by
        rintro rfl
        rcases hc23 with h | h
        · exact hn2 (h.trans (UScalar.eq_of_val_eq rfl))
        · exact hn3 (h.trans (UScalar.eq_of_val_eq rfl))
      simp [hnc]

theorem is_public_key_spec (h : Runs) (hc : Cached) (key : P256SigningKey) (d : Nat)
    (hs : SigningKeyOf key d) (enc : Slice U8) :
    high.ecdsa.SigningKey.is_public_key P256C key enc ⦃ b =>
      ∃ B, p256PublicKey d B ∧ (b ↔ enc.val = B ∨ enc.val = x962Compress B) ⦄ := by
  obtain ⟨hsd, hd0, hd⟩ := hs
  apply is_public_key_of h hc key enc (hsd ▸ hd0) (hsd ▸ hd)
  swap
  · intro m h4 hm
    obtain ⟨ep, hl, hpk⟩ := WP.spec_exists (public_key_bytes_spec h hc key d ⟨hsd, hd0, hd⟩)
    cases m
    · refine ⟨_, hpk, ?_⟩
      simp only [Bool.false_eq_true, false_iff, not_or]
      refine ⟨fun he => ?_, fun he => ?_⟩
      · have := hm.mpr ⟨by rw [Slice.length, he]; exact hpk.1, by rw [hsd, he]; exact hpk.2.2⟩
        exact Bool.false_ne_true this
      · rw [he, x962Compress, List.head?_cons, Option.some.injEq] at h4
        rcases compress_tag ((ep.bytes.val.take 65).getLastD 0#u8) with h | h <;> rw [h] at h4 <;>
          exact absurd h4 (by decide)
    · obtain ⟨hl65, hq⟩ := hm.mp rfl
      exact ⟨enc.val, ⟨hl65, h4, hsd ▸ hq⟩, by simp⟩
  have hs : SigningKeyOf key d := ⟨hsd, hd0, hd⟩
  step with public_key_bytes_spec h hc key d hs as ⟨ep, hl, hpk⟩
  step with encoded_point_as_ref_spec ep (by rw [hl]; decide) as ⟨sl, hsl⟩
  rw [hl] at hsl
  obtain ⟨xy, hxy⟩ : ∃ xy, ep.bytes.val.take 65 = 4#u8 :: xy := by
    have h4 := hpk.2.1
    revert h4
    cases ep.bytes.val.take 65 with
    | nil => simp
    | cons a t => intro h4; simp at h4; exact ⟨t, by rw [h4]⟩
  have hxyl : xy.length = 64 := by
    have := congrArg List.length hxy; rw [hpk.1] at this; simp at this; omega
  apply WP.spec_mono (sec1_is_public_key_spec sl enc xy (by rw [hsl, hxy]) hxyl)
  intro b hb
  exact ⟨_, hxy ▸ hpk, hb⟩

theorem from_scalar_spec (h : Runs) (hc : Cached) (sk pk : Slice U8) :
    high.ecdsa.SigningKey.from_private_key_and_public_key P256C sk pk ⦃ r =>
      if sk.length ≠ 32 then r = .Err (.KeyRejected .WrongLength)
      else if 0 < beNat sk.val ∧ beNat sk.val < n256 then
        ∃ b, p256PublicKey (beNat sk.val) b ∧
          if pk.val = b ∨ pk.val = x962Compress b then ∃ key, r = .Ok key ∧ SigningKeyOf key (beNat sk.val)
          else r = .Err (.KeyRejected .MismatchedPublicKey)
      else r = .Err (.KeyRejected .ScalarOutOfRange) ⦄ := by
  unfold high.ecdsa.SigningKey.from_private_key_and_public_key
  step with new_secret_spec h
  simp only [mid.p256.Scalar.Insts.RindHighCurveScalar.LEN_BYTES, mid.p256.Scalar.BYTES]
  by_cases hl : sk.length = 32
  · have hne : (Slice.len sk != 32#usize) = false := by
      simp only [bne_eq_false_iff_eq]
      apply UScalar.eq_of_val_eq
      simpa [Slice.len, Slice.length] using hl
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hl, ne_eq, not_true_eq_false]
    simp only [mid.p256.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.from_bytes,
      mid.p256.StaticPrivateKey.from_bytes]
    step with new_secret_spec h
    step with from_bytes_spec sk hl as ⟨r, hr⟩
    split_ifs at hr ⊢ with hin
    · obtain ⟨k, rfl, hk⟩ := hr
      simp only [core.result.Result.map, P.Insts.CoreOpsFunctionFnOnceTuplePrivateKeyStaticPrivateKey.call_once,
        mid.p256.StaticPrivateKey.constructor, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
      have hk' : scNat k.scalar = beNat sk.val := hk
      step with signing_new_spec hc k (hk' ▸ hin.1) (hk' ▸ hin.2) as ⟨key, hkey⟩
      rw [hk'] at hkey
      step with is_public_key_spec h hc key _ hkey pk as ⟨b, B, hB, hb⟩
      split
      · rename_i hbt
        simp only [WP.spec_ok]
        refine ⟨_, hB, ?_⟩
        rw [ite_eq_left (hb.mp hbt)]
        exact ⟨_, rfl, hkey⟩
      · rename_i hbf
        simp only [error.Error.Insts.CoreConvertFromKeyFormatError.from, bind_ok, WP.spec_ok]
        refine ⟨_, hB, ?_⟩
        rw [ite_eq_right (fun h => hbf (hb.mpr h))]
        trivial
    · subst hr
      simp [core.result.Result.map, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · have hne : (Slice.len sk != 32#usize) = true := by
      simp only [bne_iff_ne, ne_eq]
      intro h'
      exact hl (by simpa [Slice.len, Slice.length] using congrArg UScalar.val h')
    simp [hne, hl, error.Error.Insts.CoreConvertFromKeyFormatError.from]

/-- `Buffer::copy_from` of bytes that fit. -/
theorem copy_from_spec (N : Usize) (bytes : Slice U8) (hN : bytes.length ≤ N.val) :
    high.signature.Buffer.copy_from N bytes ⦃ r => ∃ b, r = .Ok b ∧ b.len.val = bytes.length ∧
      b.bytes.val.take bytes.length = bytes.val ⦄ := by
  unfold high.signature.Buffer.copy_from high.signature.Buffer.new
  step*
  have hsl : s.length = N.val := by simp [Slice.length, s_post]
  have hle : bytes.len ≤ s.length := by scalar_tac
  simp only [core.slice.Slice.get_mut, core.slice.index.SliceIndexRangeToUsizeSlice.get_mut, hle,
    ↓reduceIte]
  step*
  rw [span1_post]
  have hbl : bytes.length = bytes.len.val := by simp [Slice.length, Slice.len]
  have hs : s.val.length = N.val := hsl
  refine ⟨_, rfl, hbl.symm, ?_⟩
  split_ifs
  simp only [to_slice_mut_back_post]
  rw [Array.from_slice_val _ _ (by simp [hs])]
  have := take_setSlice! s.val bytes.val 0 (by simp [Slice.length] at hN; omega)
  simpa using this

end P256

/-- A key pair whose private scalar is `d`, for ECDSA on P-256 with SHA-256
and fixed-length signatures. -/
def EcdsaKeyPairOf (kp : high.signature.EcdsaKeyPair) (d : Nat) : Prop :=
  ∃ signing, kp.key = .P256Sha256Fixed signing ∧ SigningKeyOf signing d

open Classical in
/-- An ECDSA verification's result: accepted exactly when `sig` is 64 bytes,
the big-endian r and s of a valid signature of `e` under `Q`. -/
def ecdsaVerdict (Q : P256Point) (e : Nat) (sig : List U8) (r : core.result.Result Unit error.Error) : Prop :=
  r = if sig.length = 64 ∧ ecdsaP256Verifies Q e (beNat (sig.take 32)) (beNat (sig.drop 32)) then .Ok ()
    else .Err .BadSignature

/-- The integer ECDSA signs for `msg`: FIPS 180-4's SHA-256 of it, read
big-endian, mod n. -/
def sha256E (msg : List U8) : Nat :=
  (BitVec.fromBEBytes (sha256.hash (bv msg))).toNat % n256

/-- The digest the ECDSA layer hashes `msg` to, given the block functions'
contracts, encodes `sha256E`'s integer. -/
theorem ecdsa_sha256_spec (hsha : Sha256Blocks) (msg : Slice U8) (hm : msg.length ≤ maxInput) :
    ∃ d dg, Sha256Sig.HashInst.hash msg = ok d ∧
      high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = ok dg ∧ 32 ≤ dg.length ∧
      beNat (dg.val.take 32) % n256 = sha256E msg.val := by
  obtain ⟨d, hd, hL, hdb⟩ : ∃ d, Sha256Hash.hash msg = ok d ∧ outLen d.algorithm = 32 ∧
      digestBytes d = sha256.hash (bv msg.val) := by
    have h1 := (sha256_hashSpec hsha).hash_spec msg hm
    generalize Sha256Hash.hash msg = r at h1 ⊢
    cases r <;> simp_all
  obtain ⟨dg, hdg, hdl, hdv⟩ : ∃ dg, high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = ok dg ∧
      dg.length = outLen d.algorithm ∧ bv dg.val = digestBytes d := by
    have h1 := digest_as_ref_spec d
    generalize high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = r at h1 ⊢
    cases r <;> simp_all
  refine ⟨d, dg, hd, hdg, by omega, ?_⟩
  rw [List.take_of_length_le (by simp only [Slice.length] at hdl; omega), sha256E, ← hdb, ← hdv,
    bv, toNat_fromBEBytes]

namespace P256

/-- What the generic layer's verification outcome says, as a verdict on `e`. -/
theorem verdict_of_outcome {Q : P256Point} {dg sig : List U8} {r : core.result.Result Unit error.Error}
    (h : ecdsaVerifyOutcome Q dg sig r) : ecdsaVerdict Q (beNat (dg.take 32) % n256) sig r := by
  unfold ecdsaVerifyOutcome at h
  unfold ecdsaVerdict
  rcases h with ⟨h1, h2, rfl⟩ | ⟨hv, rfl⟩
  · rw [ite_eq_left ⟨h1, h2⟩]
  · rw [ite_eq_right hv]

end P256

/-! ## The signature API, `high::signature`, through the modelled dispatch -/

/-- A generated key pair's private scalar is in [1, n), drawn from the system
random source, and generation is refused only if the draws fail. The draws
themselves are outside the functional spec. -/
theorem p256_ecdsa_generate (h : Runs) (hc : Cached) (hfill : Fills) :
    high.signature.EcdsaKeyPair.generate high.signature.sign.ECDSA_P256_SHA256_FIXED ⦃ r =>
      (∀ kp, r = .Ok kp → ∃ d, EcdsaKeyPairOf kp d) ∧ ∀ e, r = .Err e → e = .RngFailed ⦄ := by
  unfold high.signature.EcdsaKeyPair.generate high.signature.sign.ECDSA_P256_SHA256_FIXED
    high.signature.EcdsaKeyPair.load_p256_sha256_fixed
  simp only
  step with signing_generate_spec h hc hfill as ⟨r, hok, herr⟩
  rcases r with signing | e
  · obtain ⟨d, hd⟩ := hok signing rfl
    simp only [WP.spec_ok]
    exact ⟨fun kp h' => by cases h'; exact ⟨d, signing, rfl, hd⟩, fun e h => (nomatch h)⟩
  · simp only [WP.spec_ok]
    exact ⟨fun kp h => (nomatch h), fun e' h' => by cases h'; exact herr e rfl⟩

open Classical in
/-- A key pair loaded from a private scalar and the public key it claims:
refused unless the scalar is 32 bytes, in [1, n), and the public key is its
uncompressed or compressed encoding, and otherwise its private scalar is the
scalar. -/
theorem p256_ecdsa_from_scalar_and_public_key (h : Runs) (hc : Cached) (sk pk : Slice U8) :
    high.signature.EcdsaKeyPair.from_scalar_and_public_key high.signature.sign.ECDSA_P256_SHA256_FIXED
      sk pk ⦃ r =>
      if sk.length ≠ 32 then r = .Err (.KeyRejected .WrongLength)
      else if 0 < beNat sk.val ∧ beNat sk.val < n256 then
        ∃ b, p256PublicKey (beNat sk.val) b ∧
          if pk.val = b ∨ pk.val = x962Compress b then ∃ kp, r = .Ok kp ∧ EcdsaKeyPairOf kp (beNat sk.val)
          else r = .Err (.KeyRejected .MismatchedPublicKey)
      else r = .Err (.KeyRejected .ScalarOutOfRange) ⦄ := by
  unfold high.signature.EcdsaKeyPair.from_scalar_and_public_key high.signature.sign.ECDSA_P256_SHA256_FIXED
    high.signature.EcdsaKeyPair.load_p256_sha256_fixed
  simp only
  step with from_scalar_spec h hc sk pk as ⟨r, hr⟩
  split_ifs at hr ⊢ with hl hin
  · subst hr; simp
  · obtain ⟨b, hb, hr⟩ := hr
    by_cases hm : pk.val = b ∨ pk.val = x962Compress b
    · rw [ite_eq_left hm] at hr
      obtain ⟨key, rfl, hkey⟩ := hr
      simp only [WP.spec_ok]
      exact ⟨b, hb, by rw [ite_eq_left hm]; exact ⟨_, rfl, key, rfl, hkey⟩⟩
    · rw [ite_eq_right hm] at hr
      subst hr
      simp only [WP.spec_ok]
      exact ⟨b, hb, by simp [hm]⟩
  · subst hr; simp

/-- A signature's bytes, if signing returns: the big-endian r and s of the
ECDSA signature of `msg`'s SHA-256 under the key pair's scalar, for some
nonce in [1, n), neither zero. Signing is refused only if the nonce's random
input cannot be drawn. The nonces, RFC 6979's hedged with that input, are
outside the functional spec. -/
theorem p256_ecdsa_sign (h : Runs) (hdrbg : Drbg) (hfill : Fills)
    (hsha : Sha256Blocks) (kp : high.signature.EcdsaKeyPair) (d : Nat) (hkp : EcdsaKeyPairOf kp d)
    (msg : Slice U8) (hm : msg.length ≤ maxInput) :
    high.signature.EcdsaKeyPair.sign kp msg ⦃ r =>
      (∀ sig, r = .Ok sig → high.signature.Signature.Insts.CoreConvertAsRefSliceU8.as_ref sig ⦃ b =>
        b.length = 64 ∧ ∃ k, 0 < k ∧ k < n256 ∧
          ecdsaP256Sign d k (sha256E msg.val) = some (beNat (b.val.take 32), beNat (b.val.drop 32)) ∧
          beNat (b.val.take 32) ≠ 0 ∧ beNat (b.val.drop 32) ≠ 0 ⦄) ∧
      ∀ err, r = .Err err → err = .RngFailed ⦄div := by
  obtain ⟨signing, hkey, hs⟩ := hkp
  obtain ⟨hsd, -, hd⟩ := hs
  obtain ⟨dd, dg, hhash, hdg', hdg, he⟩ := ecdsa_sha256_spec hsha msg hm
  rw [← he]
  unfold high.signature.EcdsaKeyPair.sign high.signature.Buffer.write high.signature.Buffer.new
  rw [hkey]
  simp only [lift, bind_ok, Array.to_slice_mut]
  apply WP.dspec_bind (ecdsa_sign_spec h hdrbg hfill Sha256Sig signing (by rw [hsd]; exact hd) msg _ dg dd
    hhash hdg' hdg)
  rintro ⟨r, s1⟩ ⟨hok, herr⟩
  rw [hsd] at hok
  have hr : (Array.repeat 1024#usize 0#u8).to_slice.length = 1024 := by
    simp only [Slice.length, Array.val_to_slice]; exact (Array.repeat 1024#usize 0#u8).property
  rw [hr] at hok herr
  rcases r with out | err
  · obtain ⟨hl64, hs1l, htake, k, hk0, hk, hsign, hr0, hs0⟩ := hok out rfl
    simp only [WP.dspec_ok]
    refine ⟨fun sig hsig => ?_, fun e h => (nomatch h)⟩
    cases hsig
    unfold high.signature.Signature.Insts.CoreConvertAsRefSliceU8.as_ref
    have hlen : out.len.val = 64 := by simpa [Slice.len, Slice.length] using hl64
    apply WP.spec_mono (buffer_as_ref_spec _ (by simp [hlen]))
    intro b hb
    have hbv : b.val = out.val := by
      rw [hb]
      simp only [hlen]
      rw [Array.from_slice_val _ _ (by simp only [Slice.length] at hs1l; rw [hs1l]; rfl)]
      exact htake
    have hbl : b.length = 64 := by simp only [Slice.length, hbv]; exact hl64
    rw [hbv] at ⊢
    exact ⟨hbl, k, hk0, hk, hsign, hr0, hs0⟩
  · simp only [WP.dspec_ok]
    refine ⟨fun sig h => (nomatch h), fun e h => ?_⟩
    cases h
    rcases herr err rfl with ⟨hlt, -⟩ | hrng
    · omega
    · exact hrng

namespace P256

/-- What a key pair's `public_key` returns: a key that verifies with its
scalar times G, and that point's X9.62 uncompressed encoding. -/
theorem key_pair_public_key_spec (h : Runs) (hheld : Held) (hc : Cached)
    (kp : high.signature.EcdsaKeyPair) (d : Nat) (hkp : EcdsaKeyPairOf kp d) :
    high.signature.EcdsaKeyPair.impl.public_key kp ⦃ pk =>
      (∃ vk : P256VerifyingKey, VKey (p256Pow p256G d) vk.public_key ∧
        pk.key = .Other fun message signature =>
          high.ecdsa.VerifyingKey.verify P256C Sha256Sig vk message signature) ∧
      pk.encoding.len.val = 65 ∧ p256PublicKey d (pk.encoding.bytes.val.take 65) ⦄ := by
  obtain ⟨signing, hkey, hs⟩ := hkp
  obtain ⟨-, hd0, hd⟩ := id hs
  unfold high.signature.EcdsaKeyPair.impl.public_key
  rw [hkey]
  simp only
  step with public_key_bytes_spec h hc signing d hs as ⟨ep, hl, hpk⟩
  step with encoded_point_as_ref_spec ep (by rw [hl]; decide) as ⟨sl, hsl⟩
  rw [hl] at hsl
  step with ecdsa_vk_from_x962_spec h hheld hc sl as ⟨vr, hvr⟩
  obtain ⟨hl65, h4, hq⟩ := id hpk
  obtain ⟨x, y, hxy, hon⟩ := g_mult d hd0 hd
  rw [hq] at hxy
  rw [← hxy] at hon
  unfold x962Outcome at hvr
  rw [hsl, h4] at hvr
  simp only [↓reduceIte, hl65, hon] at hvr
  obtain ⟨vk, rfl, hvk⟩ := hvr
  simp only [core.result.Result.expect, bind_ok]
  step with encoded_point_as_ref_spec ep (by rw [hl]; decide) as ⟨sl1, hsl1⟩
  rw [hl] at hsl1
  have hsl1l : sl1.length = 65 := by simp only [Slice.length, hsl1]; exact hl65
  step with copy_from_spec 2592#usize sl1 (by rw [hsl1l]; decide) as ⟨rb, b, hrb, hbl, hbt⟩
  subst hrb
  simp only [bind_ok, WP.spec_ok]
  refine ⟨⟨vk, by rw [hq]; exact hvk, rfl⟩, by rw [hbl, hsl1l], ?_⟩
  rw [← hsl1l, hbt, hsl1]
  exact hpk

end P256

/-- A key pair's public key's bytes: X9.62's uncompressed encoding of its
scalar times the generator. -/
theorem p256_ecdsa_key_pair_public_key (h : Runs) (hheld : Held) (hc : Cached)
    (kp : high.signature.EcdsaKeyPair) (d : Nat) (hkp : EcdsaKeyPairOf kp d) :
    (do
      let pk ← high.signature.EcdsaKeyPair.impl.public_key kp
      high.signature.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk) ⦃ b =>
      p256PublicKey d b.val ⦄ := by
  apply WP.spec_bind (key_pair_public_key_spec h hheld hc kp d hkp)
  rintro pk ⟨-, hl, hpk⟩
  unfold high.signature.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref
  step with buffer_as_ref_spec pk.encoding (by rw [hl]; decide) as ⟨b, hb⟩
  rw [hb, hl]
  exact hpk

/-- Verification with a key pair's public key: ECDSA's verification of
`msg`'s SHA-256 under its scalar times the generator. -/
theorem p256_ecdsa_key_pair_verify (h : Runs) (hheld : Held) (hc : Cached)
    (hsha : Sha256Blocks) (kp : high.signature.EcdsaKeyPair) (d : Nat) (hkp : EcdsaKeyPairOf kp d)
    (msg sig : Slice U8) (hm : msg.length ≤ maxInput) :
    (do
      let pk ← high.signature.EcdsaKeyPair.impl.public_key kp
      high.signature.PublicKey.verify pk msg sig) ⦃ r =>
      ecdsaVerdict (p256Pow p256G d) (sha256E msg.val) sig.val r ⦄ := by
  obtain ⟨signing, hkey, hs⟩ := id hkp
  obtain ⟨-, hd0, hd⟩ := hs
  obtain ⟨dd, dg, hhash, hdg', hdg, he⟩ := ecdsa_sha256_spec hsha msg hm
  rw [← he]
  apply WP.spec_bind (key_pair_public_key_spec h hheld hc kp d hkp)
  rintro pk ⟨⟨vk, hvk, hpkk⟩, -, -⟩
  unfold high.signature.PublicKey.verify
  rw [hpkk]
  simp only
  exact WP.spec_mono (ecdsa_verify_spec h hc Sha256Sig vk _ hvk (g_mult_order d hd0 hd) msg sig dg dd hhash
    hdg' hdg)
    fun r hr => verdict_of_outcome hr

/-- A P-256 public key parsed from its encoding: refused unless it is an
X9.62 uncompressed point on the curve, and otherwise its verification is
ECDSA's of a message's SHA-256 under that point. -/
theorem p256_ecdsa_public_key_new (h : Runs) (hheld : Held) (hc : Cached)
    (hsha : Sha256Blocks) (bytes : Slice U8) :
    high.signature.PublicKey.new high.signature.verify.ECDSA_P256_SHA256_FIXED bytes ⦃ r =>
      x962Outcome bytes.val (fun pk => ∀ (msg sig : Slice U8), msg.length ≤ maxInput →
        high.signature.PublicKey.verify pk msg sig ⦃ v =>
          ecdsaVerdict (some (x962Coords bytes.val)) (sha256E msg.val) sig.val v ⦄) r ⦄ := by
  unfold high.signature.PublicKey.new high.signature.verify.ECDSA_P256_SHA256_FIXED
    high.signature.parse_ecdsa_p256_sha256_fixed
  simp only
  step with ecdsa_vk_from_x962_spec h hheld hc bytes as ⟨r, hr⟩
  unfold x962Outcome at hr ⊢
  rcases hb : bytes.val.head? with _ | b0
  · simp only [hb] at hr ⊢; subst hr; simp
  · simp only [hb] at hr ⊢
    split_ifs at hr ⊢ with h4 hl hon
    · obtain ⟨vk, rfl, hvk⟩ := hr
      simp only
      step with copy_from_ok 2592#usize bytes (by simp [hl]) as ⟨b, enc, hb'⟩
      subst hb'
      simp only [WP.spec_ok]
      refine ⟨_, rfl, fun msg sig hm => ?_⟩
      obtain ⟨dd, dg, hhash, hdg', hdg, he⟩ := ecdsa_sha256_spec hsha msg hm
      rw [← he]
      exact WP.spec_mono (ecdsa_verify_spec h hc Sha256Sig vk _ hvk (p256_order _ hvk.1 hvk.2.1) msg sig dg dd hhash
        hdg' hdg)
        fun r hr => verdict_of_outcome hr
    · subst hr; simp
    · subst hr; simp
    · subst hr; simp

end rind.x86_64
