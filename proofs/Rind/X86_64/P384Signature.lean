import Rind.X86_64.P384KeyCheck
import Rind.X86_64.P256Signature
import Rind.X86_64.Sha512
open Aeneas Aeneas.Std Result rind.spec

/-!
# P-384 ECDSA through the signature API

The `p384_ecdsa_*` theorems state what the signature API's `ecdsa` module
returns for `P384_SHA384_FIXED`, in terms of `Rind.Spec`'s ECDSA, through the
dispatch `Rind.X86_64.EcdsaDispatch` models, with SHA-384 as
`Rind.X86_64.Sha512` states it. A signing key checks its public key as
`Rind.X86_64.P384KeyCheck` states. `admin/prove` writes the aarch64 proof
from this file by renaming the target.
-/

namespace rind.x86_64

open P384

/-- A P-384 signing key whose private scalar is `d`, in [1, n). -/
def SigningKeyOf384 (key : P384SigningKey) (d : Nat) : Prop :=
  scNat key.private_key.scalar = d ∧ 0 < d ∧ d < n384

namespace P384

theorem static_public_key_uncompressed_spec (h : Runs) (hvg : RunsP384) (k : mid.p384.StaticPrivateKey)
    (hk0 : 0 < scNat k.scalar) (hk : scNat k.scalar < n384) :
    mid.p384.StaticPrivateKey.public_key_uncompressed k ⦃ b => p384PublicKey (scNat k.scalar) b.val ⦄ := by
  obtain ⟨x, y, hq, hc⟩ := p384_g_mult _ hk0 hk
  unfold mid.p384.StaticPrivateKey.public_key_uncompressed
  step with new_secret_spec h
  obtain ⟨⟨t, ht⟩, -⟩ := hvg
  simp only [ht, bind_ok]
  rcases t with _ | vg
  swap
  · apply WP.spec_mono (vg_public_key_spec h vg k hk x y hq hc)
    rintro b ⟨hb4, hbc⟩
    exact ⟨b.property, hb4, by rw [hq, hbc]⟩
  simp only
  step with public_point_spec h k x y hk hq hc as ⟨pt, hx, hy, hpx, hpy⟩
  step with as_bytes_uncompressed_spec h pt hx hy as ⟨b, hb4, hbc⟩
  exact ⟨b.property, hb4, by rw [hq, hbc, hpx, hpy]⟩

/-- The build of a signing key's cached public key: X9.62's uncompressed
encoding of its scalar times G, in the first 97 bytes. -/
theorem point_build_spec (h : Runs) (hvg : RunsP384) (key : P384SigningKey) (d : Nat) (hs : SigningKeyOf384 key d) :
    high.ecdsa.SigningKey.public_key_uncompressed.closure.Insts.CoreOpsFunctionFnOnceTupleEncodedPoint.call_once
      P384C key () ⦃ ep => ep.len.val = 97 ∧ p384PublicKey d (ep.bytes.val.take 97) ⦄ := by
  obtain ⟨hsd, hd0, hd⟩ := hs
  unfold high.ecdsa.SigningKey.public_key_uncompressed.closure.Insts.CoreOpsFunctionFnOnceTupleEncodedPoint.call_once
    high.ecdsa.EncodedPoint.Insts.CoreDefaultDefault.default
  simp only [mid.p384.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.public_key_encode_uncompressed]
  step*
  have hsl : s.length = 133 := by simp [Slice.length, s_post, Array.repeat]
  simp only [mid.p384.PublicKey.BYTES, mid.p384.FieldElement.BYTES, core.slice.Slice.get_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.get_mut]
  step*
  rw [ite_eq_left (by simp [hsl]; scalar_tac)]
  simp only [bind_ok]
  step with static_public_key_uncompressed_spec h hvg key.private_key (hsd ▸ hd0) (hsd ▸ hd) as ⟨a, ha⟩
  have hx : x.val = 97 := by scalar_tac
  have ha97 : a.val.length = 97 := a.property
  have hcp : core.slice.Slice.copy_from_slice core.marker.CopyU8
      (Slice.from (List.slice (0#usize).val x.val s.val) (by simp [List.slice])) a.to_slice =
      ok a.to_slice := by
    simp [core.slice.Slice.copy_from_slice, Slice.len, List.slice, hx, hsl, ha97]
  simp only [lift, bind_ok, hcp, core.result.Result.expect, WP.spec_ok]
  have hl : a.to_slice.length = x.val - (0#usize).val := by simp [Slice.length, hx, ha97]
  simp only [hl, ↓reduceDIte, to_slice_mut_back_post]
  refine ⟨by simp [Slice.len, ha97], ?_⟩
  have hs : s.val.length = 133 := hsl
  rw [Array.from_slice_val _ _ (by simp [hs])]
  have := take_setSlice! s.val a.val 0 (by omega)
  simp only [Nat.zero_add, List.take_zero, List.nil_append, ha97] at this
  rw [← hsd]
  simpa [this] using ha

theorem signing_new_spec (hc : P384.Cached) (k : mid.p384.StaticPrivateKey)
    (hk0 : 0 < scNat k.scalar) (hk : scNat k.scalar < n384) :
    high.ecdsa.SigningKey.new P384C k ⦃ key => SigningKeyOf384 key (scNat k.scalar) ⦄ := by
  unfold high.ecdsa.SigningKey.new
  obtain ⟨c, hcn⟩ := hc.point_new
  simp only [hcn, bind_ok, WP.spec_ok]
  exact ⟨rfl, hk0, hk⟩

/-- A signing key's public key: X9.62's uncompressed encoding of its scalar
times G, in the first 97 bytes, built on the first read and kept. -/
theorem public_key_bytes_spec (h : Runs) (hvg : RunsP384) (hc : P384.Cached) (key : P384SigningKey) (d : Nat)
    (hs : SigningKeyOf384 key d) :
    high.ecdsa.SigningKey.public_key_uncompressed P384C key ⦃ ep =>
      ep.len.val = 97 ∧ p384PublicKey d (ep.bytes.val.take 97) ⦄ := by
  unfold high.ecdsa.SigningKey.public_key_uncompressed
  exact hc.point_get_or_build_now key _ (point_build_spec h hvg key d hs)

theorem signing_generate_spec (h : Runs) (hc : P384.Cached) (hfill : Fills) :
    high.ecdsa.SigningKey.generate P384C ⦃ r =>
      (∀ key, r = .Ok key → ∃ d, SigningKeyOf384 key d) ∧ ∀ e, r = .Err e → e = .RngFailed ⦄ := by
  unfold high.ecdsa.SigningKey.generate
  step with new_secret_spec h
  step with static_generate_spec h _ (P256.system_draws hfill) () as ⟨rr, hrr⟩
  obtain ⟨hok, herr⟩ := hrr
  rcases rr with k | e
  · obtain ⟨hk0, hk⟩ := hok k rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with signing_new_spec hc k hk0 hk as ⟨key, hkey⟩
    exact ⟨fun key' h' => by cases h'; exact ⟨_, hkey⟩, fun e h => nomatch h⟩
  · simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      using herr e rfl

end P384

/-- X9.62's compressed encoding of the P-384 point whose uncompressed
encoding is `b`: 2 or 3 by the parity of y's last byte, then x. -/
def x962Compress384 (b : List U8) : List U8 :=
  (2#u8 ||| (b.getLastD 0#u8 &&& 1#u8)) :: b.slice 1 49

namespace P384

/-- `sec1::is_public_key` against an uncompressed P-384 point `s`. -/
theorem sec1_is_public_key_spec (s enc : Slice U8) (xy : List U8) (hs : s.val = 4#u8 :: xy)
    (hxyl : xy.length = 96) :
    high.sec1.is_public_key s enc ⦃ b =>
      b ↔ enc.val = 4#u8 :: xy ∨ enc.val = x962Compress384 (4#u8 :: xy) ⦄ := by
  unfold high.sec1.is_public_key
  step with P256.split_first_spec s as ⟨o, ho⟩
  rw [hs] at ho
  obtain ⟨t, rfl, ht⟩ := ho
  simp only
  step*
  have hi1 : i1.val = 48 := by
    rw [i1_post]; simp only [Slice.len_val]; rw [Slice.length, ht, hxyl]
  rw [hi1, ht] at x_post2 x_post3
  have hyne : (xy.drop 48) ≠ [] := by simp [hxyl]
  have hlast : (4#u8 :: xy).getLastD 0#u8 = (xy.drop 48).getLast hyne := by
    have hxne : xy ≠ [] := by intro h; simp [h] at hxyl
    rw [List.getLastD_eq_getLast?, List.getLast?_cons, List.getLast_drop, List.getLast?_eq_some_getLast hxne]
    rfl
  have hcomp : x962Compress384 (4#u8 :: xy) = (2#u8 ||| ((xy.drop 48).getLast hyne &&& 1#u8)) :: x.val := by
    rw [x962Compress384, hlast, x_post2]; simp [List.slice]
  rw [hcomp]
  step with P256.split_first_spec enc as ⟨o1, ho1⟩
  rcases he : enc.val with _ | ⟨tag, rest⟩
  · rw [he] at ho1
    subst ho1
    simp only
    step with slice_eq_spec enc s as ⟨b, hb⟩
    rw [hb, he, hs]; simp
  · rw [he] at ho1
    obtain ⟨cs, rfl, hcs⟩ := ho1
    simp only
    have hy : y.val.getLast? = some ((xy.drop 48).getLast hyne) := by
      rw [x_post3, List.getLast?_eq_some_getLast hyne]
    have h4ne2 : (4#u8 : U8) ≠ 2#u8 := by decide
    have h4ne3 : (4#u8 : U8) ≠ 3#u8 := by decide
    generalize (4#u8 : U8) = four at hs h4ne2 h4ne3 ⊢
    generalize hc : (2#u8 ||| (List.drop 48 xy).getLast hyne &&& 1#u8) = c
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

theorem is_public_key_spec (h : Runs) (hvg : RunsP384) (hc : P384.Cached) (key : P384SigningKey) (d : Nat)
    (hs : SigningKeyOf384 key d) (enc : Slice U8) :
    high.ecdsa.SigningKey.is_public_key P384C key enc ⦃ b =>
      ∃ B, p384PublicKey d B ∧ (b ↔ enc.val = B ∨ enc.val = x962Compress384 B) ⦄ := by
  obtain ⟨hsd, hd0, hd⟩ := hs
  apply is_public_key_of h hc key enc (hsd ▸ hd0) (hsd ▸ hd)
  swap
  · intro m h4 hm
    obtain ⟨ep, hl, hpk⟩ := WP.spec_exists (public_key_bytes_spec h hvg hc key d ⟨hsd, hd0, hd⟩)
    cases m
    · refine ⟨_, hpk, ?_⟩
      simp only [Bool.false_eq_true, false_iff, not_or]
      refine ⟨fun he => ?_, fun he => ?_⟩
      · have := hm.mpr ⟨by rw [Slice.length, he]; exact hpk.1, by rw [hsd, he]; exact hpk.2.2⟩
        exact Bool.false_ne_true this
      · rw [he, x962Compress384, List.head?_cons, Option.some.injEq] at h4
        rcases compress_tag ((ep.bytes.val.take 97).getLastD 0#u8) with h | h <;> rw [h] at h4 <;>
          exact absurd h4 (by decide)
    · obtain ⟨hl97, hq⟩ := hm.mp rfl
      exact ⟨enc.val, ⟨hl97, h4, hsd ▸ hq⟩, by simp⟩
  have hs : SigningKeyOf384 key d := ⟨hsd, hd0, hd⟩
  step with public_key_bytes_spec h hvg hc key d hs as ⟨ep, hl, hpk⟩
  step with P256.encoded_point_as_ref_spec ep (by rw [hl]; decide) as ⟨sl, hsl⟩
  rw [hl] at hsl
  obtain ⟨xy, hxy⟩ : ∃ xy, ep.bytes.val.take 97 = 4#u8 :: xy := by
    have h4 := hpk.2.1
    revert h4
    cases ep.bytes.val.take 97 with
    | nil => simp
    | cons a t => intro h4; simp at h4; exact ⟨t, by rw [h4]⟩
  have hxyl : xy.length = 96 := by
    have := congrArg List.length hxy; rw [hpk.1] at this; simp at this; omega
  apply WP.spec_mono (sec1_is_public_key_spec sl enc xy (by rw [hsl, hxy]) hxyl)
  intro b hb
  exact ⟨_, hxy ▸ hpk, hb⟩

theorem from_scalar_spec (h : Runs) (hvg : RunsP384) (hc : P384.Cached) (sk pk : Slice U8) :
    high.ecdsa.SigningKey.from_private_key_and_public_key P384C sk pk ⦃ r =>
      if sk.length ≠ 48 then r = .Err (.KeyRejected .WrongLength)
      else if 0 < beNat sk.val ∧ beNat sk.val < n384 then
        ∃ b, p384PublicKey (beNat sk.val) b ∧
          if pk.val = b ∨ pk.val = x962Compress384 b then
            ∃ key, r = .Ok key ∧ SigningKeyOf384 key (beNat sk.val)
          else r = .Err (.KeyRejected .MismatchedPublicKey)
      else r = .Err (.KeyRejected .ScalarOutOfRange) ⦄ := by
  unfold high.ecdsa.SigningKey.from_private_key_and_public_key
  step with new_secret_spec h
  simp only [mid.p384.Scalar.Insts.RindHighCurveScalar.LEN_BYTES, mid.p384.Scalar.BYTES]
  by_cases hl : sk.length = 48
  · have hne : (Slice.len sk != 48#usize) = false := by
      simp only [bne_eq_false_iff_eq]
      apply UScalar.eq_of_val_eq
      simpa [Slice.len, Slice.length] using hl
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hl, ne_eq, not_true_eq_false]
    simp only [mid.p384.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.from_bytes,
      mid.p384.StaticPrivateKey.from_bytes]
    step with new_secret_spec h
    step with from_bytes_spec sk hl as ⟨r, hr⟩
    split_ifs at hr ⊢ with hin
    · obtain ⟨k, rfl, hk⟩ := hr
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have hk' : scNat k.scalar = beNat sk.val := hk
      step with signing_new_spec hc k (hk' ▸ hin.1) (hk' ▸ hin.2) as ⟨key, hkey⟩
      rw [hk'] at hkey
      step with is_public_key_spec h hvg hc key _ hkey pk as ⟨b, B, hB, hb⟩
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
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  · have hne : (Slice.len sk != 48#usize) = true := by
      simp only [bne_iff_ne, ne_eq]
      intro h'
      exact hl (by simpa [Slice.len, Slice.length] using congrArg UScalar.val h')
    simp [hne, hl, error.Error.Insts.CoreConvertFromKeyFormatError.from]

end P384

/-- A public key for ECDSA on P-384 with SHA-384 and fixed-length signatures,
whose point is `Q`. -/
def EcdsaPublicKeyOf384 (pk : high.signature.ecdsa.PublicKey) (Q : nist.Point) : Prop :=
  ∃ vk : P384VerifyingKey, P384.VKey Q vk.public_key ∧ pk.key = .P384Sha384Fixed vk

/-- A key pair whose private scalar is `d`, for ECDSA on P-384 with SHA-384
and fixed-length signatures, holding its public key: the scalar times G, and
that point's X9.62 uncompressed encoding. -/
def EcdsaKeyPairOf384 (kp : high.signature.ecdsa.KeyPair) (d : Nat) : Prop :=
  (∃ signing, kp.key = .P384Sha384Fixed signing ∧ SigningKeyOf384 signing d) ∧
    EcdsaPublicKeyOf384 kp.«public» (p384Pow p384G d) ∧
    kp.«public».point.len.val = 97 ∧ p384PublicKey d (kp.«public».point.bytes.val.take 97)

open Classical in
/-- A P-384 ECDSA verification's result: accepted exactly when `sig` is 96
bytes, the big-endian r and s of a valid signature of `e` under `Q`. -/
def ecdsaVerdict384 (Q : nist.Point) (e : Nat) (sig : List U8) (r : core.result.Result Unit error.Error) :
    Prop :=
  r = if sig.length = 96 ∧ ecdsaP384Verifies Q e (beNat (sig.take 48)) (beNat (sig.drop 48)) then .Ok ()
    else .Err .BadSignature

/-- The integer ECDSA signs for `msg` on P-384: FIPS 180-4's SHA-384 of it,
read big-endian, mod n. -/
def sha384E (msg : List U8) : Nat :=
  beNat (sha384 msg) % n384

/-- The digest the ECDSA layer hashes `msg` to, given the SHA-512 block
routine's contract, encodes `sha384E`'s integer. -/
theorem ecdsa_sha384_spec (hsha : RunsSha512) (msg : Slice U8) (hm : msg.length ≤ maxInput) :
    ∃ d dg, Sha384Sig.HashInst.hash msg = ok d ∧
      high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = ok dg ∧ 48 ≤ dg.length ∧
      beNat (dg.val.take 48) % n384 = sha384E msg.val := by
  obtain ⟨d, hd, hL, hdb⟩ : ∃ d, Sha384Hash.hash msg = ok d ∧ outLen d.algorithm = 48 ∧
      digestBytes d = sha384Bytes (bv msg.val) := by
    have h1 := (sha384_hashSpec hsha).hash_spec msg hm
    generalize Sha384Hash.hash msg = r at h1 ⊢
    cases r <;> simp_all
  obtain ⟨dg, hdg, hdl, hdv⟩ : ∃ dg, high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = ok dg ∧
      dg.length = outLen d.algorithm ∧ bv dg.val = digestBytes d := by
    have h1 := digest_as_ref_spec d
    generalize high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = r at h1 ⊢
    cases r <;> simp_all
  refine ⟨d, dg, hd, hdg, by omega, ?_⟩
  have hdgv : dg.val = sha384 msg.val := by
    have := congrArg ofBv (hdv.trans hdb)
    rwa [ofBv_bv, sha384Bytes, ofBv_bv, ofBv_bv] at this
  rw [List.take_of_length_le (by simp only [Slice.length] at hdl; omega), sha384E, hdgv]

namespace P384

/-- What the generic layer's verification outcome says, as a verdict on `e`. -/
theorem verdict_of_outcome {Q : nist.Point} {dg sig : List U8} {r : core.result.Result Unit error.Error}
    (h : ecdsaVerifyOutcome Q dg sig r) : ecdsaVerdict384 Q (beNat (dg.take 48) % n384) sig r := by
  unfold ecdsaVerifyOutcome at h
  unfold ecdsaVerdict384
  rcases h with ⟨h1, h2, rfl⟩ | ⟨hv, rfl⟩
  · rw [ite_eq_left ⟨h1, h2⟩]
  · rw [ite_eq_right hv]

/-- What `load::<P384, Sha384, Fixed>` makes of a signing key whose scalar
is `d`: a key pair holding it, and its public key, which parses as its own
point. -/
theorem load_tail_spec (h : Runs) (hvg : RunsP384) (hheld : Held) (hc : P384.Cached) (signing : P384SigningKey) (d : Nat)
    (hs : SigningKeyOf384 signing d) :
    (do
      let point ← high.ecdsa.SigningKey.public_key_uncompressed P384C signing
      let s ← high.ecdsa.EncodedPoint.Insts.CoreConvertAsRefSliceU8.as_ref point
      let r ← high.signature.ecdsa.EcdsaVerifier.parse_p384_sha384_fixed s
      let key ← core.result.Result.expect error.Error.Insts.CoreFmtDebug r (toStr "its own point")
      ok (core.result.Result.Ok (E := error.Error)
        { key := .P384Sha384Fixed signing, «public» := { key := .P384Sha384Fixed key, point } }
        : core.result.Result high.signature.ecdsa.KeyPair error.Error)) ⦃ r =>
      ∃ kp, r = .Ok kp ∧ EcdsaKeyPairOf384 kp d ⦄ := by
  obtain ⟨-, hd0, hd⟩ := id hs
  step with public_key_bytes_spec h hvg hc signing d hs as ⟨ep, hl, hpk⟩
  step with P256.encoded_point_as_ref_spec ep (by rw [hl]; decide) as ⟨sl, hsl⟩
  rw [hl] at hsl
  unfold high.signature.ecdsa.EcdsaVerifier.parse_p384_sha384_fixed
  step with ecdsa_vk_from_x962_spec h hheld hc sl as ⟨vr, hvr⟩
  obtain ⟨hl97, h4, hq⟩ := id hpk
  obtain ⟨x, y, hxy, hon⟩ := p384_g_mult d hd0 hd
  rw [hq] at hxy
  rw [← hxy] at hon
  unfold x962Outcome at hvr
  rw [hsl, h4] at hvr
  simp only [↓reduceIte, hl97, hon] at hvr
  obtain ⟨vk, rfl, hvk⟩ := hvr
  simp only [core.result.Result.expect, bind_ok, WP.spec_ok]
  exact ⟨_, rfl, ⟨signing, rfl, hs⟩, ⟨vk, by rw [hq]; exact hvk, rfl⟩, hl, hpk⟩

end P384

/-! ## The signature API, `high::signature::ecdsa`, through the modelled dispatch -/

/-- A generated P-384 key pair's private scalar is in [1, n), drawn from the
system random source, and it holds its public key; generation is refused only
if a draw fails or none of its 64 draws is in [1, n). The draws themselves
are outside the functional spec. -/
theorem p384_ecdsa_generate (h : Runs) (hvg : RunsP384) (hheld : Held) (hc : P384.Cached) (hfill : Fills) :
    high.signature.ecdsa.KeyPair.generate high.signature.ecdsa.sign.P384_SHA384_FIXED ⦃ r =>
      (∀ kp, r = .Ok kp → ∃ d, EcdsaKeyPairOf384 kp d) ∧ ∀ e, r = .Err e → e = .RngFailed ⦄ := by
  unfold high.signature.ecdsa.KeyPair.generate high.signature.ecdsa.sign.P384_SHA384_FIXED
    high.signature.ecdsa.KeyPair.load_p384_sha384_fixed
  simp only
  step with signing_generate_spec h hc hfill as ⟨r, hok, herr⟩
  rcases r with signing | e
  · obtain ⟨d, hd⟩ := hok signing rfl
    simp only
    apply WP.spec_mono (load_tail_spec h hvg hheld hc signing d hd)
    rintro r ⟨kp, rfl, hkp⟩
    exact ⟨fun kp' h' => by cases h'; exact ⟨d, hkp⟩, fun e h => nomatch h⟩
  · simp only [WP.spec_ok]
    exact ⟨fun kp h => (nomatch h), fun e' h' => by cases h'; exact herr e rfl⟩

open Classical in
/-- A P-384 key pair loaded from a private scalar and the public key it
claims: refused unless the scalar is 48 bytes, in [1, n), and the public key
is its uncompressed or compressed encoding, and otherwise its private scalar
is the scalar. -/
theorem p384_ecdsa_from_scalar_and_public_key (h : Runs) (hvg : RunsP384) (hheld : Held) (hc : P384.Cached)
    (sk pk : Slice U8) :
    high.signature.ecdsa.KeyPair.from_scalar_and_public_key high.signature.ecdsa.sign.P384_SHA384_FIXED
      sk pk ⦃ r =>
      if sk.length ≠ 48 then r = .Err (.KeyRejected .WrongLength)
      else if 0 < beNat sk.val ∧ beNat sk.val < n384 then
        ∃ b, p384PublicKey (beNat sk.val) b ∧
          if pk.val = b ∨ pk.val = x962Compress384 b then
            ∃ kp, r = .Ok kp ∧ EcdsaKeyPairOf384 kp (beNat sk.val)
          else r = .Err (.KeyRejected .MismatchedPublicKey)
      else r = .Err (.KeyRejected .ScalarOutOfRange) ⦄ := by
  unfold high.signature.ecdsa.KeyPair.from_scalar_and_public_key high.signature.ecdsa.sign.P384_SHA384_FIXED
    high.signature.ecdsa.KeyPair.load_p384_sha384_fixed
  simp only
  step with from_scalar_spec h hvg hc sk pk as ⟨r, hr⟩
  split_ifs at hr ⊢ with hl hin
  · subst hr; simp
  · obtain ⟨b, hb, hr⟩ := hr
    by_cases hm : pk.val = b ∨ pk.val = x962Compress384 b
    · rw [ite_eq_left hm] at hr
      obtain ⟨key, rfl, hkey⟩ := hr
      simp only
      apply WP.spec_mono (load_tail_spec h hvg hheld hc key _ hkey)
      rintro r ⟨kp, rfl, hkp⟩
      exact ⟨b, hb, by rw [ite_eq_left hm]; exact ⟨kp, rfl, hkp⟩⟩
    · rw [ite_eq_right hm] at hr
      subst hr
      simp only [WP.spec_ok]
      exact ⟨b, hb, by simp [hm]⟩
  · subst hr; simp

/-- A P-384 signature's bytes, if signing returns: the big-endian r and s of
the ECDSA signature of `msg`'s SHA-384 under the key pair's scalar, for some
nonce in [1, n), neither zero. Signing is refused only if the nonce's random
input cannot be drawn, a nonce draw fails, or none of a nonce's 64 draws is
in [1, n). The nonces, RFC 6979's hedged with that input, are
outside the functional spec. -/
theorem p384_ecdsa_sign (h : Runs) (hvg : RunsP384) (hdrbg : Drbg) (hfill : Fills)
    (hsha : RunsSha512) (kp : high.signature.ecdsa.KeyPair) (d : Nat) (hkp : EcdsaKeyPairOf384 kp d)
    (msg : Slice U8) (hm : msg.length ≤ maxInput) :
    high.signature.ecdsa.KeyPair.sign kp msg ⦃ r =>
      (∀ sig, r = .Ok sig → high.signature.ecdsa.Signature.Insts.CoreConvertAsRefSliceU8.as_ref sig ⦃ b =>
        b.length = 96 ∧ ∃ k, 0 < k ∧ k < n384 ∧
          ecdsaP384Sign d k (sha384E msg.val) = some (beNat (b.val.take 48), beNat (b.val.drop 48)) ∧
          beNat (b.val.take 48) ≠ 0 ∧ beNat (b.val.drop 48) ≠ 0 ⦄) ∧
      ∀ err, r = .Err err → err = .RngFailed ⦄div := by
  obtain ⟨⟨signing, hkey, hs⟩, -⟩ := hkp
  obtain ⟨hsd, -, hd⟩ := hs
  obtain ⟨dd, dg, hhash, hdg', hdg, he⟩ := ecdsa_sha384_spec hsha msg hm
  rw [← he]
  unfold high.signature.ecdsa.KeyPair.sign high.signature.Buffer.write high.signature.Buffer.new
  rw [hkey]
  simp only [lift, bind_ok, Array.to_slice_mut]
  apply WP.dspec_bind (ecdsa_sign_spec h hvg hdrbg hfill Sha384Sig signing (by rw [hsd]; exact hd) msg _ dg dd
    hhash hdg' hdg)
  rintro ⟨r, s1⟩ ⟨hok, herr⟩
  rw [hsd] at hok
  have hr : (Array.repeat 141#usize 0#u8).to_slice.length = 141 := by
    simp only [Slice.length, Array.val_to_slice]; exact (Array.repeat 141#usize 0#u8).property
  rw [hr] at hok herr
  rcases r with out | err
  · obtain ⟨hl96, hs1l, htake, k, hk0, hk, hsign, hr0, hs0⟩ := hok out rfl
    simp only [WP.dspec_ok]
    refine ⟨fun sig hsig => ?_, fun e h => (nomatch h)⟩
    cases hsig
    unfold high.signature.ecdsa.Signature.Insts.CoreConvertAsRefSliceU8.as_ref
    have hlen : out.len.val = 96 := by simpa [Slice.len, Slice.length] using hl96
    apply WP.spec_mono (buffer_as_ref_spec _ (by simp [hlen]))
    intro b hb
    have hbv : b.val = out.val := by
      rw [hb]
      simp only [hlen]
      rw [Array.from_slice_val _ _ (by simp only [Slice.length] at hs1l; rw [hs1l]; rfl)]
      exact htake
    have hbl : b.length = 96 := by simp only [Slice.length, hbv]; exact hl96
    rw [hbv] at ⊢
    exact ⟨hbl, k, hk0, hk, hsign, hr0, hs0⟩
  · simp only [WP.dspec_ok]
    refine ⟨fun sig h => (nomatch h), fun e h => ?_⟩
    cases h
    rcases herr err rfl with ⟨hlt, -⟩ | hrng
    · omega
    · exact hrng

/-- A P-384 key pair's public key's bytes: X9.62's uncompressed encoding of
its scalar times the generator. -/
theorem p384_ecdsa_key_pair_public_key (kp : high.signature.ecdsa.KeyPair) (d : Nat)
    (hkp : EcdsaKeyPairOf384 kp d) :
    (do
      let pk ← high.signature.ecdsa.KeyPair.public_key kp
      high.signature.ecdsa.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk) ⦃ b =>
      p384PublicKey d b.val ⦄ := by
  obtain ⟨-, -, hl, hpk⟩ := hkp
  unfold high.signature.ecdsa.KeyPair.public_key high.signature.ecdsa.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref
  simp only [bind_ok]
  step with P256.encoded_point_as_ref_spec kp.«public».point (by rw [hl]; decide) as ⟨b, hb⟩
  rw [hb, hl]
  exact hpk

/-- Verification with a P-384 key pair's public key: ECDSA's verification
of `msg`'s SHA-384 under its scalar times the generator. -/
theorem p384_ecdsa_key_pair_verify (h : Runs) (hvg : RunsP384) (hc : P384.Cached)
    (hsha : RunsSha512) (kp : high.signature.ecdsa.KeyPair) (d : Nat) (hkp : EcdsaKeyPairOf384 kp d)
    (msg sig : Slice U8) (hm : msg.length ≤ maxInput) :
    (do
      let pk ← high.signature.ecdsa.KeyPair.public_key kp
      high.signature.ecdsa.PublicKey.verify pk msg sig) ⦃ r =>
      ecdsaVerdict384 (p384Pow p384G d) (sha384E msg.val) sig.val r ⦄ := by
  obtain ⟨⟨-, -, -, hd0, hd⟩, ⟨vk, hvk, hpkk⟩, -, -⟩ := hkp
  obtain ⟨dd, dg, hhash, hdg', hdg, he⟩ := ecdsa_sha384_spec hsha msg hm
  rw [← he]
  unfold high.signature.ecdsa.KeyPair.public_key high.signature.ecdsa.PublicKey.verify
  simp only [bind_ok]
  rw [hpkk]
  exact WP.spec_mono (ecdsa_verify_spec h hvg hc Sha384Sig vk _ hvk (p384_g_mult_order d hd0 hd) msg sig dg dd
    hhash hdg' hdg)
    fun r hr => P384.verdict_of_outcome hr

/-- A P-384 public key parsed from its encoding: refused unless it is an
X9.62 uncompressed point on the curve, and otherwise its verification is
ECDSA's of a message's SHA-384 under that point. -/
theorem p384_ecdsa_public_key_new (h : Runs) (hvg : RunsP384) (hheld : Held) (hc : P384.Cached)
    (hsha : RunsSha512) (bytes : Slice U8) :
    high.signature.ecdsa.PublicKey.new high.signature.ecdsa.verify.P384_SHA384_FIXED bytes ⦃ r =>
      P384.x962Outcome bytes.val (fun pk => ∀ (msg sig : Slice U8), msg.length ≤ maxInput →
        high.signature.ecdsa.PublicKey.verify pk msg sig ⦃ v =>
          ecdsaVerdict384 (some (p384Coords bytes.val)) (sha384E msg.val) sig.val v ⦄) r ⦄ := by
  unfold high.signature.ecdsa.PublicKey.new high.signature.ecdsa.verify.P384_SHA384_FIXED
    high.signature.ecdsa.parse_ecdsa_p384_sha384_fixed high.signature.ecdsa.EcdsaVerifier.parse_p384_sha384_fixed
  simp only
  step with ecdsa_vk_from_x962_spec h hheld hc bytes as ⟨r, hr⟩
  unfold P384.x962Outcome at hr ⊢
  rcases hb : bytes.val.head? with _ | b0
  · simp only [hb] at hr ⊢; subst hr; simp
  · simp only [hb] at hr ⊢
    split_ifs at hr ⊢ with h4 hl hon
    · obtain ⟨vk, rfl, hvk⟩ := hr
      simp only [bind_ok]
      step with P256.encoded_point_copy_from_spec bytes (by simp [hl]) as ⟨p, ep, hp, _hpl, _hpt⟩
      subst hp
      simp only [WP.spec_ok]
      refine ⟨_, rfl, fun msg sig hm => ?_⟩
      obtain ⟨dd, dg, hhash, hdg', hdg, he⟩ := ecdsa_sha384_spec hsha msg hm
      rw [← he]
      exact WP.spec_mono (ecdsa_verify_spec h hvg hc Sha384Sig vk _ hvk (p384_order _ hvk.1 hvk.2.1) msg sig dg dd
        hhash hdg' hdg)
        fun r hr => P384.verdict_of_outcome hr
    · subst hr; simp
    · subst hr; simp
    · subst hr; simp

end rind.x86_64
