import Rind.Aarch64.Ed25519
open Aeneas Aeneas.Std Result rind.spec

/-!
# Ed25519 verification on aarch64, proven to s2n-bignum's contracts

aarch64's verification still recomputes `R` with s2n-bignum's
`edwards25519_scalarmuldouble`, whose contract proves it, while x86_64's
checks a multiple of the equation with half-size scalars, which nothing
proves yet (`quest/m4/verified/ed25519-half-scalar.md`). So these theorems,
unlike the rest of `Rind.Aarch64.Ed25519`, are not written from the x86_64
file, and live here.
-/

namespace rind.aarch64

@[step]
theorem scalarmuldouble_spec (_h : Runs) (_hd : RunsDouble) (k : Std.Array U64 4#usize) (pt : Std.Array U64 8#usize)
    (b : Std.Array U64 4#usize) :
    mid.ed25519.EdwardsPoint.scalarmuldouble k pt b ⦃ r =>
      ∀ P, edOnCurve P → edModDecodePair (pairNat pt.val) = P →
        pairNat r.val = edModEncodePair (edMul (edPow P (wordsNat k.val)) (edPow edB (wordsNat b.val))) ⦄ := by
  unfold mid.ed25519.EdwardsPoint.scalarmuldouble
  step*

open Classical in
/-- `verify` with a key whose point is `A`, a point of the group, and whose
bytes are `vk.bytes`: RFC 8032's verification. -/
theorem mid_verify_spec (h : Runs) (hd : RunsDouble) (hs : RunsSha512) (vk : mid.ed25519.VerifyingKey) (A : EdPoint)
    (hA : edOnCurve A) (hp : pairNat vk.point.val = edModEncodePair A)
    (sig : Std.Array U8 64#usize) (msg : Slice U8) (hm : msg.length + 64 < 2 ^ 64) :
    mid.ed25519.VerifyingKey.verify vk sig msg ⦃ r =>
      r = if ed25519Verifies A vk.bytes.val msg.val sig.val then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  unfold mid.ed25519.VerifyingKey.verify
  have hsig : sig.val.length = 64 := sig.property
  step*
  simp only [r_post, core.result.Result.Ok.injEq] at *
  have hs2 : s2.val = sig.val.drop 32 := by simp_all [Array.val_to_slice]
  have hr : r_sig.val = sig.val.take 32 := by simp_all [Array.val_to_slice]
  rw [hs2] at o_post
  by_cases hS : leNat (sig.val.drop 32) < n25519
  · simp only [hS, ↓reduceIte] at o_post
    obtain ⟨S, rfl, hSv⟩ := o_post
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch]
    step as ⟨s3, hs3⟩
    step with ed25519_digest_spec hs r_sig s3 msg (by simp [Slice.length, hs3] at *; omega)
      as ⟨k, hk⟩
    step as ⟨k1, hk1⟩
    step with negate_spec vk.point (by rw [hp]; exact (edModEncode_lt _).le) as ⟨ep, hep⟩
    step as ⟨ep1, hep1⟩
    have hR := hep1 (edNeg A) (edOnCurve_neg A hA) (by rw [hep, hp]; exact neg_decode A hA)
    step with compress_point_spec ep1 _ hR as ⟨r2, hr2⟩
    step as ⟨b, hb⟩
    have hr2l : r2.val.length = 32 := r2.property
    have hiff : r_sig.val = r2.val ↔ ed25519Verifies A vk.bytes.val msg.val sig.val := by
      rw [hk1, hk, hSv, hs3, Array.val_to_slice] at hr2
      rw [ed25519Verifies, ← hr]
      constructor
      · intro he
        refine ⟨hsig, hS, ?_⟩
        rw [← hr2, he]
      · rintro ⟨-, -, he⟩
        exact leNat_inj _ _ (by simp [hr2l, r_sig_post]) (by rw [he, hr2])
    rw [← hiff, ← hb]
    split <;> simp_all
  · simp only [hS, ↓reduceIte] at o_post
    subst o_post
    have hn : ¬ ed25519Verifies A vk.bytes.val msg.val sig.val := fun ⟨_, h, _⟩ => hS h
    simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hn]

open Classical in
theorem high_verify_spec (h : Runs) (hd : RunsDouble) (hs : RunsSha512) (vk : high.ed25519.Ed25519VerifyingKey) (A : EdPoint)
    (hA : edOnCurve A) (hp : pairNat vk.point.val = edModEncodePair A) (sig msg : Slice U8)
    (hm : msg.length + 64 < 2 ^ 64) :
    high.ed25519.Ed25519VerifyingKey.verify vk sig msg ⦃ r =>
      r = if ed25519Verifies A vk.bytes.val msg.val sig.val then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  unfold high.ed25519.Ed25519VerifyingKey.verify
  step
  step with try_from_shared_spec 64#usize sig as ⟨r, hr⟩
  by_cases hl : sig.length = 64
  · simp only [hl, ↓reduceIte] at hr
    obtain ⟨a, rfl, ha⟩ := hr
    simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch]
    step*
    step with mid_verify_spec h hd hs vk A hA hp a msg hm as ⟨r, hr⟩
    rw [hr, ha]
  · simp only [hl, ↓reduceIte] at hr
    obtain ⟨e, rfl⟩ := hr
    have hn : ¬ ed25519Verifies A vk.bytes.val msg.val sig.val := fun ⟨h64, _⟩ => hl h64
    simp [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
      high.ed25519.Ed25519VerifyingKey.verify.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hn]

open Classical in
/-- Verification with a key pair's public key: RFC 8032's verification with
its seed's public key, whose point is the base point times its secret scalar,
for a scalar whose multiple is a point of the group. -/
theorem ed25519_key_pair_verify (h : Runs) (hd : RunsDouble) (hs : RunsSha512) (kp : high.signature.Ed25519KeyPair)
    (seed : List U8) (hkp : KeyPairOf kp seed) (hA : edOnCurve (edPow edB (ed25519Scalar seed)))
    (msg sig : Slice U8) (hm : msg.length + 64 < 2 ^ 64) :
    (do
      let pk ← high.signature.Ed25519KeyPair.impl.public_key kp
      high.signature.PublicKey.verify pk msg sig) ⦃ r =>
      r = if ed25519Verifies (edPow edB (ed25519Scalar seed)) (ed25519PublicKey seed) msg.val sig.val then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  unfold high.signature.Ed25519KeyPair.impl.public_key high.signature.PublicKey.verify
    high.signature.Buffer.Insts.CoreConvertFromArrayU8N.from
  obtain ⟨⟨-, -, -, hkb, hkpt⟩, -⟩ := hkp
  step with high_public_key_spec h kp.key as ⟨vk, hvk⟩
  step*
  have hb : vk.bytes.val = ed25519PublicKey seed := by rw [hvk]; exact hkb
  rw [← hb]
  exact high_verify_spec h hd hs vk _ hA (by rw [hvk]; exact hkpt) sig msg hm

open Classical in
/-- An Ed25519 public key parsed from its encoding: refused unless it is 32
bytes, refused if its y-coordinate is one of libsodium's small-order list,
refused unless it encodes a point of the group, and otherwise its
verification is RFC 8032's with that point, for messages under 2⁶⁴ - 64
bytes. -/
theorem ed25519_public_key_new (h : Runs) (hd : RunsDouble) (hs : RunsSha512) (key : Slice U8) :
    high.signature.PublicKey.new high.signature.verify.ED25519 key ⦃ r =>
      if key.length ≠ 32 then r = .Err (.KeyRejected .WrongLength)
      else if leNat key.val % 2 ^ 255 ∈ edSmallOrderY then r = .Err (.KeyRejected .SmallOrder)
      else if edValidEncode (leNat key.val) then
        ∃ pk, r = .Ok pk ∧ ∀ msg sig : Slice U8, msg.length + 64 < 2 ^ 64 →
          high.signature.PublicKey.verify pk msg sig ⦃ v =>
            v = if ed25519Verifies (edDecode (leNat key.val)) key.val msg.val sig.val then
              (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄
      else r = .Err (.KeyRejected .NotOnCurve) ⦄ := by
  unfold high.signature.PublicKey.new high.signature.verify.ED25519 high.signature.parse_ed25519
  simp only
  step with high_from_bytes_spec h hs key as ⟨r, hr⟩
  split_ifs at hr ⊢ with hl hso hv
  · subst hr; simp
  · subst hr; simp
  · obtain ⟨vk, rfl, hvb, hvp⟩ := hr
    simp only
    have hl' : key.length = 32 := by simpa using hl
    step with copy_from_ok 2592#usize key (by simp [hl']) as ⟨b, enc, hb⟩
    subst hb
    simp only [WP.spec_ok]
    refine ⟨_, rfl, fun msg sig hm => ?_⟩
    simp only [high.signature.PublicKey.verify]
    have := high_verify_spec h hd hs vk _ (edDecode_spec _ hv).1 hvp sig msg hm
    rwa [hvb] at this
  · subst hr; simp

end rind.aarch64
