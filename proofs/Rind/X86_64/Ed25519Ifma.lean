import Rind.X86_64.Ed25519
open Aeneas Aeneas.Std Result rind.spec

/-!
# Ed25519 on pyca/verified-garbage's AVX-512 IFMA routines

On a CPU whose IFMA check returns a token (`CurveIfma (some t)`), each Ed25519
key picks pyca/verified-garbage's (VG's) whole operations once, as its path:
key-pair derivation, signing, and verification, whose contracts
`Rind.X86_64.VgCurve25519` restates. Rind's glue around them is proven here,
from the signature API down to those axioms: the key types, which keep the
seed's digest and public key VG's key-pair derivation writes and pass them to
its signing, as its precondition asks, and key loading's checks, which run on
every CPU. The theorems state the API's results in terms of VG's RFC 8032 spec,
`VG.Spec.Ed25519`, over bytes as VG takes them, `bvs`; `Rind.X86_64.Ed25519`
states them on the other CPUs in terms of HOL Light's.

Verification is proven here only on VG's routines: on the other x86_64 CPUs it
checks a multiple of the equation with half-size scalars, which nothing proves
yet.
-/

namespace rind.x86_64

open low.x86_64.curve25519_ifma (Curve25519Ifma)

/-! ## Keys on VG's routines, `mid::ed25519` -/

/-- A signing key whose private key is the 32-byte `seed`, on VG's routines:
the seed's SHA-512 digest and public key as VG's spec states them. -/
def VgSeedKey (k : mid.ed25519.SigningKey) (seed : List U8) : Prop :=
  k.seed.val = seed ∧ bvs k.expanded.val = VG.Spec.Sha512.sha512 (bvs seed) ∧
    bvs k.verifying_key.bytes.val = VG.Spec.Ed25519.publicKey (bvs seed) ∧
    ∃ t, k.verifying_key.path = .Ifma t

theorem VgSeedKey.clone {k : mid.ed25519.SigningKey} {seed : List U8} (hk : VgSeedKey k seed) :
    mid.ed25519.Path.Insts.CoreCloneClone.clone k.verifying_key.path ⦃ p => p = k.verifying_key.path ⦄ := by
  obtain ⟨t, ht⟩ := hk.2.2.2
  rw [ht]
  simp [mid.ed25519.Path.Insts.CoreCloneClone.clone,
    low.x86_64.curve25519_ifma.Curve25519Ifma.Insts.CoreCloneClone.clone]

/-- On VG's routines, a key made from a seed holds VG's digest and public key
of it. -/
theorem from_seed_ifma_spec {t : Curve25519Ifma} (hi : CurveIfma (some t)) : FromSeed VgSeedKey := by
  intro seed
  unfold mid.ed25519.SigningKey.from_seed low.ct.into_public low.ct.into_secret
  simp only [bind_ok]
  rw [hi]
  simp only [bind_ok]
  step as ⟨e, b, he, hb⟩
  exact ⟨rfl, he, hb, t, rfl⟩

/-- `sign` with a key on VG's routines whose private key is `seed`: VG's
RFC 8032 signature. -/
theorem mid_sign_ifma_spec (k : mid.ed25519.SigningKey) (seed : List U8) (hk : VgSeedKey k seed)
    (msg : Slice U8) :
    mid.ed25519.SigningKey.sign k msg ⦃ sig => bvs sig.val = VG.Spec.Ed25519.sign (bvs seed) (bvs msg.val) ⦄ := by
  obtain ⟨hs, he, hp, t, hpath⟩ := hk
  have hlen : (bvs seed).length = 32 := by rw [length_bvs, ← hs]; exact k.seed.property
  unfold mid.ed25519.SigningKey.sign low.ct.into_public
  rw [hpath]
  simp only
  step with vg_ed25519_sign_spec t k.expanded k.verifying_key.bytes msg ⟨bvs seed, hlen, he, hp⟩ as ⟨sig, hsig⟩
  exact hsig _ hlen he

open Classical in
/-- On VG's routines, a key loads as on the other CPUs, but runs VG's
verification on its bytes. -/
theorem mid_from_bytes_ifma_spec (h : Runs) (hheld : low.entry.Entry.assert_held = ok ()) {t : Curve25519Ifma}
    (hi : CurveIfma (some t)) (bytes : Slice U8) :
    mid.ed25519.VerifyingKey.from_bytes bytes ⦃ r =>
      if bytes.length = 32 then
        if edValidEncode (leNat bytes.val) then
          ∃ vk, r = .Ok vk ∧ vk.bytes.val = bytes.val ∧ vk.path = .Ifma t
        else r = .Err (.KeyRejected .NotOnCurve)
      else r = .Err (.KeyRejected .WrongLength) ⦄ := by
  unfold mid.ed25519.VerifyingKey.from_bytes
  rw [hheld, bind_ok]
  step with try_from_shared_spec 32#usize bytes as ⟨r, hr⟩
  by_cases hl : bytes.length = 32
  · simp only [hl, ↓reduceIte] at hr ⊢
    obtain ⟨a, rfl, ha⟩ := hr
    simp only
    step as ⟨r1, hr1⟩
    rw [ha] at hr1
    split_ifs at hr1 ⊢ with hv
    · obtain ⟨pt, rfl, hpt⟩ := hr1
      rw [hi]
      simp [core.result.Result.Insts.CoreOpsTry.branch, ha]
    · subst hr1
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp only [hl, ↓reduceIte] at hr ⊢
    obtain ⟨e, rfl⟩ := hr
    simp [error.Error.Insts.CoreConvertFromKeyFormatError.from]

/-- `verify` with a key on VG's routines: VG's RFC 8032 verification of the
key's bytes. -/
theorem mid_verify_ifma_spec (vk : mid.ed25519.VerifyingKey) {t : Curve25519Ifma} (hp : vk.path = .Ifma t)
    (sig : Std.Array U8 64#usize) (msg : Slice U8) :
    mid.ed25519.VerifyingKey.verify vk sig msg ⦃ r =>
      r = if VG.Spec.Ed25519.verify (bvs vk.bytes.val) (bvs msg.val) (bvs sig.val) then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  unfold mid.ed25519.VerifyingKey.verify
  rw [hp]
  simp only
  step as ⟨b, hb⟩
  rw [← hb]
  split <;> simp_all

/-- VG's verification refuses a signature that is not 64 bytes. -/
theorem vg_verify_length (pk msg sig : List VG.Byte) (hs : sig.length ≠ 64) :
    VG.Spec.Ed25519.verify pk msg sig = false := by
  simp [VG.Spec.Ed25519.verify, VG.Spec.Ed25519.verifyEquation, hs]

theorem high_verify_ifma_spec (h : Runs) (vk : high.ed25519.Ed25519VerifyingKey) {t : Curve25519Ifma}
    (hp : vk.path = .Ifma t) (sig msg : Slice U8) :
    high.ed25519.Ed25519VerifyingKey.verify vk sig msg ⦃ r =>
      r = if VG.Spec.Ed25519.verify (bvs (mid.ed25519.VerifyingKey.bytes vk).val) (bvs msg.val) (bvs sig.val) then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  unfold high.ed25519.Ed25519VerifyingKey.verify
  step
  step with try_from_shared_spec 64#usize sig as ⟨r, hr⟩
  by_cases hl : sig.length = 64
  · simp only [hl, ↓reduceIte] at hr
    obtain ⟨a, rfl, ha⟩ := hr
    simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch]
    step*
    step with mid_verify_ifma_spec vk hp a msg as ⟨r, hr⟩
    rw [hr, ha]
  · simp only [hl, ↓reduceIte] at hr
    obtain ⟨e, rfl⟩ := hr
    have hn := vg_verify_length (bvs (mid.ed25519.VerifyingKey.bytes vk).val) (bvs msg.val) (bvs sig.val)
      (by rw [length_bvs]; exact hl)
    simp [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
      high.ed25519.Ed25519VerifyingKey.verify.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hn]

/-! ## The signature API, `high::signature::ed25519` -/

/-- A key pair on VG's routines whose private key is the 32-byte `seed`,
holding its public key. -/
def VgKeyPairOf (kp : high.signature.ed25519.KeyPair) (seed : List U8) : Prop :=
  VgSeedKey kp.key seed ∧ kp.«public» = kp.key.verifying_key

/-- `ed25519_generate` on VG's routines: a generated key pair's private key is
the 32 bytes the random source drew, and a failed draw is refused. -/
theorem ed25519_generate_ifma (h : Runs) {t : Curve25519Ifma} (hi : CurveIfma (some t))
    (r : core.result.Result Unit getrandom.error.Error)
    (out : Slice U8) (hout : out.length = 32)
    (hfill : getrandom.fill (Array.repeat 32#usize 0#u8).to_slice = ok (r, out)) :
    high.signature.ed25519.KeyPair.generate ⦃ kp =>
      match r with
      | .Ok _ => ∃ k, kp = core.result.Result.Ok k ∧ VgKeyPairOf k out.val
      | .Err _ => kp = core.result.Result.Err error.Error.RngFailed ⦄ :=
  ed25519_generate_of h VgSeedKey (from_seed_ifma_spec hi) (fun _ _ hk => hk.clone) r out hout hfill

/-- `ed25519_from_seed_and_public_key` on VG's routines: refused unless the
seed is 32 bytes and the public key is VG's of it, and otherwise its private
key is the seed. -/
theorem ed25519_from_seed_and_public_key_ifma (h : Runs) {t : Curve25519Ifma} (hi : CurveIfma (some t))
    (seed pk : Slice U8) :
    high.signature.ed25519.KeyPair.from_seed_and_public_key seed pk ⦃ r =>
      if seed.length = 32 then
        if VG.Spec.Ed25519.publicKey (bvs seed.val) = bvs pk.val then ∃ kp, r = .Ok kp ∧ VgKeyPairOf kp seed.val
        else r = .Err (.KeyRejected .MismatchedPublicKey)
      else r = .Err (.KeyRejected .WrongLength) ⦄ :=
  ed25519_from_seed_and_public_key_of h VgSeedKey (from_seed_ifma_spec hi) (fun _ _ hk => hk.clone) seed pk
    (VG.Spec.Ed25519.publicKey (bvs seed.val) = bvs pk.val)
    (fun _ hk => by rw [← hk.2.2.1, rind.spec.bvs_inj])

/-- `ed25519_sign` on VG's routines: VG's RFC 8032 PureEd25519 signature of the
message under the key pair's seed. -/
theorem ed25519_sign_ifma (h : Runs) (kp : high.signature.ed25519.KeyPair) (seed : List U8)
    (hkp : VgKeyPairOf kp seed) (msg : Slice U8) :
    (do
      let sig ← high.signature.ed25519.KeyPair.sign kp msg
      high.signature.ed25519.Signature.Insts.CoreConvertAsRefSliceU8.as_ref sig) ⦃ b =>
      bvs b.val = VG.Spec.Ed25519.sign (bvs seed) (bvs msg.val) ⦄ := by
  unfold high.signature.ed25519.KeyPair.sign high.signature.ed25519.Signature.Insts.CoreConvertAsRefSliceU8.as_ref
    high.ed25519.Ed25519SigningKey.sign
  step with new_secret_spec h
  step with mid_sign_ifma_spec kp.key seed hkp.1 msg as ⟨a, ha⟩
  simpa [Array.val_to_slice] using ha

/-- `ed25519_key_pair_public_key` on VG's routines: VG's RFC 8032 public key of
the key pair's seed. -/
theorem ed25519_key_pair_public_key_ifma (kp : high.signature.ed25519.KeyPair) (seed : List U8)
    (hkp : VgKeyPairOf kp seed) :
    (do
      let pk ← high.signature.ed25519.KeyPair.public_key kp
      high.signature.ed25519.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk) ⦃ b =>
      bvs b.val = VG.Spec.Ed25519.publicKey (bvs seed) ⦄ := by
  unfold high.signature.ed25519.KeyPair.public_key high.signature.ed25519.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref
    high.ed25519.Ed25519VerifyingKey.bytes mid.ed25519.VerifyingKey.impl.bytes
  obtain ⟨⟨-, -, hkb, -⟩, hpub⟩ := hkp
  simp only [bind_ok, WP.spec_ok, Array.val_to_slice]
  rw [hpub]
  exact hkb

/-- Verification with a key pair's public key on VG's routines: VG's RFC 8032
verification with its seed's public key. -/
theorem ed25519_key_pair_verify_ifma (h : Runs) (kp : high.signature.ed25519.KeyPair) (seed : List U8)
    (hkp : VgKeyPairOf kp seed) (msg sig : Slice U8) :
    (do
      let pk ← high.signature.ed25519.KeyPair.public_key kp
      high.signature.ed25519.PublicKey.verify pk msg sig) ⦃ r =>
      r = if VG.Spec.Ed25519.verify (VG.Spec.Ed25519.publicKey (bvs seed)) (bvs msg.val) (bvs sig.val) then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  unfold high.signature.ed25519.KeyPair.public_key high.signature.ed25519.PublicKey.verify
  obtain ⟨⟨-, -, hkb, t, hkp⟩, hpub⟩ := hkp
  simp only [bind_ok]
  have hb : bvs (mid.ed25519.VerifyingKey.bytes kp.«public»).val = VG.Spec.Ed25519.publicKey (bvs seed) := by
    rw [hpub]; exact hkb
  rw [← hb]
  exact high_verify_ifma_spec h kp.«public» (t := t) (by rw [hpub]; exact hkp) sig msg

open Classical in
/-- An Ed25519 public key parsed from its encoding on VG's routines: refused
as on the other CPUs, unless it is 32 bytes, if its y-coordinate is one of
libsodium's small-order list, and unless it encodes a point of the group, and
otherwise its verification is VG's RFC 8032 verification with those bytes. -/
theorem ed25519_public_key_new_ifma (h : Runs) (hheld : low.entry.Entry.assert_held = ok ()) {t : Curve25519Ifma}
    (hi : CurveIfma (some t)) (key : Slice U8) :
    high.signature.ed25519.PublicKey.new key ⦃ r =>
      if key.length ≠ 32 then r = .Err (.KeyRejected .WrongLength)
      else if leNat key.val % 2 ^ 255 ∈ edSmallOrderY then r = .Err (.KeyRejected .SmallOrder)
      else if edValidEncode (leNat key.val) then
        ∃ pk, r = .Ok pk ∧ ∀ msg sig : Slice U8,
          high.signature.ed25519.PublicKey.verify pk msg sig ⦃ v =>
            v = if VG.Spec.Ed25519.verify (bvs key.val) (bvs msg.val) (bvs sig.val) then
              (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄
      else r = .Err (.KeyRejected .NotOnCurve) ⦄ := by
  unfold high.signature.ed25519.PublicKey.new
  step with high_from_bytes_of h (fun vk => vk.path = .Ifma t) key (mid_from_bytes_ifma_spec h hheld hi key) as ⟨r, hr⟩
  split_ifs at hr ⊢ with hl hso hv
  · subst hr; simp [core.result.Result.map]
  · subst hr; simp [core.result.Result.map]
  · obtain ⟨vk, rfl, hvb, hvp⟩ := hr
    simp only [core.result.Result.map, P.Insts.CoreOpsFunctionFnOnceTupleEd25519VerifyingKeyPublicKey.call_once,
      high.signature.ed25519.PublicKey.constructor, bind_ok, WP.spec_ok]
    refine ⟨_, rfl, fun msg sig => ?_⟩
    simp only [high.signature.ed25519.PublicKey.verify]
    have := high_verify_ifma_spec h vk hvp sig msg
    rwa [hvb] at this
  · subst hr; simp [core.result.Result.map]

end rind.x86_64
