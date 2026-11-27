import Rind.X86_64.S2nBignum
import Rind.X86_64.Dispatch
import Rind.X86_64.X25519Bytes
open Aeneas Aeneas.Std Result rind.spec

/-!
# X25519, proven from rind's agreement API to its routines' contracts

The `x25519_*` theorems state what the agreement API returns for X25519,
through the dispatch `Rind.X86_64.Dispatch` models, in terms of `cpuX25519 o`,
RFC 7748's X25519 as the routines the CPU runs state it, for the result `o`
of the IFMA check, `CurveIfma o`: HOL Light's `rfcx25519` for s2n-bignum's,
and on x86_64 CPUs with AVX-512 IFMA, VG's spec, `vgX25519`, for
pyca/verified-garbage's. `admin/prove` writes the aarch64 proof from this
file by renaming the target, and the armv7 one, whose hypothesis on the CPU
is `Rind.Armv7.Curve25519`'s: that `o` is the NEON check's result, and that
the CPU lacks NEON, so `cpuX25519 o` is curve25519-dalek's X25519 as
Beneficial AI Foundation's spec states it.
-/

namespace rind.x86_64

variable {o : Option low.x86_64.curve25519_ifma.Curve25519Ifma}

/-! ## `mid::x25519` -/

@[step]
theorem public_key_spec (h : Runs) (hi : CurveIfma o) (k : mid.x25519.PrivateKey) :
    mid.x25519.PrivateKey.public_key k ⦃ pk => wordsNat pk.val = cpuX25519 o (wordsNat k.val) 9 ⦄ := by
  unfold mid.x25519.PrivateKey.public_key low.ct.into_public
  step*

@[step]
theorem as_bytes_spec (h : Runs) (pk : mid.x25519.PublicKey) :
    mid.x25519.PublicKey.as_bytes pk ⦃ b => leNat b.val = wordsNat pk.val ⦄ := by
  unfold mid.x25519.PublicKey.as_bytes
  step*

@[step]
theorem try_from_slice_spec (h : Runs) (b : Slice U8) :
    mid.x25519.PublicKey.try_from_slice b ⦃ r =>
      if b.length = 32 then ∃ pk, r = .Ok pk ∧ wordsNat pk.val = leNat b.val
      else r = .Err (.KeyRejected .WrongLength) ⦄ := by
  unfold mid.x25519.PublicKey.try_from_slice
  step
  step as ⟨o, ho⟩
  simp only [core.option.Option.map,
    P.Insts.CoreOpsFunctionFnOnceTupleArrayU644PublicKey.call_once, mid.x25519.PublicKey.constructor,
    error.Error.Insts.CoreConvertFromKeyFormatError.from, core.option.Option.ok_or]
  split_ifs at ho with hb
  · obtain ⟨w, rfl, hw⟩ := ho
    simp [hb, hw]
  · subst ho
    simp [hb]

@[step]
theorem from_bytes_spec (h : Runs) (b : Slice U8) :
    mid.x25519.PrivateKey.from_bytes b ⦃ r =>
      if b.length = 32 then ∃ k, r = .Ok k ∧ wordsNat k.val = leNat b.val
      else r = .Err (.KeyRejected .WrongLength) ⦄ := by
  unfold mid.x25519.PrivateKey.from_bytes
  step
  step as ⟨o, ho⟩
  simp only [core.option.Option.map,
    mid.x25519.PrivateKey.from_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU644PrivateKey.call_once,
    low.ct.into_secret,
    error.Error.Insts.CoreConvertFromKeyFormatError.from, core.option.Option.ok_or]
  split_ifs at ho with hb
  · obtain ⟨w, rfl, hw⟩ := ho
    simp [hb, hw]
  · subst ho
    simp [hb]

theorem wordsNat_ZERO : wordsNat mid.x25519.ZERO.val = 0 := by
  unfold mid.x25519.ZERO
  simp [wordsNat, Array.repeat, Nat.ofDigits]

@[step]
theorem diffie_hellman_spec (h : Runs) (hi : CurveIfma o) (k : mid.x25519.PrivateKey) (peer : mid.x25519.PublicKey) :
    mid.x25519.PrivateKey.diffie_hellman k peer ⦃ r =>
      if cpuX25519 o (wordsNat k.val) (wordsNat peer.val) = 0 then r = .Err (.KeyRejected .SmallOrder)
      else ∃ s, r = .Ok s ∧ leNat s.val = cpuX25519 o (wordsNat k.val) (wordsNat peer.val) ⦄ := by
  unfold mid.x25519.PrivateKey.diffie_hellman low.ct.into_public
  step*
  · have hz : wordsNat s1.val = 0 := by rw [s1_post, Array.val_to_slice, wordsNat_ZERO]
    rw [s_post, Array.val_to_slice, res1_post, hz] at b1_post
    simp only [error.Error.Insts.CoreConvertFromKeyFormatError.from]
    simp_all
  · have hz : wordsNat s1.val = 0 := by rw [s1_post, Array.val_to_slice, wordsNat_ZERO]
    rw [s_post, Array.val_to_slice, res1_post, hz] at b1_post
    simp_all

/-! ## The agreement API's X25519 impl, `high::agreement` -/

theorem encode_public_spec (h : Runs) (hi : CurveIfma o) (k : mid.x25519.PrivateKey) (algorithm : high.agreement.Algorithm) :
    high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.encode_public k algorithm ⦃ pk =>
      high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
        b.length = 32 ∧ leNat b.val = cpuX25519 o (wordsNat k.val) 9 ⦄ ⦄ := by
  unfold high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.encode_public high.agreement.PublicKey.from_encoding
    high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref low.generic.zeroise.ZeroableRef.new
  step as ⟨pk, hpk⟩
  step as ⟨a, ha⟩
  step as ⟨sl, hsl⟩
  subst hsl
  have hlen : a.to_slice.len.val = 32 := by simp
  step as ⟨s, back, hs, hsl, hback⟩
  step as ⟨x, hx⟩
  step as ⟨b, hb, hbl⟩
  have ha32 : (a.val).length = 32 := a.property
  have hz : (Array.repeat 133#usize 0#u8).val.length = 133 := (Array.repeat 133#usize 0#u8).property
  refine ⟨by rw [hbl, hlen], ?_⟩
  have := take_setSlice! (Array.repeat 133#usize 0#u8).val a.val 0 (by omega)
  rw [hb, Array.val_to_slice, hback, hx, Array.val_to_slice, hlen, List.slice]
  simp only [ha32, Nat.zero_add, List.take_zero, List.nil_append] at this
  simp only [List.drop_zero, Nat.sub_zero, this, ha, hpk]

theorem agree_spec (h : Runs) (hi : CurveIfma o) (k : mid.x25519.PrivateKey) (peer : Slice U8) :
    high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.agree k peer ⦃ r =>
      if peer.length = 32 then
        if cpuX25519 o (wordsNat k.val) (leNat peer.val) = 0 then
          r = .Err (.KeyRejected .SmallOrder)
        else ∃ s, r = .Ok (.X25519 s) ∧ leNat s.val = cpuX25519 o (wordsNat k.val) (leNat peer.val)
      else r = .Err (.KeyRejected .WrongLength) ⦄ := by
  unfold high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.agree
  step as ⟨r, hr⟩
  by_cases hp : peer.length = 32
  · simp only [hp, ↓reduceIte] at hr ⊢
    obtain ⟨pk, rfl, hpk⟩ := hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    step as ⟨r1, hr1⟩
    rw [hpk] at hr1
    split_ifs at hr1 ⊢ with hz
    · subst hr1
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · obtain ⟨sec, rfl, hsec⟩ := hr1
      simp [hsec]
  · simp only [hp, ↓reduceIte] at hr ⊢
    subst hr
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem random_spec (h : Runs) (r : core.result.Result Unit getrandom.error.Error)
    (out : Slice U8) (hout : out.length = 32)
    (hfill : getrandom.fill (Array.repeat 32#usize 0#u8).to_slice = ok (r, out)) :
    high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.random ⦃ key =>
      match r with
      | .Ok _ => ∃ k, key = core.result.Result.Ok k ∧ wordsNat k.val = leNat out.val
      | .Err _ => key = core.result.Result.Err error.Error.RngFailed ⦄ := by
  unfold high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.random mid.x25519.PrivateKey.new_random
    mid.rng.SystemRandom.Insts.RindMidRngRandomSource.fill low.ct.into_secret
  rcases r with _ | e <;> simp only [Array.to_slice_mut, lift] <;> step <;> rw [hfill]
  · simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch]
    have hfrom : ((Array.repeat 32#usize 0#u8).from_slice out).val = out.val := by
      simp [Array.from_slice, hout]
    step as ⟨k, hk⟩
    simp [hk, hfrom]
  · simp [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
      mid.rng.RandomSourceSystemRandom.fill.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem load_scalar_spec (h : Runs) (hi : CurveIfma o) (algorithm : high.agreement.Algorithm) (b : Slice U8) :
    high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.load algorithm (.Scalar b) ⦃ r =>
      if b.length = 32 then ∃ k pk, r = .Ok (k, pk) ∧ wordsNat k.val = leNat b.val ∧
        high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
          b.length = 32 ∧ leNat b.val = cpuX25519 o (wordsNat k.val) 9 ⦄
      else r = .Err (.KeyRejected .WrongLength) ⦄ := by
  unfold high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.load
  step with from_bytes_spec h b as ⟨r, hr⟩
  split_ifs at hr ⊢
  · obtain ⟨k, rfl, hk⟩ := hr
    step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec as ⟨cf, hcf⟩
    subst hcf
    simp only
    step with encode_public_spec h hi k algorithm as ⟨pk, hpk⟩
    exact ⟨k, pk, rfl, hk, hpk⟩
  · subst hr
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-! ## The agreement API, `high::agreement`, through the modelled dispatch -/

/-- `key` is an X25519 key whose scalar is `d`, holding its public key: the
u-coordinate of `d` times the base point, as RFC 7748's 32 little-endian
bytes. -/
def x25519Key (o : Option low.x86_64.curve25519_ifma.Curve25519Ifma) (d : Nat) (key : high.agreement.PrivateKey) : Prop :=
  ∃ k : high.agreement.Keyed high.agreement.X25519Curve mid.x25519.PrivateKey, key.«private» = .X25519 k ∧
    wordsNat k.key.val = d ∧
    high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref key.«public» ⦃ b =>
      b.length = 32 ∧ leNat b.val = cpuX25519 o d 9 ⦄

/-- A key and its public key, as `Keyed::private_key` keeps them, is an
`x25519Key`. -/
theorem private_key_spec (k : mid.x25519.PrivateKey) (pk : high.agreement.PublicKey)
    (hpk : high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
      b.length = 32 ∧ leNat b.val = cpuX25519 o (wordsNat k.val) 9 ⦄) :
    high.agreement.Keyed.private_key high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey k pk ⦃ key =>
      x25519Key o (wordsNat k.val) key ⦄ := by
  simp only [high.agreement.Keyed.private_key, high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.wrap,
    bind_ok, WP.spec_ok]
  exact ⟨{ key := k, ops := () }, rfl, rfl, hpk⟩

/-- A generated X25519 key's scalar is the 32 bytes the random source drew,
read little-endian, and a failed draw is refused. The draw itself is outside
the functional spec. -/
theorem x25519_generate (h : Runs) (hi : CurveIfma o) (r : core.result.Result Unit getrandom.error.Error)
    (out : Slice U8) (hout : out.length = 32)
    (hfill : getrandom.fill (Array.repeat 32#usize 0#u8).to_slice = ok (r, out)) :
    high.agreement.PrivateKey.generate high.agreement.X25519 ⦃ key =>
      match r with
      | .Ok _ => ∃ key', key = core.result.Result.Ok key' ∧ x25519Key o (leNat out.val) key'
      | .Err _ => key = core.result.Result.Err error.Error.RngFailed ⦄ := by
  unfold high.agreement.PrivateKey.generate high.agreement.X25519 high.agreement.Algorithm.generate
    high.agreement.Keyed.generate
  step with random_spec h r out hout hfill as ⟨key, hkey⟩
  rcases r with _ | _ <;> simp only at hkey
  · obtain ⟨k, rfl, hk⟩ := hkey
    simp only
    step with encode_public_spec h hi k .X25519 as ⟨pk, hpk⟩
    step with private_key_spec k pk hpk as ⟨key', hkey'⟩
    exact ⟨key', rfl, hk ▸ hkey'⟩
  · simp [hkey]

/-- An X25519 key loaded from its scalar is refused unless it is 32 bytes, and
otherwise is those bytes, read little-endian, as `x25519_generate`'s is the
random source's. -/
theorem x25519_from_scalar (h : Runs) (hi : CurveIfma o) (b : Slice U8) :
    high.agreement.PrivateKey.from_scalar high.agreement.X25519 b ⦃ key =>
      if b.length = 32 then ∃ key', key = core.result.Result.Ok key' ∧ x25519Key o (leNat b.val) key'
      else key = core.result.Result.Err (.KeyRejected .WrongLength) ⦄ := by
  unfold high.agreement.PrivateKey.from_scalar high.agreement.X25519 high.agreement.Algorithm.load
    high.agreement.Keyed.load
  step with load_scalar_spec h hi .X25519 b as ⟨r, hr⟩
  split_ifs at hr ⊢
  · obtain ⟨k, pk, rfl, hk, hpk⟩ := hr
    simp only
    step with private_key_spec k pk hpk as ⟨key', hkey'⟩
    exact ⟨key', rfl, hk ▸ hkey'⟩
  · subst hr
    simp

/-- An X25519 key's public key: the u-coordinate of its scalar times the base
point, as RFC 7748's 32 little-endian bytes, which `x25519_generate` and
`x25519_from_scalar` show every key holds. -/
theorem x25519_public_key (key : high.agreement.PrivateKey) (d : Nat) (hkey : x25519Key o d key) :
    (do
      let pk ← high.agreement.PrivateKey.public_key key
      high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk) ⦃ b =>
      b.length = 32 ∧ leNat b.val = cpuX25519 o d 9 ⦄ := by
  obtain ⟨_, _, _, hpk⟩ := hkey
  simpa [high.agreement.PrivateKey.public_key] using hpk

/-- An X25519 agreement with the peer's encoded public key: refused unless it
is 32 bytes, refused for the all-zero output of a small-order point, and
otherwise RFC 7748's X25519 of this key's scalar and the peer's u-coordinate. -/
theorem x25519_agree (h : Runs) (hi : CurveIfma o) (key : high.agreement.PrivateKey)
    (k : high.agreement.Keyed high.agreement.X25519Curve mid.x25519.PrivateKey) (hk : key.«private» = .X25519 k)
    (peer : Slice U8) :
    high.agreement.PrivateKey.agree key peer ⦃ r =>
      if peer.length = 32 then
        if cpuX25519 o (wordsNat k.key.val) (leNat peer.val) = 0 then
          r = .Err (.KeyRejected .SmallOrder)
        else ∃ s, r = .Ok (.X25519 s) ∧ leNat s.val = cpuX25519 o (wordsNat k.key.val) (leNat peer.val)
      else r = .Err (.KeyRejected .WrongLength) ⦄ := by
  unfold high.agreement.PrivateKey.agree high.agreement.Keyed.agree
  rw [hk]
  step with agree_spec h hi k.key peer as ⟨r, hr⟩
  split_ifs at hr ⊢ <;> first
    | (subst hr; simp)
    | (obtain ⟨s, rfl, hs⟩ := hr; simp [hs])

/-- The shared secret's bytes are the ones `x25519_agree` states. -/
theorem x25519_shared_secret (s : mid.x25519.SharedSecret) :
    high.agreement.SharedSecret.Insts.CoreConvertAsRefSliceU8.as_ref (.X25519 s) ⦃ b =>
      b.val = s.val ⦄ := by
  simp [high.agreement.SharedSecret.Insts.CoreConvertAsRefSliceU8.as_ref, Array.val_to_slice]

end rind.x86_64
