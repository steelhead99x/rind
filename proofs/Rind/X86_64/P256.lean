import Rind.X86_64.P256Base
import Rind.P256Multiples
open Aeneas Aeneas.Std Result rind.spec

/-!
# P-256 key generation, proven from rind's agreement API to s2n-bignum's contracts

The `p256_*` theorems state the keys the agreement API generates and loads for
`ECDH_P256`, in terms of `p256Pow`, HOL Light's `group_pow p256_group`,
through the dispatch `Rind.X86_64.Dispatch` and `Rind.X86_64.P256Dispatch`
model. Agreement itself is `Rind.X86_64.P256Agree`'s. Key generation
multiplies the generator as `Rind.X86_64.P256Base` states, which each target
proves its own way. `admin/prove` writes the aarch64 proof from this file by
renaming the target.
-/

namespace rind.x86_64

/-! ## What the theorems state -/

/-- `b` is X9.62's uncompressed encoding of `d` times the generator. -/
def p256PublicKey (d : Nat) (b : List U8) : Prop :=
  b.length = 65 ∧ b.head? = some 4#u8 ∧ p256Pow p256G d = some (x962Coords b)

/-- `key` is a P-256 key whose scalar is `d`, holding its public key: X9.62's
uncompressed encoding of `d` times the generator. -/
def p256Key (d : Nat) (key : high.agreement.PrivateKey) : Prop :=
  ∃ k : high.agreement.Keyed high.curve.P256 mid.p256.PrivateKey, key.«private» = .P256 k ∧
    wordsNat k.key.scalar.val = d ∧
    high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref key.«public» ⦃ b =>
      p256PublicKey d b.val ⦄

/-- P-256 key generation's outcome, for the system source's successive
draws: a `p256Key` whose scalar is the first of `n` draws, from the `i`th,
whose bytes, read big-endian, are in [1, n), unless a draw fails first;
refused if none is. -/
def p256Keygen (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8) (i : Nat) :
    Nat → core.result.Result high.agreement.PrivateKey error.Error → Prop
  | 0, key => key = .Err .RngFailed
  | n + 1, key =>
    match draws i with
    | (.Err _, _) => key = .Err .RngFailed
    | (.Ok _, out) =>
      if 0 < beNat out.val ∧ beNat out.val < n256 then
        ∃ key', key = .Ok key' ∧ p256Key (beNat out.val) key'
      else p256Keygen draws (i + 1) n key

namespace P256

/-! ## Key generation -/

@[step]
theorem private_eq_spec (a b : mid.p256.Scalar) :
    mid.p256.Scalar.private_eq a b ⦃ r => r = decide (wordsNat a.val = wordsNat b.val) ⦄ := by
  unfold mid.p256.Scalar.private_eq
  step*

@[step]
theorem reduce_mod_n_spec (a : mid.p256.Scalar) :
    mid.p256.Scalar.reduce_mod_n a ⦃ r => wordsNat r.val = wordsNat a.val % n256 ⦄ := by
  unfold mid.p256.Scalar.reduce_mod_n mid.p256.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

theorem into_range_check_spec (sc : mid.p256.Scalar) :
    mid.p256.Scalar.into_range_check sc ⦃ r =>
      if 0 < wordsNat sc.val ∧ wordsNat sc.val < n256 then r = .Ok sc
      else r = .Err (.KeyRejected .ScalarOutOfRange) ⦄ := by
  unfold mid.p256.Scalar.into_range_check mid.p256.Scalar.is_zero
    mid.p256.Scalar.Insts.CoreDefaultDefault.default core.default.DefaultArray.default low.ct.into_public
  simp only [core.convert.IntoFrom.into, error.Error.Insts.CoreConvertFromKeyFormatError.from]
  step as ⟨red, hred⟩
  step as ⟨b, hb⟩
  step as ⟨b1, hb1⟩
  have hn : 0 < n256 := by simp [n256]
  have hbv : b = decide (wordsNat sc.val < n256) := by
    rw [hb, hred]; exact decide_eq_decide.mpr (Nat.mod_eq_iff_lt (by omega))
  have hb1v : b1 = decide (wordsNat sc.val = 0) := by
    rw [hb1]; congr 2
  subst hbv hb1v
  by_cases hr : 0 < wordsNat sc.val ∧ wordsNat sc.val < n256
  · have h0 : wordsNat sc.val ≠ 0 := by omega
    simp [hr, h0]
  · simp only [hr, ↓reduceIte]
    by_cases h0 : wordsNat sc.val = 0
    · simp [h0]
    · have : ¬ wordsNat sc.val < n256 := fun h => hr ⟨by omega, h⟩
      simp [this, h0]

theorem from_bytes_checked_spec (bytes : Slice U8) (hl : bytes.length = 32) :
    mid.p256.Scalar.from_bytes_checked bytes ⦃ r =>
      if 0 < beNat bytes.val ∧ beNat bytes.val < n256 then
        ∃ sc, r = .Ok sc ∧ wordsNat sc.val = beNat bytes.val
      else r = .Err (.KeyRejected .ScalarOutOfRange) ⦄ := by
  unfold mid.p256.Scalar.from_bytes_checked
  apply WP.spec_bind (be_any_size_32_spec bytes hl)
  rintro o ⟨w, rfl, hw⟩
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply WP.spec_mono (into_range_check_spec w)
  intro r hr
  rw [hw] at hr
  split_ifs at hr ⊢
  · exact ⟨w, hr, hw⟩
  · exact hr

theorem from_bytes_spec (bytes : Slice U8) (hl : bytes.length = 32) :
    mid.p256.PrivateKey.from_bytes bytes ⦃ r =>
      if 0 < beNat bytes.val ∧ beNat bytes.val < n256 then
        ∃ k, r = .Ok k ∧ wordsNat k.scalar.val = beNat bytes.val
      else r = .Err (.KeyRejected .ScalarOutOfRange) ⦄ := by
  unfold mid.p256.PrivateKey.from_bytes
  step with from_bytes_checked_spec bytes hl as ⟨r, hr⟩
  split_ifs at hr ⊢
  · obtain ⟨sc, rfl, hsc⟩ := hr
    simp [core.result.Result.map,
      mid.p256.PrivateKey.from_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleScalarPrivateKey.call_once,
      low.ct.into_secret, hsc]
  · subst hr
    simp [core.result.Result.map]

theorem public_point_spec (h : Runs) (k : mid.p256.PrivateKey) (hk : wordsNat k.scalar.val < n256) (x y : Nat)
    (hq : p256Pow p256G (wordsNat k.scalar.val) = some (x, y)) (hc : p256OnCurve (some (x, y))) :
    mid.p256.PrivateKey.public_point k ⦃ pt =>
      pairNat pt.xy.val = (2 ^ 256 * x % p256, 2 ^ 256 * y % p256) ⦄ := by
  unfold mid.p256.PrivateKey.public_point low.ct.into_public
  step with base_multiply_spec h k.scalar hk as ⟨q, rx, ry, hz, hqq⟩
  unfold p256AffineZ at hz
  split_ifs at hz with h0
  · rw [hz] at hq; cases hq
  · rw [hz] at hq
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    step as ⟨b, hb⟩
    rw [hqq] at hb
    simp only [rinv_tomont_mod] at hb
    have hbt : b = true := hb.mpr hc
    subst hbt
    step
    rw [hqq, tomont_mod, tomont_mod]

/-- `PrivateKey::vg_public_key`: pyca/verified-garbage's public key of a
scalar below n, which rind checks is on the curve. -/
theorem vg_public_key_spec (h : Runs) (vg : low.x86_64.p256_vg.P256) (k : mid.p256.PrivateKey)
    (hk : wordsNat k.scalar.val < n256) (x y : Nat)
    (hq : p256Pow p256G (wordsNat k.scalar.val) = some (x, y)) (hc : p256OnCurve (some (x, y))) :
    mid.p256.PrivateKey.vg_public_key k vg ⦃ b =>
      b.val.head? = some 4#u8 ∧ x962Coords b.val = (x, y) ⦄ := by
  have hk0 : 0 < wordsNat k.scalar.val := by
    rcases Nat.eq_zero_or_pos (wordsNat k.scalar.val) with h0 | h0
    · rw [h0] at hq; simp [p256Pow, nist.pow] at hq
    · exact h0
  obtain ⟨x', y', hpk, hpow⟩ := vgP256.publicKey_eq _ hk0 hk
  rw [hq, Option.some.injEq, Prod.mk.injEq] at hpow
  obtain ⟨rfl, rfl⟩ := hpow
  unfold mid.p256.PrivateKey.vg_public_key mid.p256.Scalar.as_bytes low.ct.into_public
  step with u64x4_to_be_spec k.scalar as ⟨a, ha⟩
  step with vg_p256_public_key_spec vg a as ⟨o, ho⟩
  simp only [vgBytes, vgP256.ofBytes_bv, ha, hpk] at ho
  obtain ⟨out, rfl, hout⟩ := ho
  obtain ⟨h4, hx, hy⟩ := vgP256.encode_affine x' y' out.val hout
  have hxy : x962Coords out.val = (x'.val, y'.val) := by
    simp only [x962Coords, hx, hy]
  step as ⟨s, hs⟩
  step with from_x962_spec h s as ⟨r, hr⟩
  have hsl : s.length = 65 := by simp [hs]
  have hsv : s.val = out.val := by simp [hs]
  simp only [hsv, h4, ↓reduceIte, hsl, hxy, hc] at hr
  obtain ⟨pt, rfl, -⟩ := hr
  simp only [WP.spec_ok]
  exact ⟨h4, hxy⟩

theorem public_key_uncompressed_spec (h : Runs) (hvg : RunsP256) (k : mid.p256.PrivateKey) (hk : wordsNat k.scalar.val < n256)
    (x y : Nat) (hq : p256Pow p256G (wordsNat k.scalar.val) = some (x, y)) (hc : p256OnCurve (some (x, y))) :
    mid.p256.PrivateKey.public_key_uncompressed k ⦃ b =>
      b.val.head? = some 4#u8 ∧ x962Coords b.val = (x, y) ⦄ := by
  unfold mid.p256.PrivateKey.public_key_uncompressed
  step
  obtain ⟨-, t, ht⟩ := hvg
  simp only [ht, bind_ok]
  rcases t with _ | vg
  swap
  · exact vg_public_key_spec h vg k hk x y hq hc
  simp only
  step with public_point_spec h k hk x y hq hc as ⟨pt, hpt⟩
  have hp : 0 < p256 := by simp [p256]
  step with as_bytes_uncompressed_spec h pt (by rw [hpt]; exact Nat.mod_lt _ hp)
    (by rw [hpt]; exact Nat.mod_lt _ hp) as ⟨b, hb4, hbc⟩
  refine ⟨hb4, ?_⟩
  rw [hbc, hpt]
  simp only [rinv_tomont _ hc.1, rinv_tomont _ hc.2.1]

theorem encode_public_spec (h : Runs) (hvg : RunsP256) (k : mid.p256.PrivateKey) (algorithm : high.agreement.Algorithm)
    (hk : wordsNat k.scalar.val < n256) (x y : Nat) (hq : p256Pow p256G (wordsNat k.scalar.val) = some (x, y))
    (hc : p256OnCurve (some (x, y))) :
    high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.encode_public k algorithm ⦃ pk =>
      high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
        b.length = 65 ∧ b.val.head? = some 4#u8 ∧ x962Coords b.val = (x, y) ⦄ ⦄ := by
  unfold high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.encode_public high.agreement.PublicKey.from_encoding
    high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref low.generic.zeroise.ZeroableRef.new
  step with public_key_uncompressed_spec h hvg k hk x y hq hc as ⟨a, ha4, hac⟩
  step as ⟨sl, hsl⟩
  subst hsl
  have hlen : a.to_slice.len.val = 65 := by simp
  step as ⟨s, back, hs, hsl, hback⟩
  step as ⟨x', hx⟩
  step as ⟨b, hb, hbl⟩
  have ha65 : (a.val).length = 65 := a.property
  have hz : (Array.repeat 133#usize 0#u8).val.length = 133 := (Array.repeat 133#usize 0#u8).property
  have hbv : b.val = a.val := by
    have := take_setSlice! (Array.repeat 133#usize 0#u8).val a.val 0 (by omega)
    rw [hb, Array.val_to_slice, hback, hx, Array.val_to_slice, hlen, List.slice]
    simp only [ha65, Nat.zero_add, List.take_zero, List.nil_append] at this
    simp only [List.drop_zero, Nat.sub_zero, this]
  refine ⟨by rw [hbl, hlen], ?_, ?_⟩
  · rw [hbv]; exact ha4
  · rw [hbv]; exact hac

/-- An encoded public key, as `encode_public_spec` states it, is `p256PublicKey`'s. -/
theorem public_key_of_coords (d x y : Nat) (hq : p256Pow p256G d = some (x, y))
    (pk : high.agreement.PublicKey)
    (hpk : high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
      b.length = 65 ∧ b.val.head? = some 4#u8 ∧ x962Coords b.val = (x, y) ⦄) :
    high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
      p256PublicKey d b.val ⦄ :=
  WP.spec_mono hpk fun b ⟨hl, h4, hxy⟩ => ⟨hl, h4, by rw [hq, hxy]⟩

/-- The public key `encode_public` computes for a scalar in [1, n). -/
theorem encode_public_key_spec (h : Runs) (hvg : RunsP256) (k : mid.p256.PrivateKey) (algorithm : high.agreement.Algorithm)
    (hk0 : 0 < wordsNat k.scalar.val) (hk : wordsNat k.scalar.val < n256) :
    high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.encode_public k algorithm ⦃ pk =>
      high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
        p256PublicKey (wordsNat k.scalar.val) b.val ⦄ ⦄ := by
  obtain ⟨x, y, hq, hc⟩ := g_mult _ hk0 hk
  exact WP.spec_mono (encode_public_spec h hvg k algorithm hk x y hq hc)
    fun pk hpk => public_key_of_coords _ x y hq pk hpk

/-- `p256Agree`'s fields, which the theorems below rewrite to, so `step` finds
their specs. -/
theorem p256Agree_random : high.agreement.p256Agree.random = mid.p256.PrivateKey.generate := rfl

theorem p256Agree_load :
    high.agreement.p256Agree.load = high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.load := rfl

theorem p256Agree_encode_public :
    high.agreement.p256Agree.encode_public =
      high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.encode_public := rfl

/-- A key and its public key, as `Keyed::private_key` keeps them, is a `p256Key`. -/
theorem private_key_spec (k : mid.p256.PrivateKey) (pk : high.agreement.PublicKey)
    (hpk : high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
      p256PublicKey (wordsNat k.scalar.val) b.val ⦄) :
    high.agreement.Keyed.private_key high.agreement.p256Agree k pk ⦃ key =>
      p256Key (wordsNat k.scalar.val) key ⦄ := by
  simp only [high.agreement.Keyed.private_key, high.agreement.p256Agree,
    high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.wrap, bind_ok, WP.spec_ok]
  exact ⟨{ key := k, ops := () }, rfl, rfl, hpk⟩

/-- `p256Keygen`, for the scalar `generate_loop` returns. -/
def drawKeygen (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8) (i : Nat) :
    Nat → core.result.Result mid.p256.PrivateKey error.Error → Prop
  | 0, key => key = .Err .RngFailed
  | n + 1, key =>
    match draws i with
    | (.Err _, _) => key = .Err .RngFailed
    | (.Ok _, out) =>
      if 0 < beNat out.val ∧ beNat out.val < n256 then
        ∃ k, key = .Ok k ∧ wordsNat k.scalar.val = beNat out.val
      else drawKeygen draws (i + 1) n key

theorem generate_loop_spec (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8)
    (hdraw : ∀ i, mid.p256.PrivateKey.draw i (Array.repeat 32#usize 0#u8).to_slice = ok (draws i))
    (hlen : ∀ i, (draws i).2.length = 32) (n i : Nat) :
    mid.p256.PrivateKey.generate_loop i n ⦃ key => drawKeygen draws i n key ⦄ := by
  induction n generalizing i with
  | zero => simp [mid.p256.PrivateKey.generate_loop, drawKeygen]
  | succ n ih =>
    unfold mid.p256.PrivateKey.generate_loop
    simp only [Array.to_slice_mut, lift, bind_ok]
    have hf : mid.p256.PrivateKey.draw i (Array.repeat 32#usize 0#u8).to_slice ⦃ p => p = draws i ⦄ := by
      rw [hdraw]; simp [WP.spec_ok]
    step with hf as ⟨r, out, hd⟩
    simp only [drawKeygen, ← hd]
    have hout : out.length = 32 := by simpa [← hd] using hlen i
    have hfrom : ((Array.repeat 32#usize 0#u8).from_slice out).to_slice.val = out.val := by
      simp [Array.from_slice, hout]
    have hl : ((Array.repeat 32#usize 0#u8).from_slice out).to_slice.length = 32 := by
      simp only [Slice.length, hfrom]; simpa [Slice.length] using hout
    rcases r with _ | e
    · simp only
      step with from_bytes_spec _ hl as ⟨p, hp⟩
      rw [hfrom] at hp
      split_ifs at hp ⊢ with hr
      · obtain ⟨k, rfl, hk⟩ := hp
        simp [hk]
      · subst hp
        exact ih (i + 1)
    · simp

/-- A scalar `generate_loop` returns is in [1, n), and is `p256Keygen`'s with
any public key a `p256Key` holds for it. -/
theorem drawKeygen_ok (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8)
    (n i : Nat) (k : mid.p256.PrivateKey) (hr : drawKeygen draws i n (.Ok k)) :
    0 < wordsNat k.scalar.val ∧ wordsNat k.scalar.val < n256 ∧
      ∀ key, p256Key (wordsNat k.scalar.val) key → p256Keygen draws i n (.Ok key) := by
  induction n generalizing i with
  | zero => simp [drawKeygen] at hr
  | succ n ih =>
    simp only [drawKeygen] at hr
    simp only [p256Keygen]
    rcases hd : draws i with ⟨res, out⟩
    simp only [hd] at hr ⊢
    rcases res with _ | _
    · simp only at hr ⊢
      split_ifs at hr ⊢ with hrange
      · obtain ⟨k', hk', hk⟩ := hr
        cases hk'
        rw [hk]
        exact ⟨hrange.1, hrange.2, fun key hkey => ⟨key, rfl, hkey⟩⟩
      · exact ih (i + 1) hr
    · simp at hr

/-- A failure `generate_loop` returns is `p256Keygen`'s. -/
theorem drawKeygen_err (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8)
    (n i : Nat) (e : error.Error) (hr : drawKeygen draws i n (.Err e)) :
    p256Keygen draws i n (.Err e) := by
  induction n generalizing i with
  | zero => simpa [drawKeygen, p256Keygen] using hr
  | succ n ih =>
    simp only [drawKeygen] at hr
    simp only [p256Keygen]
    rcases hd : draws i with ⟨res, out⟩
    simp only [hd] at hr ⊢
    rcases res with _ | _
    · simp only at hr ⊢
      split_ifs at hr ⊢
      · obtain ⟨k, hk, -⟩ := hr
        cases hk
      · exact ih (i + 1) hr
    · simpa using hr

theorem load_scalar_spec (h : Runs) (hvg : RunsP256) (algorithm : high.agreement.Algorithm) (b : Slice U8) :
    high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.load algorithm (.Scalar b) ⦃ r =>
      if b.length = 32 then
        if 0 < beNat b.val ∧ beNat b.val < n256 then
          ∃ k pk, r = .Ok (k, pk) ∧ wordsNat k.scalar.val = beNat b.val ∧
            high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b' =>
              p256PublicKey (beNat b.val) b'.val ⦄
        else r = .Err (.KeyRejected .ScalarOutOfRange)
      else r = .Err (.KeyRejected .WrongLength) ⦄ := by
  unfold high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.load
  step as ⟨_⟩
  by_cases hl : b.length = 32
  · have hlen : Slice.len b = mid.p256.Scalar.BYTES := by
      apply UScalar.eq_of_val_eq
      simpa [Slice.len, Slice.length, mid.p256.Scalar.BYTES] using hl
    simp only [hlen, ↓reduceIte, hl]
    step with from_bytes_spec b hl as ⟨r, hr⟩
    split_ifs at hr ⊢ with hrange
    · obtain ⟨k, rfl, hk⟩ := hr
      step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec as ⟨cf, hcf⟩
      subst hcf
      simp only
      step with encode_public_key_spec h hvg k algorithm (hk ▸ hrange.1) (hk ▸ hrange.2) as ⟨pk, hpk⟩
      exact ⟨k, pk, rfl, hk, hk ▸ hpk⟩
    · subst hr
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · have hlen : ¬ Slice.len b = mid.p256.Scalar.BYTES := by
      intro h'
      exact hl (by simpa [Slice.len, Slice.length, mid.p256.Scalar.BYTES] using congrArg UScalar.val h')
    simp [hlen, hl, error.Error.Insts.CoreConvertFromKeyFormatError.from]

end P256

open P256

/-! ## The agreement API, `high::agreement`, through the modelled dispatch -/

/-- A generated P-256 key's scalar is the first of up to 64 draws from the
system source whose bytes, read big-endian, are in [1, n), and key generation
is refused if a draw fails before one is, or none is. The draws themselves are
outside the functional spec. -/
theorem p256_generate (h : Runs) (hvg : RunsP256) (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8)
    (hdraw : ∀ i, mid.p256.PrivateKey.draw i (Array.repeat 32#usize 0#u8).to_slice = ok (draws i))
    (hlen : ∀ i, (draws i).2.length = 32) :
    high.agreement.PrivateKey.generate high.agreement.ECDH_P256 ⦃ key => p256Keygen draws 0 64 key ⦄ := by
  unfold high.agreement.PrivateKey.generate high.agreement.ECDH_P256 high.agreement.Algorithm.generate
    high.agreement.Keyed.generate
  simp only [p256Agree_random]
  unfold mid.p256.PrivateKey.generate
  step as ⟨_⟩
  step with generate_loop_spec draws hdraw hlen 64 0 as ⟨r, hr⟩
  rcases r with k | e
  · obtain ⟨hk0, hk, hkey⟩ := drawKeygen_ok draws 64 0 k hr
    simp only [p256Agree_encode_public]
    step with encode_public_key_spec h hvg k _ hk0 hk as ⟨pk, hpk⟩
    step with private_key_spec k pk hpk as ⟨key, hkey'⟩
    exact hkey key hkey'
  · simp only [WP.spec_ok]
    exact drawKeygen_err draws 64 0 e hr

/-- A P-256 key loaded from its scalar is refused unless it is 32 bytes and,
read big-endian, in [1, n), and otherwise is that scalar, as
`p256_generate`'s is a draw's. -/
theorem p256_from_scalar (h : Runs) (hvg : RunsP256) (b : Slice U8) :
    high.agreement.PrivateKey.from_scalar high.agreement.ECDH_P256 b ⦃ key =>
      if b.length = 32 then
        if 0 < beNat b.val ∧ beNat b.val < n256 then
          ∃ key', key = .Ok key' ∧ p256Key (beNat b.val) key'
        else key = core.result.Result.Err (.KeyRejected .ScalarOutOfRange)
      else key = core.result.Result.Err (.KeyRejected .WrongLength) ⦄ := by
  unfold high.agreement.PrivateKey.from_scalar high.agreement.ECDH_P256 high.agreement.Algorithm.load
    high.agreement.Keyed.load
  simp only [p256Agree_load]
  step with load_scalar_spec h hvg _ b as ⟨r, hr⟩
  split_ifs at hr ⊢
  · obtain ⟨k, pk, rfl, hk, hpk⟩ := hr
    simp only
    step with private_key_spec k pk (hk ▸ hpk) as ⟨key', hkey'⟩
    exact ⟨key', rfl, hk ▸ hkey'⟩
  · subst hr
    simp
  · subst hr
    simp

/-- A P-256 key's public key: X9.62's uncompressed encoding of its scalar
times the generator, which `p256_generate` and `p256_from_scalar` show every
key holds. -/
theorem p256_public_key (key : high.agreement.PrivateKey) (d : Nat) (hkey : p256Key d key) :
    (do
      let pk ← high.agreement.PrivateKey.public_key key
      high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk) ⦃ b =>
      p256PublicKey d b.val ⦄ := by
  obtain ⟨_, _, _, hpk⟩ := hkey
  simpa [high.agreement.PrivateKey.public_key] using hpk

end rind.x86_64
