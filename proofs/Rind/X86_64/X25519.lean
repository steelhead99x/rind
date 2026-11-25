import Rind.X86_64.S2nBignum
import Rind.X86_64.Dispatch
import Rind.Bytes
open Aeneas Aeneas.Std Result rind.spec

/-!
# X25519, proven from rind's agreement API to its routines' contracts

The `x25519_*` theorems state what the agreement API returns for X25519,
through the dispatch `Rind.X86_64.Dispatch` models, in terms of `cpuX25519 o`,
RFC 7748's X25519 as the routines the CPU runs state it, for the result `o`
of the IFMA check, `CurveIfma o`: HOL Light's `rfcx25519` for s2n-bignum's,
and on x86_64 CPUs with AVX-512 IFMA, VG's spec, `vgX25519`, for
pyca/verified-garbage's. `admin/prove` writes the aarch64 proof from this
file by renaming the target.
-/

namespace rind.x86_64

variable {o : Option low.x86_64.curve25519_ifma.Curve25519Ifma}

/-! ## Byte and limb conversions, `mid::util` -/

theorem le_to_u64x4_loop_spec
    (z : core.iter.adapters.zip.Zip (core.ops.range.Range Std.Usize) (core.slice.iter.ChunksExact Std.U8))
    (r : Std.Array Std.U64 4#usize) (F : List Nat)
    (hs : z.fst.start.val ≤ 4) (he : z.fst.end.val = 4)
    (hc : z.snd.chunks.length = 4 - z.fst.start.val)
    (h8 : ∀ c ∈ z.snd.chunks, c.length = 8)
    (hF : (r.val.take z.fst.start.val).map (·.val) ++ z.snd.chunks.map (leNat ·.val) = F) :
    mid.util.little_endian_to_u64x4_loop z r ⦃ r' => r'.val.map (·.val) = F ⦄ := by
  unfold mid.util.little_endian_to_u64x4_loop
  apply loop.spec_decr_nat (fun x => 4 - x.1.fst.start.val)
    (fun x => x.1.fst.start.val ≤ 4 ∧ x.1.fst.end.val = 4 ∧
      x.1.snd.chunks.length = 4 - x.1.fst.start.val ∧ (∀ c ∈ x.1.snd.chunks, c.length = 8) ∧
      (x.2.val.take x.1.fst.start.val).map (·.val) ++ x.1.snd.chunks.map (leNat ·.val) = F)
  · rintro ⟨⟨rg, ce⟩, r⟩ ⟨hs, he, hc, h8, hF⟩
    simp only at hs he hc h8 hF ⊢
    unfold mid.util.little_endian_to_u64x4_loop.body
    unfold core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    step*
    obtain ⟨o, rg'⟩ := x
    simp only at x_post x_post1
    split_ifs at x_post with hlt
    · obtain ⟨rfl, hst⟩ := x_post
      rcases hch : ce.chunks with _ | ⟨c, rest⟩
      · simp [hch] at hc; omega
      simp only [core.slice.iter.IteratorChunksExact.next, hch]
      have hc8 : c.length = 8 := h8 c (by simp [hch])
      step*
      · rcases r1 with a | _
        · exact ⟨a, rfl⟩
        · exact absurd hc8 r1_post
      · subst r1_post
        obtain ⟨hac, -⟩ := r1_post
        have hi : i.val = leNat c.val := by rw [val_of_fromLEBytes _ i i_post, hac]
        have hlen : (r.val).length = 4 := r.property
        refine ⟨by omega, by simp [x_post1, he], by simp [hch] at hc; omega,
          fun c' hc' => h8 c' (by simp [hch, hc']), ?_, by omega⟩
        rw [hst, a1_post, Std.Array.set_val_eq, List.take_add_one, List.getElem?_set_self (by omega),
          List.take_set_of_le (by omega)]
        rw [hch] at hF
        simp only [List.map_append, List.map_cons, Option.toList_some, List.map_nil, hi] at hF ⊢
        simpa using hF
    · obtain ⟨rfl, hst⟩ := x_post
      have hst4 : rg.start.val = 4 := by omega
      have hnil : ce.chunks = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hlen : (r.val).length = 4 := r.property
      rw [hnil, hst4, List.take_of_length_le (by omega)] at hF
      simpa [WP.spec_ok] using hF
  · exact ⟨hs, he, hc, h8, hF⟩

@[step]
theorem le_to_u64x4_spec (b : Std.Array U8 32#usize) :
    mid.util.little_endian_to_u64x4 b ⦃ w => wordsNat w.val = leNat b.val ⦄ := by
  unfold mid.util.little_endian_to_u64x4
  simp only [core.slice.Slice.chunks_exact, show (8#usize).val > 0 by decide, ↓reduceDIte]
  step*
  simp only [core.iter.traits.collect.IntoIterator.Blanket.into_iter, ok.injEq] at iter_post
  subst s_post iter_post
  have hflat := toChunksExact_flatten 8 (by decide) b.val
  have hlen8 := toChunksExact_length 8 (by decide) b.val
  have hrem := toChunksExact_remainder 8 (by decide) b.val
  set C := (List.toChunksExact 8 (by decide) b.val).1
  have hb : b.val.length = 32 := b.property
  have hfl := length_flatten_of_length C 8 hlen8
  have hC : C.length = 4 := by
    have := congrArg List.length hflat
    simp only [List.length_append, hfl, hb] at this
    omega
  have hR : (List.toChunksExact 8 (by decide) b.val).2 = [] := by
    have := congrArg List.length hflat
    simp only [List.length_append, hfl, hb, hC] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  rw [hR, List.append_nil] at hflat
  apply WP.spec_mono (le_to_u64x4_loop_spec iter _ (C.map leNat) ?_ ?_ ?_ ?_ ?_)
  · intro w hw
    rw [wordsNat, hw, ← leNat_flatten C hlen8, hflat]
  · simp [iter_post1]
  · simp [iter_post1]
  · simpa [iter_post1, other'_post, C] using hC
  · simp only [other'_post, List.mem_map, List.mem_attach, true_and, Subtype.exists]
    rintro _ ⟨c, hc, rfl⟩
    simpa [C] using hlen8 c (by simpa [C] using hc)
  · simp [iter_post1, other'_post, C]

/-- The bytes `u64::to_le_bytes` writes. -/
def leBytes (w : U64) : List U8 := w.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8)

theorem u64x4_to_le_loop_spec
    (it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Std.U64))
    (r : Std.Array U8 32#usize) (V : List U64) (hVl : V.length = 4)
    (hV : it.iter.slice.val = V) (hi : it.iter.i = it.count.val) (hk : it.count.val ≤ 4)
    (hr : r.val.take (8 * it.count.val) = (V.take it.count.val).flatMap leBytes) :
    mid.util.u64x4_to_little_endian_loop it r ⦃ r' => r'.val = V.flatMap leBytes ⦄ := by
  unfold mid.util.u64x4_to_little_endian_loop
  apply loop.spec_decr_nat (fun x => 4 - x.1.count.val)
    (fun x => x.1.iter.slice.val = V ∧ x.1.iter.i = x.1.count.val ∧ x.1.count.val ≤ 4 ∧
      x.2.val.take (8 * x.1.count.val) = (V.take x.1.count.val).flatMap leBytes)
  · rintro ⟨it, r⟩ ⟨hV, hi, hk, hr⟩
    simp only at hV hi hk hr ⊢
    unfold mid.util.u64x4_to_little_endian_loop.body
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorSliceIter.next]
    have hsl : it.iter.slice.len.val = 4 := by simp [Slice.len, hV, hVl]
    split
    · rename_i hlt
      have hk4 : it.count.val < 4 := by omega
      step*
      · rw [s_post1, s1_post]
        simp [i3_post, i2_post, i1_post, Slice.length]
        omega
      · have ha8 : (a.val).length = 8 := a.property
        have hw : it.iter.slice[it.iter.i] = V[it.count.val] := by
          subst hV
          show it.iter.slice.val[it.iter.i]'(by simp [Slice.len] at hlt; omega) = _
          simp only [hi]
        refine ⟨hV, by omega, by omega, ?_, by omega⟩
        rw [s_post2, s2_post, s1_post]
        have hr32 : (r.val).length = 32 := r.property
        have := take_setSlice! r.val a.val (i1.val) (by rw [ha8, i1_post]; omega)
        simp only [Array.val_to_slice, ha8] at this ⊢
        rw [show 8 * x.val = i1.val + 8 by rw [x_post, i1_post]; ring, this, i1_post,
          show it.count.val * 8 = 8 * it.count.val by ring, hr, x_post, List.take_add_one,
          List.flatMap_append, List.getElem?_eq_getElem (by omega)]
        simp [a_post, hw, leBytes]
    · rename_i hlt
      have hk4 : it.count.val = 4 := by omega
      have hr32 : (r.val).length = 32 := r.property
      rw [hk4, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hr
      simpa [WP.spec_ok] using hr
  · exact ⟨hV, hi, hk, hr⟩

@[step]
theorem u64x4_to_le_spec (v : Std.Array U64 4#usize) :
    mid.util.u64x4_to_little_endian v ⦃ b => leNat b.val = wordsNat v.val ⦄ := by
  unfold mid.util.u64x4_to_little_endian
  simp only [core.slice.Slice.iter]
  step*
  have hv : (v.val).length = 4 := v.property
  apply WP.spec_mono (u64x4_to_le_loop_spec iter _ v.val hv ?_ ?_ ?_ ?_)
  · intro b hb
    have h8 : ∀ c ∈ v.val.map leBytes, c.length = 8 := by
      simp [leBytes]
    rw [hb, List.flatMap_def, leNat_flatten _ h8, wordsNat, List.map_map]
    congr 1
    apply List.map_congr_left
    intro w _
    exact leNat_toLEBytes w
  all_goals simp [iter_post, iter_post1, s_post, Array.val_to_slice]

@[step]
theorem le_slice_to_u64x4_spec (s : Slice U8) :
    mid.util.little_endian_slice_to_u64x4 s ⦃ o =>
      if s.length = 32 then ∃ w, o = some w ∧ wordsNat w.val = leNat s.val else o = none ⦄ := by
  unfold mid.util.little_endian_slice_to_u64x4
  step*
  rcases r with a | _
  · obtain ⟨ha, hl⟩ := r_post
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    step*
  · simp [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual, r_post]

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
