import Rind.X86_64.ChaCha20
import Rind.X86_64.AesGcmAead
import Rind.X86_64.CtEqual
open Aeneas Aeneas.Std Result rind.spec

/-!
# ChaCha20-Poly1305 and XChaCha20-Poly1305, from the AEAD API to aws-lc's routine

The `chacha20_poly1305_*` theorems state what the AEAD API's
`CHACHA20_POLY1305` keys return, and the `randomized_nonce_key_*` ones what
`RandomizedNonceKey`'s XChaCha20-Poly1305 does, against RFC 8439 and
draft-irtf-cfrg-xchacha-03 as `Rind.Spec` transliterates them, through the
dispatch `Rind.X86_64.AeadDispatch` models. HChaCha20 runs HACL*'s rounds,
which are Rust, so it is proven here too.

Below rind's Rust, they take `OnePass` as a hypothesis: that aws-lc's one-pass
routines, which `one_pass` calls, compute RFC 8439's ciphertext and tag. No
proof covers those routines yet, so no theorem here earns the ✓.
-/

namespace rind.x86_64

/-- aws-lc's one-pass routines, behind `one_pass`, compute RFC 8439's AEAD for
a message of at most 2^38 - 64 bytes, as many as its 32-bit block counter
covers from block 1: sealing leaves the ChaCha20 ciphertext in place and
returns the Poly1305 tag over the AAD and it, and opening leaves the
plaintext and returns the tag over the AAD and the ciphertext it was given.
Either half, AVX2 or SSE4.1, computes the same. -/
def OnePass : Prop :=
  ∀ sse41 avx2 (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8),
    inout.length ≤ 2 ^ 38 - 64 →
    low.x86_64.chacha20poly1305.one_pass sse41 avx2 key nonce aad inout true ⦃ r =>
      r.2.length = inout.length ∧
      (bvs r.2.val, bvs r.1.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ ∧
    low.x86_64.chacha20poly1305.one_pass sse41 avx2 key nonce aad inout false ⦃ r =>
      r.2.length = inout.length ∧
      bvs r.2.val = chacha20.encrypt (bvs key.val) 1 (bvs nonce.val) (bvs inout.val) ∧
      bvs r.1.val = poly1305.mac (chacha20poly1305.otk (bvs key.val) (bvs nonce.val))
        (chacha20poly1305.macData (bvs aad.val) (bvs inout.val)) ⦄

/-- rind runs aws-lc's one-pass routines on this CPU, and they compute RFC
8439's AEAD: its entry guard passes and holds, and its CPU-feature checks find
SSE4.1. None reads an input. -/
def RunsChaCha20Poly1305 : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
  (∃ s, low.x86_64.cpu.HaveSse41.check = ok (some s)) ∧ (∃ a, low.x86_64.cpu.HaveAvx2.check = ok a) ∧
  OnePass

theorem bvs_inj (x y : List U8) : bvs x = bvs y ↔ x = y := by
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun a b hab => by cases a; cases b; simp_all) h
  · intro h; rw [h]

theorem bvs_length (x : List U8) : (bvs x).length = x.length := by simp [bvs]

/-! ## The one-pass seal and open, `low::x86_64::chacha20poly1305` -/

theorem chacha20_poly1305_seal_spec (h : RunsChaCha20Poly1305) (key : Std.Array U8 32#usize)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (hl : inout.length ≤ 2 ^ 38 - 64) :
    low.x86_64.chacha20poly1305.seal key nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧
      (bvs r.2.val, bvs r.1.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ := by
  obtain ⟨-, -, ⟨s, hs⟩, ⟨a, ha⟩, hop⟩ := h
  unfold low.x86_64.chacha20poly1305.seal
  simp only [hs, ha, bind_ok]
  exact (hop s a key nonce aad inout hl).1

theorem chacha20_poly1305_open_spec (h : RunsChaCha20Poly1305) (key : Std.Array U8 32#usize)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (hl : inout.length ≤ 2 ^ 38 - 64) :
    low.x86_64.chacha20poly1305.open key nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧
      bvs r.2.val = chacha20.encrypt (bvs key.val) 1 (bvs nonce.val) (bvs inout.val) ∧
      bvs r.1.val = poly1305.mac (chacha20poly1305.otk (bvs key.val) (bvs nonce.val))
        (chacha20poly1305.macData (bvs aad.val) (bvs inout.val)) ⦄ := by
  obtain ⟨-, -, ⟨s, hs⟩, ⟨a, ha⟩, hop⟩ := h
  unfold low.x86_64.chacha20poly1305.open
  simp only [hs, ha, bind_ok]
  exact (hop s a key nonce aad inout hl).2

/-! ## The length check, `mid::chacha20` -/

/-- From block 1, the 32-bit block counter covers 2^38 - 64 bytes. -/
theorem chacha20_check_counter_spec (len : Usize) :
    mid.chacha20.check_counter 1#u32 len ⦃ r =>
      r = if len.val ≤ 2 ^ 38 - 64 then .Ok () else .Err .WrongLength ⦄ := by
  unfold mid.chacha20.check_counter core.num.Usize.div_ceil
  simp only [lift, bind_ok, show ¬ (64#usize : Usize).val = 0 by decide, ↓reduceDIte]
  have h1 : (core.convert.num.FromU64U32.from 1#u32 : U64).val = 1 := rfl
  have hb : len.val < 2 ^ 64 := by
    have := len.hmax
    rcases System.Platform.numBits_eq with h | h
    · simp_all [UScalarTy.Usize_numBits_eq]; omega
    · simp_all [UScalarTy.Usize_numBits_eq]
  have hm : (len.val + 64 - 1) / 64 % 2 ^ UScalarTy.U64.numBits = (len.val + 63) / 64 := by
    rw [UScalarTy.U64_numBits_eq]; apply Nat.mod_eq_of_lt; omega
  step*
  all_goals simp only [h1, UScalar.cast_val_eq, UScalar.ofNatCore_val_eq] at *
  all_goals simp only [hm] at *
  all_goals first
    | scalar_tac
    | (have h4 : i4.val = 2 ^ 32 := by rw [i4_post]; simp [Nat.shiftLeft_eq, U64.size, U64.numBits]
       first
        | (rw [ite_eq_right (by intro; scalar_tac)])
        | (rw [ite_eq_left (by scalar_tac)]))

/-! ## `mid::chacha20poly1305` and `mid::xchacha20poly1305`, above the routine -/

/-- The one-pass seal's result as the `Continue` branch of both keys'
`encrypt` returns it. -/
theorem seal_tail_spec (h : RunsChaCha20Poly1305) (key : Std.Array U8 32#usize)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (hl : inout.length ≤ 2 ^ 38 - 64) :
    (do
      let (tag_out1, cipher_inout1) ← low.x86_64.chacha20poly1305.seal key nonce aad inout
      low.ct.public_slice cipher_inout1
      let s ← lift (Std.Array.to_slice tag_out1)
      low.ct.public_slice s
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Error), cipher_inout1, tag_out1))
      ⦃ r => r.1 = .Ok () ∧ r.2.1.length = inout.length ∧
        (bvs r.2.1.val, bvs r.2.2.val) =
          chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ := by
  apply WP.spec_bind (chacha20_poly1305_seal_spec h key nonce aad inout hl)
  rintro ⟨tag, ct⟩ ⟨hlen, hseal⟩
  simp only [low.ct.public_slice, lift, bind_ok]
  exact (WP.spec_ok _).2 ⟨rfl, hlen, hseal⟩

/-- The one-pass open's result as the `Continue` branch of both keys'
`decrypt` returns it. -/
theorem open_tail_spec (h : RunsChaCha20Poly1305) (key : Std.Array U8 32#usize)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (hl : inout.length ≤ 2 ^ 38 - 64) :
    (do
      let (actual_tag, cipher_inout1) ← low.x86_64.chacha20poly1305.open key nonce aad inout
      let s ← lift (Std.Array.to_slice actual_tag)
      let s1 ← lift (Std.Array.to_slice tag)
      let b ← low.generic.ct_equal.ct_equal s s1
      let b1 ← low.ct.into_public b
      if b1
      then
        low.ct.public_slice cipher_inout1
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Error), cipher_inout1)
      else
        let cipher_inout2 ← core.slice.Slice.fill core.clone.CloneU8 cipher_inout1 0#u8
        ok (core.result.Result.Err error.Error.DecryptFailed, cipher_inout2))
      ⦃ r =>
        let out := chacha20poly1305.open (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
          (bvs tag.val)
        if out.2 then r.1 = .Ok () ∧ r.2.length = inout.length ∧ bvs r.2.val = out.1
        else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate inout.length 0#u8 ⦄ := by
  have hh := h.2.1
  apply WP.spec_bind (chacha20_poly1305_open_spec h key nonce aad inout hl)
  rintro ⟨actual, pt⟩ ⟨hlen, hpt, hmac⟩
  simp only [lift, bind_ok]
  apply WP.spec_bind (ct_equal_spec hh _ _)
  rintro _ rfl
  simp only [low.ct.into_public, bind_ok, Std.Array.to_slice]
  have heq : (actual.val = tag.val) = ((poly1305.mac (chacha20poly1305.otk (bvs key.val) (bvs nonce.val))
      (chacha20poly1305.macData (bvs aad.val) (bvs inout.val)) == bvs tag.val) = true) := by
    rw [← hmac, beq_iff_eq, bvs_inj]
  by_cases hv : actual.val = tag.val
  · have ht : (poly1305.mac (chacha20poly1305.otk (bvs key.val) (bvs nonce.val))
        (chacha20poly1305.macData (bvs aad.val) (bvs inout.val)) == bvs tag.val) = true := by
      rw [← heq]; exact hv
    simp only [hv, decide_true, ite_true, low.ct.public_slice, bind_ok, chacha20poly1305.open, ht]
    exact (WP.spec_ok _).2 ⟨rfl, hlen, hpt⟩
  · have ht : (poly1305.mac (chacha20poly1305.otk (bvs key.val) (bvs nonce.val))
        (chacha20poly1305.macData (bvs aad.val) (bvs inout.val)) == bvs tag.val) = false := by
      rw [Bool.eq_false_iff]; intro ht; exact hv (heq ▸ ht)
    simp only [Slice.from_val, hv, decide_false, Bool.false_eq_true, ite_false, chacha20poly1305.open, ht]
    have hc : core.clone.CloneU8.clone 0#u8 ⦃ fun v' => v' = 0#u8 ⦄ := (WP.spec_ok _).2 rfl
    apply WP.spec_bind (core.slice.Slice.fill.spec core.clone.CloneU8 pt 0#u8 hc)
    rintro s ⟨-, hs⟩
    refine (WP.spec_ok _).2 ?_
    refine ⟨rfl, ?_⟩
    rw [hs, ← hlen]

/-- `ChaCha20Poly1305::encrypt`: a message past 2^38 - 64 bytes is refused,
left as it is, and otherwise the ciphertext in place and the tag are RFC
8439's. -/
theorem chacha20_poly1305_encrypt_spec (h : RunsChaCha20Poly1305) (k : mid.chacha20poly1305.ChaCha20Poly1305)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize) :
    mid.chacha20poly1305.ChaCha20Poly1305.encrypt k nonce aad inout tag ⦃ r =>
      if inout.length ≤ 2 ^ 38 - 64 then
        r.1 = .Ok () ∧ r.2.1.length = inout.length ∧
        (bvs r.2.1.val, bvs r.2.2.val) =
          chacha20poly1305.seal (bvs k.key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
      else r.1 = .Err .WrongLength ∧ r.2.1 = inout ⦄ := by
  have he := h.1
  obtain ⟨e, he⟩ := he
  unfold mid.chacha20poly1305.ChaCha20Poly1305.encrypt
  rw [he, bind_ok]
  apply WP.spec_bind (chacha20_check_counter_spec _)
  rintro r rfl
  rw [Slice.len_val]
  by_cases hb : inout.length ≤ 2 ^ 38 - 64
  · simp only [Slice.length] at hb
    simp only [hb, ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    exact seal_tail_spec h k.key nonce aad inout hb
  · simp only [Slice.length] at hb
    simp only [hb, ite_false, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨rfl, rfl⟩

/-- `ChaCha20Poly1305::decrypt`: a message past 2^38 - 64 bytes is refused,
left as it is; otherwise the call succeeds exactly when RFC 8439's tag is
`tag`, leaving the plaintext in place, and fails, leaving zeros. -/
theorem chacha20_poly1305_decrypt_spec (h : RunsChaCha20Poly1305) (k : mid.chacha20poly1305.ChaCha20Poly1305)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize) :
    mid.chacha20poly1305.ChaCha20Poly1305.decrypt k nonce aad inout tag ⦃ r =>
      if inout.length ≤ 2 ^ 38 - 64 then
        let out := chacha20poly1305.open (bvs k.key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
          (bvs tag.val)
        if out.2 then r.1 = .Ok () ∧ r.2.length = inout.length ∧ bvs r.2.val = out.1
        else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate inout.length 0#u8
      else r.1 = .Err .WrongLength ∧ r.2 = inout ⦄ := by
  have he := h.1
  obtain ⟨e, he⟩ := he
  unfold mid.chacha20poly1305.ChaCha20Poly1305.decrypt
  rw [he, bind_ok]
  apply WP.spec_bind (chacha20_check_counter_spec _)
  rintro r rfl
  rw [Slice.len_val]
  by_cases hb : inout.length ≤ 2 ^ 38 - 64
  · simp only [Slice.length] at hb
    simp only [hb, ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    exact open_tail_spec h k.key nonce aad inout tag hb
  · simp only [Slice.length] at hb
    simp only [hb, ite_false, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨rfl, rfl⟩

/-! ## HChaCha20 over HACL*'s rounds, `low::generic::chacha20` -/

/-- HChaCha20's output words: 0 to 3, then 12 to 15. -/
def hwords (st : Std.Array U32 16#usize) : List (BitVec 32) :=
  (st.val.map (·.bv)).take 4 ++ (st.val.map (·.bv)).drop 12

theorem hwords_length (st : Std.Array U32 16#usize) : (hwords st).length = 8 := by
  simp [hwords]

/-- Output word `i` is state word `i` below 4, and `i + 8` from there. -/
theorem hword_spec (st : Std.Array U32 16#usize) (i : Usize) (hi : i.val < 8) :
    (if i < 4#usize then Std.Array.index_usize st i
     else do
       let i1 ← i + 8#usize
       Std.Array.index_usize st i1) ⦃ w => (hwords st)[i.val]? = some w.bv ⦄ := by
  have hl : st.val.length = 16 := by simp
  split
  · step*
    have h4 : i.val < 4 := by scalar_tac
    rw [hwords, List.getElem?_append_left (by simp [hl]; omega)]
    simp [*]
  · step*
    have h4 : 4 ≤ i.val := by scalar_tac
    rw [hwords, List.getElem?_append_right (by simp [hl]; omega)]
    simp only [List.length_take, List.length_map, hl, List.getElem?_drop, List.getElem?_map]
    rw [show 12 + (i.val - min 4 16) = i1.val by scalar_tac]
    simp only [w_post]
    rw [List.getElem?_eq_getElem (by rw [hl]; scalar_tac)]
    rfl

theorem hchacha20_loop_spec (st : Std.Array U32 16#usize)
    (iter : core.ops.range.Range Usize) (out : Std.Array U8 32#usize) (hs : iter.start.val ≤ 8)
    (he : iter.end.val = 8)
    (ho : (out.val.map (·.bv)).take (4 * iter.start.val) =
      ((hwords st).take iter.start.val).flatMap BitVec.toLEBytes) :
    low.generic.chacha20.hchacha20_loop iter st out ⦃ r =>
      r.val.map (·.bv) = (hwords st).flatMap BitVec.toLEBytes ⦄ := by
  unfold low.generic.chacha20.hchacha20_loop
  apply loop.spec_decr_nat (fun x => 8 - x.1.start.val)
    (fun x => x.1.start.val ≤ 8 ∧ x.1.end.val = 8 ∧
      (x.2.val.map (·.bv)).take (4 * x.1.start.val) =
        ((hwords st).take x.1.start.val).flatMap BitVec.toLEBytes)
  · rintro ⟨it, out⟩ ⟨hs, he, ho⟩
    simp only at hs he ho ⊢
    unfold low.generic.chacha20.hchacha20_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
      subst ho'
      simp only
      step with hword_spec st it.start (by agrind) as ⟨w, hw⟩
      step*
      case h => simp [s_post1, s1_post, i3_post, i2_post, i1_post]; agrind
      refine ⟨by agrind, by agrind, ?_, by agrind⟩
      have ha : a.val.map (·.bv) = w.bv.toLEBytes := by
        rw [a_post, List.map_map]
        exact List.map_id _
      have ha4 : (a.val.map (·.bv)).length = 4 := by simp
      rw [s_post2, s2_post, s1_post, Array.val_to_slice, List.map_setSlice!, hst,
        show 4 * (it.start.val + 1) = i1.val + (a.val.map (·.bv)).length by rw [ha4, i1_post]; ring,
        take_setSlice! _ _ _ (by simp [i1_post]; agrind), i1_post, ho, ha, List.take_add_one,
        List.flatMap_append]
      congr 1
      simp [hw]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      have h8 : it.start.val = 8 := by agrind
      rw [h8, List.take_of_length_le (by simp), List.take_of_length_le (by rw [hwords_length])] at ho
      simpa using ho
  · exact ⟨hs, he, ho⟩

/-- HChaCha20, draft-irtf-cfrg-xchacha-03 section 2.2. -/
@[step]
theorem hchacha20_spec (key : Std.Array U8 32#usize) (nonce : Std.Array U8 16#usize) :
    low.generic.chacha20.hchacha20 key nonce ⦃ out =>
      bvs out.val = chacha20.hchacha20 (bvs key.val) (bvs nonce.val) ⦄ := by
  unfold low.generic.chacha20.hchacha20
  step*
  apply WP.spec_mono (hchacha20_loop_spec _ _ _ (by simp) (by simp) (by simp))
  intro out hout
  have hst : (to_slice_mut_back s1).val = s1.val := by
    rw [to_slice_mut_back_post]; simp [Std.Array.from_slice, s1_post]
  rw [bvs, hout, hwords, hst, s1_post1, s_post, st_post]
  rfl

/-! ## XChaCha20-Poly1305, `mid::xchacha20poly1305` -/

/-- The subkey and nonce are draft-irtf-cfrg-xchacha-03's. -/
theorem subkey_spec (k : mid.xchacha20poly1305.XChaCha20Poly1305) (nonce : Std.Array U8 24#usize) :
    mid.xchacha20poly1305.XChaCha20Poly1305.subkey k nonce ⦃ r =>
      (bvs r.1.val, bvs r.2.val) = chacha20poly1305.xKeyNonce (bvs k.key.val) (bvs nonce.val) ⦄ := by
  unfold mid.xchacha20poly1305.XChaCha20Poly1305.subkey
  step*
  simp only [core.array.TryFromSharedArraySlice.try_from]
  rw [dite_eq_left (by scalar_tac)]
  simp only [bind_ok, core.result.Result.unwrap]
  step*
  have hs : s.val = nonce.val := by rw [s_post]; simp [Std.Array.to_slice]
  have ht : tail.val.length = 8 := by
    have : tail.length = 8 := by rw [head_post1]; simp [s_post]
    exact this
  refine Prod.ext ?_ ?_
  · rw [chacha20poly1305.xKeyNonce]
    dsimp only
    rw [a1_post, Std.Array.from_val, head_post2, hs]
    simp [bvs, List.map_take]
  · rw [chacha20poly1305.xKeyNonce]
    dsimp only
    rw [s1_post2, s2_post, head_post3, hs]
    rw [head_post3, hs] at ht
    simp [bvs, Std.Array.repeat, List.setSlice!, ht, List.map_drop]

/-- `XChaCha20Poly1305::encrypt`: a message past 2^38 - 64 bytes is refused,
left as it is, and otherwise the ciphertext in place and the tag are
draft-irtf-cfrg-xchacha-03's. -/
theorem xchacha20_poly1305_encrypt_spec (h : RunsChaCha20Poly1305)
    (k : mid.xchacha20poly1305.XChaCha20Poly1305) (nonce : Std.Array U8 24#usize) (aad inout : Slice U8)
    (tag : Std.Array U8 16#usize) :
    mid.xchacha20poly1305.XChaCha20Poly1305.encrypt k nonce aad inout tag ⦃ r =>
      if inout.length ≤ 2 ^ 38 - 64 then
        r.1 = .Ok () ∧ r.2.1.length = inout.length ∧
        (bvs r.2.1.val, bvs r.2.2.val) =
          chacha20poly1305.xseal (bvs k.key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
      else r.1 = .Err .WrongLength ∧ r.2.1 = inout ⦄ := by
  obtain ⟨e, he⟩ := h.1
  unfold mid.xchacha20poly1305.XChaCha20Poly1305.encrypt
  rw [he, bind_ok]
  apply WP.spec_bind (chacha20_check_counter_spec _)
  rintro r rfl
  rw [Slice.len_val]
  by_cases hb : inout.length ≤ 2 ^ 38 - 64
  · simp only [hb, ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_bind (subkey_spec k nonce)
    rintro ⟨sk, sn⟩ hsk
    rw [chacha20poly1305.xseal, ← hsk]
    exact seal_tail_spec h sk sn aad inout hb
  · simp only [hb, ite_false, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨rfl, rfl⟩

/-- `XChaCha20Poly1305::decrypt`: a message past 2^38 - 64 bytes is refused,
left as it is; otherwise the call succeeds exactly when
draft-irtf-cfrg-xchacha-03's tag is `tag`, leaving the plaintext in place, and
fails, leaving zeros. -/
theorem xchacha20_poly1305_decrypt_spec (h : RunsChaCha20Poly1305)
    (k : mid.xchacha20poly1305.XChaCha20Poly1305) (nonce : Std.Array U8 24#usize) (aad inout : Slice U8)
    (tag : Std.Array U8 16#usize) :
    mid.xchacha20poly1305.XChaCha20Poly1305.decrypt k nonce aad inout tag ⦃ r =>
      if inout.length ≤ 2 ^ 38 - 64 then
        let out := chacha20poly1305.xopen (bvs k.key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
          (bvs tag.val)
        if out.2 then r.1 = .Ok () ∧ r.2.length = inout.length ∧ bvs r.2.val = out.1
        else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate inout.length 0#u8
      else r.1 = .Err .WrongLength ∧ r.2 = inout ⦄ := by
  obtain ⟨e, he⟩ := h.1
  unfold mid.xchacha20poly1305.XChaCha20Poly1305.decrypt
  rw [he, bind_ok]
  apply WP.spec_bind (chacha20_check_counter_spec _)
  rintro r rfl
  rw [Slice.len_val]
  by_cases hb : inout.length ≤ 2 ^ 38 - 64
  · simp only [hb, ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_bind (subkey_spec k nonce)
    rintro ⟨sk, sn⟩ hsk
    rw [chacha20poly1305.xopen, ← hsk]
    exact open_tail_spec h sk sn aad inout tag hb
  · simp only [hb, ite_false, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨rfl, rfl⟩

/-! ## The AEAD API, through the modelled dispatch -/

/-- An AEAD key holding ChaCha20-Poly1305 for the key bytes `key`. -/
def ChaChaKeyHolds (key : List (BitVec 8)) (k : aead.Key) : Prop :=
  ∃ c : mid.chacha20poly1305.ChaCha20Poly1305, k = .ChaCha20Poly1305 c ∧ bvs c.key.val = key

/-- A ChaCha20-Poly1305 key is refused unless it is 32 bytes, and otherwise
holds them. -/
theorem chacha20_poly1305_new (key : Slice U8) :
    aead.Key.new aead.CHACHA20_POLY1305 key ⦃ r =>
      if key.length = 32 then ∃ k, r = .Ok k ∧ ChaChaKeyHolds (bvs key.val) k
      else r = .Err .WrongLength ⦄ := by
  have hlen : aead.CHACHA20_POLY1305.key_len.val = 32 := rfl
  unfold aead.Key.new
  by_cases hk : key.length = 32
  · have hne : ¬ key.len ≠ aead.CHACHA20_POLY1305.key_len := by
      intro hne; apply hne; scalar_tac
    rw [ite_eq_right hne]
    simp only [aead.CHACHA20_POLY1305, aead.Sealer.expand,
      mid.chacha20poly1305.ChaCha20Poly1305.Insts.RindAeadCipher.new,
      mid.chacha20poly1305.ChaCha20Poly1305.Insts.RindAeadCipher.inner,
      mid.chacha20poly1305.ChaCha20Poly1305.new, low.ct.secret_slice]
    step as ⟨x, hx⟩
    rcases x with a | e
    · obtain ⟨ha, -⟩ := hx
      simp only [core.result.Result.unwrap, bind_ok, lift]
      refine (WP.spec_ok _).2 ?_
      rw [ite_eq_left hk]
      exact ⟨_, rfl, _, rfl, by rw [ha]⟩
    · exact absurd hk hx
  · have hne : key.len ≠ aead.CHACHA20_POLY1305.key_len := by
      intro he; apply hk; rw [← hlen, ← he]; simp
    rw [ite_eq_left hne]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_right hk]

/-- Sealing: a message past 2^38 - 64 bytes is refused, left as it is, and
otherwise the ciphertext in place and the tag are RFC 8439's. -/
theorem chacha20_poly1305_seal (h : RunsChaCha20Poly1305) (key : List (BitVec 8)) (k : aead.Key)
    (hk : ChaChaKeyHolds key k) (nonce : aead.Nonce) (aad in_out : Slice U8) :
    k.seal_in_place_separate_tag nonce aad in_out ⦃ r =>
      if in_out.length ≤ 2 ^ 38 - 64 then
        ∃ tag, r.1 = .Ok tag ∧ r.2.length = in_out.length ∧
          (bvs r.2.val, bvs tag.bytes.val) =
            chacha20poly1305.seal key (bvs nonce.bytes.val) (bvs aad.val) (bvs in_out.val)
      else r.1 = .Err .WrongLength ∧ r.2 = in_out ⦄ := by
  obtain ⟨c, rfl, rfl⟩ := hk
  unfold aead.Key.seal_in_place_separate_tag aead.Sealer.seal
  simp only [mid.chacha20poly1305.ChaCha20Poly1305.Insts.RindAeadCipher.seal]
  apply WP.spec_bind (chacha20_poly1305_encrypt_spec h c nonce.bytes aad in_out _)
  rintro ⟨r, out, tag⟩ hr
  dsimp only at hr
  split at hr
  · obtain ⟨rfl, hlen, hout⟩ := hr
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_left (by assumption)]
    exact ⟨⟨tag⟩, rfl, hlen, hout⟩
  · obtain ⟨rfl, rfl⟩ := hr
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_right (by assumption)]
    exact ⟨rfl, rfl⟩

/-- Sealing through any buffer `InOut`: for the view its `as_mut` gives, the
call returns what its `extend` makes of the buffer holding the view's
ciphertext, handed the tag, both RFC 8439's, or refuses a view past
2^38 - 64 bytes, leaving it as it is. -/
theorem chacha20_poly1305_seal_append_tag (h : RunsChaCha20Poly1305) (key : List (BitVec 8)) (k : aead.Key)
    (hk : ChaChaKeyHolds key k) (nonce : aead.Nonce) (aad : Slice U8)
    {InOut : Type} (AsMutInst : core.convert.AsMut InOut (Slice U8))
    (ExtendInst : core.iter.traits.collect.Extend InOut U8) (in_out : InOut) (view : Slice U8)
    (back : Slice U8 → InOut) (hview : AsMutInst.as_mut in_out = ok (view, back))
    (Q : (core.result.Result Unit error.Error) × InOut → Prop)
    (hlong : 2 ^ 38 - 64 < view.length → Q (.Err .WrongLength, back view))
    (hext : ∀ (ct : Slice U8) (tag : Std.Array U8 16#usize), view.length ≤ 2 ^ 38 - 64 →
      ct.length = view.length →
      (bvs ct.val, bvs tag.val) = chacha20poly1305.seal key (bvs nonce.bytes.val) (bvs aad.val) (bvs view.val) →
      ExtendInst.extend (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U8) (back ct)
        tag.to_slice ⦃ out => Q (.Ok (), out) ⦄) :
    k.seal_in_place_append_tag AsMutInst ExtendInst nonce aad in_out ⦃ Q ⦄ := by
  unfold aead.Key.seal_in_place_append_tag
  simp only [hview, bind_ok]
  apply WP.spec_bind (chacha20_poly1305_seal h key k hk nonce aad view)
  rintro ⟨r, ct⟩ hr
  dsimp only at hr
  split at hr
  · obtain ⟨tag, rfl, hlen, henc⟩ := hr
    exact WP.spec_bind (hext ct tag.bytes (by assumption) hlen henc) fun out h => (WP.spec_ok _).2 h
  · obtain ⟨rfl, rfl⟩ := hr
    exact (WP.spec_ok _).2 (hlong (by omega))

/-- `Vec<u8>`'s `extend` appends the tag to the ciphertext. -/
theorem vec_extend_tag (ExtendInst : core.iter.traits.collect.Extend (alloc.vec.Vec U8) U8)
    (hextend : VecExtend ExtendInst) (ct : Slice U8) (tag : Std.Array U8 16#usize) (n : Nat)
    (hct : ct.length = n) (hroom : n + 16 ≤ Usize.max) :
    ExtendInst.extend (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U8) ⟨ct⟩ tag.to_slice ⦃ out =>
      out.length = n + 16 ∧ out.val.take n = ct.val ∧ out.val.drop n = tag.val ⦄ := by
  have hct : ct.val.length = n := hct
  have htag : tag.to_slice.val = tag.val := by simp [Std.Array.to_slice]
  have htl : tag.val.length = 16 := by simp
  rw [hextend]
  unfold alloc.vec.Vec.extend_from_slice
  have hfit : (⟨ct⟩ : alloc.vec.Vec U8).length + tag.to_slice.length ≤ Usize.max := by
    change ct.val.length + tag.to_slice.val.length ≤ Usize.max
    rw [htag, htl, hct]; exact hroom
  rw [dite_eq_left hfit]
  apply WP.spec_bind (List.clone_spec fun _ _ => rfl)
  rintro s' ⟨hs', -⟩
  have hv : ∀ h, (alloc.vec.Vec.from ((⟨ct⟩ : alloc.vec.Vec U8).val ++ s'.val) h).val = ct.val ++ tag.val := by
    intro h; rw [alloc.vec.Vec.from_val, hs', htag]; rfl
  refine (WP.spec_ok _).2 ⟨?_, ?_, ?_⟩
  · rw [alloc.vec.Vec.length, hv, List.length_append, hct, htl]
  · rw [hv, List.take_left' hct]
  · rw [hv, List.drop_left' hct]

/-- Sealing a `Vec<u8>` with room for the tag: the vector becomes the
ciphertext followed by the tag, RFC 8439's, or a vector past 2^38 - 64 bytes
is refused, left as it is. -/
theorem chacha20_poly1305_seal_append_tag_vec (h : RunsChaCha20Poly1305) (key : List (BitVec 8))
    (k : aead.Key) (hk : ChaChaKeyHolds key k) (nonce : aead.Nonce) (aad : Slice U8)
    (AsMutInst : core.convert.AsMut (alloc.vec.Vec U8) (Slice U8))
    (ExtendInst : core.iter.traits.collect.Extend (alloc.vec.Vec U8) U8) (hasmut : VecAsMut AsMutInst)
    (hextend : VecExtend ExtendInst) (in_out : alloc.vec.Vec U8) (hroom : in_out.length + 16 ≤ Usize.max) :
    k.seal_in_place_append_tag AsMutInst ExtendInst nonce aad in_out ⦃ r =>
      if in_out.length ≤ 2 ^ 38 - 64 then
        r.1 = .Ok () ∧ r.2.length = in_out.length + 16 ∧
          (bvs (r.2.val.take in_out.length), bvs (r.2.val.drop in_out.length)) =
            chacha20poly1305.seal key (bvs nonce.bytes.val) (bvs aad.val) (bvs in_out.val)
      else r.1 = .Err .WrongLength ∧ r.2 = in_out ⦄ := by
  have hl : in_out.slice.length = in_out.length := rfl
  apply chacha20_poly1305_seal_append_tag h key k hk nonce aad AsMutInst ExtendInst in_out in_out.slice
    (fun s => ⟨s⟩) (hasmut in_out)
  · intro hlong
    rw [hl] at hlong
    dsimp only
    rw [ite_eq_right (by omega)]
    exact ⟨rfl, rfl⟩
  · intro ct tag hshort hlen henc
    rw [hl] at hshort hlen
    apply WP.spec_mono (vec_extend_tag ExtendInst hextend ct tag in_out.length hlen hroom)
    rintro out ⟨hol, hot, hod⟩
    dsimp only
    rw [ite_eq_left hshort]
    exact ⟨rfl, hol, by rw [hot, hod]; exact henc⟩

/-- Opening against a separate tag: a message past 2^38 - 64 bytes is
refused, left as it is; otherwise the call succeeds exactly when RFC 8439's
tag is `tag`, leaving the plaintext in place, and fails, leaving zeros. -/
theorem chacha20_poly1305_open_separate_tag (h : RunsChaCha20Poly1305) (key : List (BitVec 8))
    (k : aead.Key) (hk : ChaChaKeyHolds key k) (nonce : aead.Nonce) (aad : Slice U8) (tag : aead.Tag)
    (in_out : Slice U8) :
    k.open_in_place_separate_tag nonce aad tag in_out ⦃ r =>
      if in_out.length ≤ 2 ^ 38 - 64 then
        let out := chacha20poly1305.open key (bvs nonce.bytes.val) (bvs aad.val) (bvs in_out.val)
          (bvs tag.bytes.val)
        if out.2 then r.1 = .Ok r.2 ∧ bvs r.2.val = out.1
        else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate in_out.length 0#u8
      else r.1 = .Err .WrongLength ∧ r.2 = in_out ⦄ := by
  obtain ⟨c, rfl, rfl⟩ := hk
  unfold aead.Key.open_in_place_separate_tag aead.Sealer.open
  simp only [mid.chacha20poly1305.ChaCha20Poly1305.Insts.RindAeadCipher.open]
  apply WP.spec_bind (chacha20_poly1305_decrypt_spec h c nonce.bytes aad in_out tag.bytes)
  rintro ⟨r, out⟩ hr
  dsimp only at hr
  split at hr
  · split at hr
    · obtain ⟨rfl, -, hout⟩ := hr
      refine (WP.spec_ok _).2 ?_
      simp_all
    · obtain ⟨rfl, hout⟩ := hr
      refine (WP.spec_ok _).2 ?_
      simp_all
  · obtain ⟨rfl, rfl⟩ := hr
    refine (WP.spec_ok _).2 ?_
    simp_all

/-- Opening the ciphertext followed by its tag: shorter than a tag is
refused, and otherwise the call opens the bytes before the tag against it, as
`chacha20_poly1305_open_separate_tag` states. -/
theorem chacha20_poly1305_open (h : RunsChaCha20Poly1305) (key : List (BitVec 8)) (k : aead.Key)
    (hk : ChaChaKeyHolds key k) (nonce : aead.Nonce) (aad in_out : Slice U8) :
    k.open_in_place nonce aad in_out ⦃ r =>
      if in_out.length < 16 then r.1 = .Err .DecryptFailed else
      if in_out.length - 16 ≤ 2 ^ 38 - 64 then
        let out := chacha20poly1305.open key (bvs nonce.bytes.val) (bvs aad.val)
          (bvs (in_out.val.take (in_out.length - 16))) (bvs (in_out.val.drop (in_out.length - 16)))
        if out.2 then r.1 = .Ok r.2 ∧ bvs r.2.val = out.1
        else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate (in_out.length - 16) 0#u8
      else r.1 = .Err .WrongLength ∧ r.2.val = in_out.val.take (in_out.length - 16) ⦄ := by
  unfold aead.Key.open_in_place
  by_cases hs : in_out.length < 16
  · rw [ite_eq_left hs]
    exact (WP.spec_ok _).2 (by rw [ite_eq_left hs])
  · rw [ite_eq_right hs]
    have hd : (in_out.val.drop (in_out.length - 16)).length = 16 := by simp [Slice.length] at *; omega
    rw [dite_eq_left hd]
    apply WP.spec_mono (chacha20_poly1305_open_separate_tag h key k hk nonce aad _ _)
    intro r hr
    rw [ite_eq_right hs]
    simp only [Slice.from_val, Std.Array.from_val] at hr
    have hl : ∀ h, (Slice.from (List.take (in_out.length - 16) in_out.val) h).length = in_out.length - 16 := by
      intro h; rw [Slice.length, Slice.from_val, List.length_take]; simp only [Slice.length] at *; omega
    rw [hl] at hr
    split at hr
    · rw [ite_eq_left (by assumption)]; exact hr
    · rw [ite_eq_right (by assumption)]
      obtain ⟨h1, h2⟩ := hr
      exact ⟨h1, by rw [h2, Slice.from_val]⟩

/-! ## `RandomizedNonceKey`, XChaCha20-Poly1305 under a random nonce -/

/-- `RandomizedNonceKey::new` holds the key's bytes. -/
theorem randomized_nonce_key_new (key : Std.Array U8 32#usize) :
    aead.RandomizedNonceKey.new key ⦃ k => k.key.key = key ⦄ := by
  unfold aead.RandomizedNonceKey.new mid.xchacha20poly1305.XChaCha20Poly1305.new
  simp [low.ct.secret_slice, lift, WP.spec_ok]

/-- Sealing a `Vec<u8>` with room for the tag, when the system's random
source fills the nonce with `nonce`: the call fails if the source does,
leaving the vector, and otherwise returns `nonce` and makes the vector the
ciphertext followed by the tag, draft-irtf-cfrg-xchacha-03's, or refuses a
vector past 2^38 - 64 bytes, leaving it as it is. -/
theorem randomized_nonce_key_seal_append_tag_vec (h : RunsChaCha20Poly1305) (k : aead.RandomizedNonceKey)
    (aad : Slice U8) (AsMutInst : core.convert.AsMut (alloc.vec.Vec U8) (Slice U8))
    (ExtendInst : core.iter.traits.collect.Extend (alloc.vec.Vec U8) U8) (hasmut : VecAsMut AsMutInst)
    (hextend : VecExtend ExtendInst) (in_out : alloc.vec.Vec U8) (hroom : in_out.length + 16 ≤ Usize.max)
    (rr : core.result.Result Unit getrandom.error.Error) (nonce : Slice U8) (hn : nonce.length = 24)
    (hfill : getrandom.fill (Std.Array.repeat 24#usize 0#u8).to_slice = ok (rr, nonce)) :
    k.seal_in_place_append_tag AsMutInst ExtendInst aad in_out ⦃ r =>
      (rr = .Ok () →
        if in_out.length ≤ 2 ^ 38 - 64 then
          ∃ n : aead.RandomNonce, r.1 = .Ok n ∧ n.bytes.val = nonce.val ∧ r.2.length = in_out.length + 16 ∧
            (bvs (r.2.val.take in_out.length), bvs (r.2.val.drop in_out.length)) =
              chacha20poly1305.xseal (bvs k.key.key.val) (bvs nonce.val) (bvs aad.val) (bvs in_out.val)
        else r.1 = .Err .WrongLength ∧ r.2 = in_out) ∧
      (rr ≠ .Ok () → r.1 = .Err .RngFailed ∧ r.2 = in_out) ⦄ := by
  unfold aead.RandomizedNonceKey.seal_in_place_append_tag mid.rng.SystemRandom.Insts.RindMidRngRandomSource.fill
  generalize Std.Array.repeat 24#usize 0#u8 = A at hfill ⊢
  generalize Std.Array.repeat 16#usize 0#u8 = T
  have hfrom : (A.from_slice nonce).val = nonce.val := by
    simp [Std.Array.from_slice, hn]
  step with Std.Array.to_slice_mut_spec as ⟨s, back, hs, hb⟩
  have hs' : s = A.to_slice := by
    apply Slice.ext; rw [hs]; simp [Std.Array.to_slice]
  subst hs' hb
  rcases rr with ⟨⟨⟩⟩ | e
  · rw [hfill]
    simp only [core.result.Result.map_err, hasmut in_out]
    step*
    dsimp only [alloc.vec.Vec.deref_mut]
    have hl : in_out.slice.length = in_out.length := rfl
    apply WP.spec_bind (xchacha20_poly1305_encrypt_spec h k.key _ aad in_out.slice _)
    rintro ⟨r, ct, tag⟩ hr
    dsimp only at hr
    rw [hfrom, hl] at hr
    split at hr
    · obtain ⟨rfl, hlen, henc⟩ := hr
      simp only
      apply WP.spec_bind (vec_extend_tag ExtendInst hextend ct tag in_out.length hlen hroom)
      rintro out ⟨hol, hot, hod⟩
      refine (WP.spec_ok _).2 ⟨fun _ => ?_, fun hne => absurd rfl hne⟩
      rw [ite_eq_left (by assumption)]
      exact ⟨_, rfl, hfrom, hol, by rw [hot, hod]; exact henc⟩
    · obtain ⟨rfl, rfl⟩ := hr
      refine (WP.spec_ok _).2 ⟨fun _ => ?_, fun hne => absurd rfl hne⟩
      rw [ite_eq_right (by assumption)]
      exact ⟨rfl, rfl⟩
  · rw [hfill]
    simp only [core.result.Result.map_err,
      mid.rng.RandomSourceSystemRandom.fill.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once]
    step*

/-- Opening the ciphertext followed by its tag under the nonce sealing
returned: shorter than a tag is refused, and otherwise the call succeeds
exactly when draft-irtf-cfrg-xchacha-03's tag over the bytes before the tag is
the last 16, leaving the plaintext in place, and fails, leaving zeros, or
refuses more than 2^38 - 64 bytes before the tag, leaving them. -/
theorem randomized_nonce_key_open (h : RunsChaCha20Poly1305) (k : aead.RandomizedNonceKey)
    (nonce : aead.RandomNonce) (aad in_out : Slice U8) :
    k.open_in_place nonce aad in_out ⦃ r =>
      if in_out.length < 16 then r.1 = .Err .DecryptFailed else
      if in_out.length - 16 ≤ 2 ^ 38 - 64 then
        let out := chacha20poly1305.xopen (bvs k.key.key.val) (bvs nonce.bytes.val) (bvs aad.val)
          (bvs (in_out.val.take (in_out.length - 16))) (bvs (in_out.val.drop (in_out.length - 16)))
        if out.2 then r.1 = .Ok r.2 ∧ bvs r.2.val = out.1
        else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate (in_out.length - 16) 0#u8
      else r.1 = .Err .WrongLength ∧ r.2.val = in_out.val.take (in_out.length - 16) ⦄ := by
  unfold aead.RandomizedNonceKey.open_in_place
  by_cases hs : in_out.length < 16
  · rw [ite_eq_left hs]
    exact (WP.spec_ok _).2 (by rw [ite_eq_left hs])
  · rw [ite_eq_right hs]
    have hd : (in_out.val.drop (in_out.length - 16)).length = 16 := by simp [Slice.length] at *; omega
    rw [dite_eq_left hd]
    apply WP.spec_bind (xchacha20_poly1305_decrypt_spec h k.key nonce.bytes aad _ _)
    rintro ⟨r, body⟩ hr
    simp only [Slice.from_val, Std.Array.from_val] at hr
    have hl : ∀ h, (Slice.from (List.take (in_out.length - 16) in_out.val) h).length = in_out.length - 16 := by
      intro h; rw [Slice.length, Slice.from_val, List.length_take]; simp only [Slice.length] at *; omega
    rw [hl] at hr
    split at hr
    · split at hr
      · obtain ⟨rfl, -, hout⟩ := hr
        refine (WP.spec_ok _).2 ?_
        rw [ite_eq_right hs, ite_eq_left (by assumption)]
        simp_all
      · obtain ⟨rfl, hout⟩ := hr
        refine (WP.spec_ok _).2 ?_
        rw [ite_eq_right hs, ite_eq_left (by assumption)]
        simp_all
    · obtain ⟨rfl, rfl⟩ := hr
      refine (WP.spec_ok _).2 ?_
      rw [ite_eq_right hs, ite_eq_right (by assumption)]
      exact ⟨rfl, by rw [Slice.from_val]⟩

end rind.x86_64
