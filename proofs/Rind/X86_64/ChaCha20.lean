import Rind.X86_64.QuicDispatch
import Rind.Spec
import Rind.Bytes
open Aeneas Aeneas.Std Result rind.spec

/-!
# ChaCha20 header protection, proven from rind's header-protection API to RFC 8439

The `chacha20_*` theorems state what the header-protection API returns for
ChaCha20, in terms of `chacha20.headerProtectionMask`, through the dispatch
`Rind.X86_64.QuicDispatch` models. HACL*'s rounds are Rust, so they are proven
here too, and no axiom stands in for them. `admin/prove` writes the aarch64,
armv7, and portable proofs from this file by renaming the target.
-/

namespace rind.x86_64

/-! ## Words, bytes, and rotations -/

theorem bv_getElem {ty : UScalarTy} (l : List (UScalar ty)) (i : Nat) (h : i < l.length) :
    (l[i]).bv = (l.map (·.bv))[i]! := by
  simp [h]

theorem words_getElem! (b : List (BitVec 8)) (i : Nat) (h : i < b.length / 4) :
    (chacha20.words b)[i]! = chacha20.le32 b[4 * i]! b[4 * i + 1]! b[4 * i + 2]! b[4 * i + 3]! := by
  simp [chacha20.words, h]

/-- A rotation as the rounds compute it, by two shifts. -/
theorem rotl (x : BitVec 32) (n : Nat) (h : 0 < n ∧ n < 32) :
    x.shiftLeft n ||| x.ushiftRight (32 - n) = x.rotateLeft n := by
  rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt h.2]
  rfl

theorem rotl16 (x : BitVec UScalarTy.U32.numBits) :
    x.shiftLeft 16 ||| x.ushiftRight 16 = x.rotateLeft 16 :=
  rotl x 16 (by decide)

theorem rotl12 (x : BitVec UScalarTy.U32.numBits) :
    x.shiftLeft 12 ||| x.ushiftRight 20 = x.rotateLeft 12 :=
  rotl x 12 (by decide)

theorem rotl8 (x : BitVec UScalarTy.U32.numBits) :
    x.shiftLeft 8 ||| x.ushiftRight 24 = x.rotateLeft 8 :=
  rotl x 8 (by decide)

theorem rotl7 (x : BitVec UScalarTy.U32.numBits) :
    x.shiftLeft 7 ||| x.ushiftRight 25 = x.rotateLeft 7 :=
  rotl x 7 (by decide)

theorem cast_usize (a : U32) (h : a.val < 16) : (UScalar.cast .Usize a).val = a.val := by
  rw [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac

/-- `u32::from_le_bytes` reads a little-endian word. -/
theorem fromLEBytes_le32 (a b c d : U8) {h hl} :
    (BitVec.fromLEBytes ((Std.Array.make 4#usize [a, b, c, d] hl).val.map U8.bv)).cast h =
      chacha20.le32 a.bv b.bv c.bv d.bv :=
  rfl

/-! ## HACL*'s rounds, `low::generic::chacha20` -/

/-- The quarter round on four distinct words, as every call passes them. -/
@[step]
theorem quarter_round_spec (st : Slice U32) (a b c d : U32) (hl : st.length = 16)
    (ha : a.val < 16) (hb : b.val < 16) (hc : c.val < 16) (hd : d.val < 16)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val) (hbc : b.val ≠ c.val)
    (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    low.generic.chacha20.quarter_round st a b c d ⦃ st' =>
      st'.length = 16 ∧
      st'.val.map (·.bv) = chacha20.quarterRound (st.val.map (·.bv)) a.val b.val c.val d.val ⦄ := by
  unfold low.generic.chacha20.quarter_round
  step*
  all_goals try agrind
  have hS : (st.val.map (·.bv)).length = 16 := by simp only [List.length_map]; exact hl
  refine ⟨by agrind, ?_⟩
  have h16 : (16#u32).val = 16 := rfl
  have h12 : (12#u32).val = 12 := rfl
  have h20 : (20#u32).val = 20 := rfl
  have h8 : (8#u32).val = 8 := rfl
  have h24 : (24#u32).val = 24 := rfl
  have h7 : (7#u32).val = 7 := rfl
  have h25 : (25#u32).val = 25 := rfl
  simp only [st'_post, st7_post, st6_post, st5_post, st4_post, st3_post, st2_post, st1_post,
    Slice.set_val_eq, List.map_set, chacha20.quarterRound,
    i_post, i1_post, i2_post, i5_post, i6_post, i7_post, i8_post, i9_post, i12_post, i13_post,
    i14_post, i15_post, i16_post, i19_post, i20_post, i21_post, i22_post, i23_post, i26_post, i27_post,
    cast_usize a ha, cast_usize b hb, cast_usize c hc, cast_usize d hd,
    std22_post1, std21_post1, std20_post1, std2_post1, std12_post1, std11_post1, std10_post1,
    std1_post1, i24_post, i25_post, i17_post, i18_post, i10_post, i11_post, i3_post, i4_post,
    core.num.U32.wrapping_shl_bv_eq, core.num.U32.wrapping_shr_bv_eq,
    sta12_post, sta11_post, sta10_post, sta1_post, core.num.U32.wrapping_add_bv_eq,
    sta3_post, stb2_post, std4_post, sta2_post, stb1_post, std3_post, sta0_post, stb0_post, std0_post,
    sta_post, stb_post, std_post, bv_getElem, h16, h12, h20, h8, h24, h7, h25, Nat.reduceMod,
    rotl16, rotl12, rotl8, rotl7, chacha20.qr]
  apply List.ext_getElem?
  intro j
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set, List.length_set, hS, ha, hb, hc, hd,
    ite_true, hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc,
    Ne.symm hbd, Ne.symm hcd, ite_false, Option.getD_some]
  split_ifs <;> first | (exfalso; omega) | rfl

@[step]
theorem double_round_spec (st : Slice U32) (hl : st.length = 16) :
    low.generic.chacha20.double_round st ⦃ st' =>
      st'.length = 16 ∧ st'.val.map (·.bv) = chacha20.innerBlock (st.val.map (·.bv)) ⦄ := by
  unfold low.generic.chacha20.double_round
  step*
  refine ⟨by agrind, ?_⟩
  simp only [chacha20.innerBlock, *]

@[step]
theorem rounds_spec (st : Slice U32) (hl : st.length = 16) :
    low.generic.chacha20.rounds st ⦃ st' =>
      st'.length = 16 ∧ st'.val.map (·.bv) = chacha20.innerBlock^[10] (st.val.map (·.bv)) ⦄ := by
  unfold low.generic.chacha20.rounds
  step*
  refine ⟨by agrind, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, *]

/-! ## The block function, `low::generic::chacha20` -/

theorem state_loop0_spec (key : Std.Array U8 32#usize) (iter : core.ops.range.Range Usize)
    (st : Std.Array U32 16#usize) (F : List (BitVec 32)) (hs : iter.start.val ≤ 8) (he : iter.end.val = 8)
    (hF : (List.range' iter.start.val (8 - iter.start.val)).foldl
      (fun l i => l.set (4 + i) (chacha20.words (key.val.map (·.bv)))[i]!) (st.val.map (·.bv)) = F) :
    low.generic.chacha20.state_loop0 iter key st ⦃ r => r.val.map (·.bv) = F ⦄ := by
  unfold low.generic.chacha20.state_loop0
  apply loop.spec_decr_nat (fun x => 8 - x.1.start.val)
    (fun x => x.1.start.val ≤ 8 ∧ x.1.end.val = 8 ∧
      (List.range' x.1.start.val (8 - x.1.start.val)).foldl
        (fun l i => l.set (4 + i) (chacha20.words (key.val.map (·.bv)))[i]!) (x.2.val.map (·.bv)) = F)
  · rintro ⟨it, st⟩ ⟨hs, he, hF⟩
    simp only at hs he hF ⊢
    unfold low.generic.chacha20.state_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      step*
      refine ⟨by agrind, by agrind, ?_, by agrind⟩
      have hr : List.range' it.start.val (8 - it.start.val) =
          it.start.val :: List.range' it'.start.val (8 - it'.start.val) := by
        rw [hst, show 8 - it.start.val = (8 - (it.start.val + 1)) + 1 by agrind]
        rfl
      rw [hr, List.foldl_cons] at hF
      rw [← hF]
      congr 1
      simp only [a_post, Array.set_val_eq, List.map_set, i10_post]
      congr 1
      rw [i9_post]
      refine (fromLEBytes_le32 i2 i4 i6 i8).trans ?_
      rw [words_getElem! _ _ (by simp; agrind)]
      simp only [i2_post, i4_post, i6_post, i8_post, i7_post, i5_post, i3_post, i1_post, bv_getElem]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have h8 : it.start.val = 8 := by agrind
      simpa [h8] using hF
  · exact ⟨hs, he, hF⟩

theorem state_loop1_spec (nonce : Std.Array U8 16#usize) (iter : core.ops.range.Range Usize)
    (st : Std.Array U32 16#usize) (F : List (BitVec 32)) (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (hF : (List.range' iter.start.val (4 - iter.start.val)).foldl
      (fun l i => l.set (12 + i) (chacha20.words (nonce.val.map (·.bv)))[i]!) (st.val.map (·.bv)) = F) :
    low.generic.chacha20.state_loop1 iter nonce st ⦃ r => r.val.map (·.bv) = F ⦄ := by
  unfold low.generic.chacha20.state_loop1
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧
      (List.range' x.1.start.val (4 - x.1.start.val)).foldl
        (fun l i => l.set (12 + i) (chacha20.words (nonce.val.map (·.bv)))[i]!) (x.2.val.map (·.bv)) = F)
  · rintro ⟨it, st⟩ ⟨hs, he, hF⟩
    simp only at hs he hF ⊢
    unfold low.generic.chacha20.state_loop1.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
      subst ho
      step*
      refine ⟨by agrind, by agrind, ?_, by agrind⟩
      have hr : List.range' it.start.val (4 - it.start.val) =
          it.start.val :: List.range' it'.start.val (4 - it'.start.val) := by
        rw [hst, show 4 - it.start.val = (4 - (it.start.val + 1)) + 1 by agrind]
        rfl
      rw [hr, List.foldl_cons] at hF
      rw [← hF]
      congr 1
      simp only [a_post, Array.set_val_eq, List.map_set, i10_post]
      congr 1
      rw [i9_post]
      refine (fromLEBytes_le32 i2 i4 i6 i8).trans ?_
      rw [words_getElem! _ _ (by simp; agrind)]
      simp only [i2_post, i4_post, i6_post, i8_post, i7_post, i5_post, i3_post, i1_post, bv_getElem]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have h4 : it.start.val = 4 := by agrind
      simpa [h4] using hF
  · exact ⟨hs, he, hF⟩

/-- ChaCha20's constant, as `chacha20.block` spells it. -/
theorem SIGMA_bv : low.generic.chacha20.SIGMA.val.map (·.bv) =
    [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] := by
  simp [low.generic.chacha20.SIGMA]

@[step]
theorem state_spec (key : Std.Array U8 32#usize) (nonce : Std.Array U8 16#usize) :
    low.generic.chacha20.state key nonce ⦃ st =>
      st.val.map (·.bv) = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++
        chacha20.words (key.val.map (·.bv)) ++ chacha20.words (nonce.val.map (·.bv)) ⦄ := by
  unfold low.generic.chacha20.state
  step*
  step with state_loop0_spec key { start := 0#usize, «end» := 8#usize } _ _ (by simp) (by simp) rfl as ⟨st2, h2⟩
  step with state_loop1_spec nonce { start := 0#usize, «end» := 4#usize } _ _ (by simp) (by simp) rfl as ⟨st3, h3⟩
  have hk : (key.val.map (·.bv)).length = 32 := by simp
  have hn : (nonce.val.map (·.bv)).length = 16 := by simp
  rw [h3, h2, s_post2, s2_post, s1_post]
  simp [chacha20.words, hk, hn, List.range', List.range_succ, SIGMA_bv, Array.repeat, List.setSlice!]

/-- The keystream block's words, added and written out little-endian. -/
def keystream (st input : Std.Array U32 16#usize) : List (BitVec 32) :=
  List.zipWith (· + ·) (st.val.map (·.bv)) (input.val.map (·.bv))

theorem keystream_loop_spec (input st : Std.Array U32 16#usize)
    (iter : core.ops.range.Range Usize) (out : Std.Array U8 64#usize) (hs : iter.start.val ≤ 16)
    (he : iter.end.val = 16)
    (ho : (out.val.map (·.bv)).take (4 * iter.start.val) =
      ((keystream st input).take iter.start.val).flatMap BitVec.toLEBytes) :
    low.generic.chacha20.keystream_loop iter input st out ⦃ r =>
      r.val.map (·.bv) = (keystream st input).flatMap BitVec.toLEBytes ⦄ := by
  unfold low.generic.chacha20.keystream_loop
  apply loop.spec_decr_nat (fun x => 16 - x.1.start.val)
    (fun x => x.1.start.val ≤ 16 ∧ x.1.end.val = 16 ∧
      (x.2.val.map (·.bv)).take (4 * x.1.start.val) =
        ((keystream st input).take x.1.start.val).flatMap BitVec.toLEBytes)
  · rintro ⟨it, out⟩ ⟨hs, he, ho⟩
    simp only at hs he ho ⊢
    unfold low.generic.chacha20.keystream_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
      subst ho'
      step*
      case h => simp [s_post1, s1_post, i3_post, i2_post, i1_post]; agrind
      refine ⟨by agrind, by agrind, ?_, by agrind⟩
      have hk : it.start.val < 16 := by agrind
      have ha : a.val.map (·.bv) = (i4.bv + i5.bv).toLEBytes := by
        rw [a_post, i6_post, core.num.U32.wrapping_add_bv_eq, List.map_map]
        exact List.map_id _
      have ha4 : (a.val.map (·.bv)).length = 4 := by simp
      rw [s_post2, s2_post, s1_post, Array.val_to_slice, List.map_setSlice!, hst,
        show 4 * (it.start.val + 1) = i1.val + (a.val.map (·.bv)).length by rw [ha4, i1_post]; ring,
        take_setSlice! _ _ _ (by simp [i1_post]; agrind), i1_post, ho, ha, List.take_add_one,
        List.flatMap_append]
      congr 1
      have hz : (keystream st input)[it.start.val]? = some (i4.bv + i5.bv) := by
        simp [keystream, i4_post, i5_post, hk]
      simp [hz]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      have h16 : it.start.val = 16 := by agrind
      have hl : (keystream st input).length = 16 := by simp [keystream]
      rw [h16, List.take_of_length_le (by simp), List.take_of_length_le (by rw [hl])] at ho
      simpa using ho
  · exact ⟨hs, he, ho⟩

/-- A 16-byte counter and nonce's words: the counter's, then the nonce's. -/
theorem words_counter_nonce (b : List (BitVec 8)) (h : b.length = 16) :
    chacha20.words b = [chacha20.le32 b[0]! b[1]! b[2]! b[3]!] ++ chacha20.words (b.drop 4) := by
  simp [chacha20.words, h, List.range_succ]

/-- The keystream block for a state: its rounds, added to it, written out
little-endian. -/
@[step]
theorem keystream_spec (input : Std.Array U32 16#usize) :
    low.generic.chacha20.keystream input ⦃ out =>
      out.val.map (·.bv) = (List.zipWith (· + ·) (chacha20.innerBlock^[10] (input.val.map (·.bv)))
        (input.val.map (·.bv))).flatMap BitVec.toLEBytes ⦄ := by
  unfold low.generic.chacha20.keystream
  step*
  apply WP.spec_mono (keystream_loop_spec input _ _ _ (by simp) (by simp) (by simp))
  intro out hout
  have hst : (to_slice_mut_back s1).val = s1.val := by
    rw [to_slice_mut_back_post]; simp [Std.Array.from_slice, s1_post]
  rw [hout, keystream, hst, s1_post1, s_post]

@[step]
theorem chacha20_block_spec (key : Std.Array U8 32#usize) (counter_nonce : Std.Array U8 16#usize) :
    low.generic.chacha20.chacha20_block key counter_nonce ⦃ out =>
      let cn := counter_nonce.val.map (·.bv)
      out.val.map (·.bv) =
        chacha20.block (key.val.map (·.bv)) (chacha20.le32 cn[0]! cn[1]! cn[2]! cn[3]!) (cn.drop 4) ⦄ := by
  unfold low.generic.chacha20.chacha20_block
  step*
  rw [out_post, a_post, words_counter_nonce (counter_nonce.val.map (·.bv)) (by simp)]
  simp only [chacha20.block, List.append_assoc]

/-! ## Header protection, `mid::chacha20` and `aead::quic` -/

/-- The entry guard admits a call that handles secrets: the one fact about the
machine the mask needs, as it runs the same Rust on every CPU. Each target's
`Runs` implies it. -/
def RunsChaCha20 : Prop := ∃ e, low.entry.Entry.new_secret = ok e

@[step]
theorem chacha20_new_secret_spec (h : RunsChaCha20) :
    low.entry.Entry.new_secret ⦃ _ => True ⦄ := by
  obtain ⟨e, he⟩ := h
  simp [he]

@[step]
theorem header_protection_mask_spec (h : RunsChaCha20) (k : mid.chacha20.ChaCha20)
    (sample : Std.Array U8 16#usize) :
    mid.chacha20.ChaCha20.header_protection_mask k sample ⦃ mask =>
      mask.val.map (·.bv) =
        chacha20.headerProtectionMask (k.key.val.map (·.bv)) (sample.val.map (·.bv)) ⦄ := by
  unfold mid.chacha20.ChaCha20.header_protection_mask low.ct.public_slice
  step*
  have hb : block.val.length = 64 := block.property
  rw [chacha20.headerProtectionMask, ← block_post]
  apply List.ext_getElem (by simp [Std.Array.make, hb])
  intro j hj _
  have hj5 : j < 5 := by simpa [Std.Array.make] using hj
  obtain rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  all_goals simp [Std.Array.make, i_post, i1_post, i2_post, i3_post, i4_post]

/-! ## The header-protection API, through the modelled dispatch -/

/-- A ChaCha20 header-protection key is refused unless it is 32 bytes, and
otherwise holds them. -/
theorem chacha20_new (key : Slice U8) :
    aead.quic.HeaderProtectionKey.new aead.quic.CHACHA20 key ⦃ r =>
      if key.length = 32 then ∃ k : mid.chacha20.ChaCha20, r = .Ok (.ChaCha20 k) ∧ k.key.val = key.val
      else r = .Err .WrongLength ⦄ := by
  unfold aead.quic.HeaderProtectionKey.new aead.quic.CHACHA20
  simp only
  step*
  rcases x with a | e
  · obtain ⟨ha, hl⟩ := x_post
    have hk : key.length = 32 := by rw [Slice.length, ← ha]; exact a.property
    simp [mid.chacha20.ChaCha20.new, low.ct.into_secret, aead.quic.Masker.new, hk, ha]
  · simp [x_post]

/-- A ChaCha20 header-protection key's mask for a sample: RFC 9001's, the
first five bytes of RFC 8439's keystream block for the key, with the sample
as the block counter and nonce. -/
theorem chacha20_mask (h : RunsChaCha20) (k : mid.chacha20.ChaCha20) (sample : Std.Array U8 16#usize) :
    aead.quic.HeaderProtectionKey.mask (.ChaCha20 k) sample ⦃ mask =>
      mask.val.map (·.bv) =
        chacha20.headerProtectionMask (k.key.val.map (·.bv)) (sample.val.map (·.bv)) ⦄ := by
  unfold aead.quic.HeaderProtectionKey.mask aead.quic.Masker.mask
  exact header_protection_mask_spec h k sample

end rind.x86_64
