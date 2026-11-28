import Rind.Mcu.Blockwise
import Rind.Sha2Lemmas
import Rind.Sha2Rounds
open Aeneas Aeneas.Std Result rind.spec

/-!
# 32-bit microcontrollers' SHA-512 block function

`low::generic::sha512_rolled` computes cryptol-specs' `processBlocks`,
`Rind.Sha2`'s `compress`, of each whole block in turn:
`sha512_rolled_compress_blocks_spec`. Its block function is one loop of eighty
rounds over a sixteen-word window, each round's schedule word written into
the slot of the one sixteen before it, so `Last16` says the window holds the
sixteen schedule words before the round, wherever the loop is.
-/

namespace rind.mcu.sha512_rolled
open rind.sha512_rounds

/-- The window `x` before round `t`: each of the up to sixteen schedule words
before `t` in its slot, `s mod 16`. -/
def Last16 (W : List (BitVec 64)) (t : Nat) (x : Std.Array U64 16#usize) : Prop :=
  ∀ s < t, t ≤ s + 16 → x.val[s % 16]!.bv = W[s]!

theorem last16_zero (W : List (BitVec 64)) (x : Std.Array U64 16#usize) : Last16 W 0 x :=
  fun _ hs => absurd hs (Nat.not_lt_zero _)

/-- Round `t`'s word, written into slot `t mod 16`, keeps `Last16`. -/
theorem last16_set (W : List (BitVec 64)) (t : Nat) (x : Std.Array U64 16#usize)
    (hx : Last16 W t x) (i : Usize) (hi : i.val = t % 16) (w : U64) (hw : w.bv = W[t]!) :
    Last16 W (t + 1) (x.set i w) := by
  intro s hs hts
  rw [Array.set_val_eq]
  by_cases h : s = t
  · subst h
    rw [← hi, getElem!_pos _ _ (by simp; omega), List.getElem_set_self, hw]
  · rw [getElem!_pos _ _ (by simp; omega), List.getElem_set_ne (by omega),
      ← getElem!_pos _ _ (by simp; omega)]
    exact hx s (by omega) (by omega)

/-- A word of the window, `d` rounds back. -/
theorem last16_get (W : List (BitVec 64)) (t d : Nat) (x : Std.Array U64 16#usize)
    (hx : Last16 W t x) (hd : 0 < d) (hd16 : d ≤ 16) (htd : d ≤ t) (k : Nat) (hk : k = (t - d) % 16)
    (h : k < x.val.length) : (x.val[k]'h).bv = W[t - d]! := by
  subst hk
  rw [← hx (t - d) (by omega) (by omega), getElem!_pos]

/-- FIPS 180-4 section 4.2.3's constants, as `sha512::K` holds them. -/
theorem K_spec : low.generic.sha512.K.val.map (·.bv) = fips512.K := by
  unfold low.generic.sha512.K; rfl

theorem K_index (t : Usize) (ht : t.val < 80) (k : U64)
    (hk : k = low.generic.sha512.K.val[t.val]'(by simp; omega)) : k.bv = fips512.K[t.val]! := by
  rw [← K_spec, hk, getElem!_pos _ t.val (by simp; omega), List.getElem_map]

/-- `as_chunks::<8>` of a block: its sixteen words' bytes, and nothing left. -/
theorem as_chunks8_spec (block : Std.Array U8 128#usize) :
    core.slice.Slice.as_chunks 8#usize (Array.to_slice block) ⦃ p =>
      p.1.val.length = 16 ∧
      (∀ i (h : i < p.1.val.length), (p.1.val[i]).val = (block.val.drop (i * 8)).take 8) ∧
      p.2.length = 0 ⦄ := by
  have hbl : block.val.length = 128 := block.property
  simp only [core.slice.Slice.as_chunks, show (8#usize).val ≠ 0 by simp, ite_false, WP.spec_ok]
  refine ⟨by simp [Slice.from_val, Slice.length, hbl], fun i h => ?_,
    by simp [Slice.from_val, Slice.length, hbl]⟩
  simp only [Slice.from_val, List.getElem_ofFn, Std.Array.from_val, Array.val_to_slice,
    Fin.val_cast, show (8#usize).val = 8 from rfl]

/-- The block's big-endian word `t`, from the eight bytes `as_chunks` cut. -/
theorem word_eq (block : List U8) (t : Nat) (ht : t < 16) (a : Std.Array U8 8#usize)
    (ha : a.val = (block.drop (t * 8)).take 8) :
    (BitVec.fromBEBytes (a.val.map U8.bv)).setWidth 64 = ((blockWords block).map (·.bv))[t]! := by
  rw [getElem!_pos _ _ (by simp [blockWords]; omega), List.getElem_map, ha]
  simp only [blockWords, List.getElem_map, List.getElem_range]
  rw [Nat.mul_comm 8 t]
  rfl

set_option maxHeartbeats 1000000 in
/-- Round `t`'s schedule word, written into the window. -/
theorem schedule_spec (block : Std.Array U8 128#usize) (words : Slice (Std.Array U8 8#usize))
    (hwl : words.val.length = 16)
    (hw : ∀ i (h : i < words.val.length), (words.val[i]).val = (block.val.drop (i * 8)).take 8)
    (x : Std.Array U64 16#usize) (t : Usize) (ht : t.val < 80)
    (hx : Last16 (fips512.schedule ((blockWords block.val).map (·.bv))) t.val x) :
    low.generic.sha512_rolled.schedule x words t ⦃ r =>
      r.1.bv = (fips512.schedule ((blockWords block.val).map (·.bv)))[t.val]! ∧
      Last16 (fips512.schedule ((blockWords block.val).map (·.bv))) (t.val + 1) r.2 ⦄ := by
  set M := (blockWords block.val).map (·.bv) with hM_def
  have hM : M.length = 16 := by simp [M, blockWords_length]
  set W := fips512.schedule M
  unfold low.generic.sha512_rolled.schedule
  split
  · rename_i h16
    have h16' : t.val < 16 := by scalar_tac
    step with Slice.index_usize_spec as ⟨a, ha⟩
    step as ⟨w_t, hw_t⟩
    step as ⟨x1, hx1⟩
    have hwt : w_t.bv = W[t.val]! := by
      rw [schedule_lt M hM _ h16', hw_t, cast_setWidth]
      exact word_eq block.val t.val h16' a (by rw [ha]; exact hw _ _)
    refine ⟨hwt, ?_⟩
    rw [hx1]; exact last16_set _ _ x hx t (by omega) w_t hwt
  · rename_i h16
    have h16' : 16 ≤ t.val := by scalar_tac
    step*
    have g : ∀ (d : Nat) (u : U64) (k : Usize) (hd : 0 < d) (hd16 : d ≤ 16)
        (hk : k.val = (t.val - d) % 16) (h : k.val < x.val.length) (hu : u = x.val[k.val]),
        u.bv = W[t.val - d]! := fun d u k hd hd16 hk h hu => by
      rw [hu]; exact last16_get W t.val d x hx hd hd16 (by omega) _ hk h
    have g2 := g 2 i2 i1 (by omega) (by omega) (by rw [i1_post, i_post]) _ i2_post
    have g5 := g 2 i5 i4 (by omega) (by omega) (by rw [i4_post, i_post]) _ i5_post
    have g9 := g 2 i9 i8 (by omega) (by omega) (by rw [i8_post, i_post]) _ i9_post
    have g14 := g 7 i14 i13 (by omega) (by omega) (by rw [i13_post, i12_post]) _ i14_post
    have g18 := g 15 i18 i17 (by omega) (by omega) (by rw [i17_post, i16_post]) _ i18_post
    have g21 := g 15 i21 i20 (by omega) (by omega) (by rw [i20_post, i16_post]) _ i21_post
    have g25 := g 15 i25 i24 (by omega) (by omega) (by rw [i24_post, i16_post]) _ i25_post
    have g31 := g 16 i31 i30 (by omega) (by omega) (by rw [i30_post, i29_post]) _ i31_post
    have hwt : w_t.bv = W[t.val]! := by
      have e := schedule_succ M hM (t.val - 16) (by omega)
      rw [show t.val - 16 + 16 = t.val by omega, show t.val - 16 + 14 = t.val - 2 by omega,
        show t.val - 16 + 9 = t.val - 7 by omega, show t.val - 16 + 1 = t.val - 15 by omega] at e
      rw [e]
      simp only [w_t_post, i28_post, i15_post, core.num.U64.wrapping_add_bv_eq, i11_post1,
        i7_post1, i27_post1, i23_post1, i10_post1, i26_post1, i3_post, i6_post, i19_post,
        i22_post, bv_rotate_right64, g2, g5, g9, g14, g18, g21, g25, g31, fips512.smallSigma0,
        fips512.smallSigma1]
      rfl
    refine ⟨hwt, ?_⟩
    rw [w1_post]; exact last16_set _ _ x hx i32 (by rw [i32_post]) w_t hwt

/-- One round, in the working variables' bit-vectors. -/
theorem round_eq (W H : List (BitVec 64)) (t : Nat) (w k a b c d e f g h t1 t2 : U64)
    (hs : [a.bv, b.bv, c.bv, d.bv, e.bv, f.bv, g.bv, h.bv] = (List.range t).foldl (sha512Round W) H)
    (hw : w.bv = W[t]!) (hk : k.bv = fips512.K[t]!)
    (ht1 : t1.bv = h.bv + fips512.bigSigma1 e.bv + fips512.ch e.bv f.bv g.bv + k.bv + w.bv)
    (ht2 : t2.bv = fips512.bigSigma0 a.bv + fips512.maj a.bv b.bv c.bv) :
    [t1.bv + t2.bv, a.bv, b.bv, c.bv, d.bv + t1.bv, e.bv, f.bv, g.bv] =
      (List.range (t + 1)).foldl (sha512Round W) H := by
  rw [List.range_succ, List.foldl_append, ← hs]
  simp only [List.foldl_cons, List.foldl_nil, sha512Round, List.getElem!_cons_succ,
    List.getElem!_cons_zero, ht1, ht2, hw, hk]

/-- What the round loop keeps before round `it.start`: the window, and the
working variables after the rounds before it. -/
def Inv (M H : List (BitVec 64))
    (p : core.ops.range.Range Usize × U64 × U64 × U64 × U64 × U64 × U64 × U64 × U64 ×
      Std.Array U64 16#usize) : Prop :=
  match p with
  | (it, a, b, c, d, e, f, g, h, x) =>
    it.start.val ≤ 80 ∧ it.end.val = 80 ∧ Last16 (fips512.schedule M) it.start.val x ∧
      [a.bv, b.bv, c.bv, d.bv, e.bv, f.bv, g.bv, h.bv] =
        (List.range it.start.val).foldl (sha512Round (fips512.schedule M)) H

set_option maxHeartbeats 4000000 in
/-- The eighty rounds, from round `it.start`. -/
theorem rounds_spec (block : Std.Array U8 128#usize) (words : Slice (Std.Array U8 8#usize))
    (hwl : words.val.length = 16)
    (hw : ∀ i (h : i < words.val.length), (words.val[i]).val = (block.val.drop (i * 8)).take 8)
    (H : List (BitVec 64)) (it : core.ops.range.Range Usize) (a b c d e f g h : U64)
    (x : Std.Array U64 16#usize)
    (hinv : Inv ((blockWords block.val).map (·.bv)) H (it, a, b, c, d, e, f, g, h, x)) :
    low.generic.sha512_rolled.sha512_compress_block_loop it words a b c d e f g h x ⦃ r =>
      [r.1.bv, r.2.1.bv, r.2.2.1.bv, r.2.2.2.1.bv, r.2.2.2.2.1.bv, r.2.2.2.2.2.1.bv,
        r.2.2.2.2.2.2.1.bv, r.2.2.2.2.2.2.2.bv] =
        (List.range 80).foldl (sha512Round (fips512.schedule ((blockWords block.val).map (·.bv)))) H ⦄ := by
  unfold low.generic.sha512_rolled.sha512_compress_block_loop
  apply loop.spec_decr_nat (fun p => 80 - p.1.start.val) (Inv ((blockWords block.val).map (·.bv)) H)
  · rintro ⟨it, a, b, c, d, e, f, g, h, x⟩ ⟨hs, he, hx, hst⟩
    unfold low.generic.sha512_rolled.sha512_compress_block_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      dsimp only
      step with schedule_spec block words hwl hw x it.start (by omega) hx as ⟨w_t, x1, hwt, hx1⟩
      step*
      refine ⟨⟨by omega, by rw [hen]; exact he, by rw [hst']; exact hx1, ?_⟩, by omega⟩
      have hk : i11.bv = fips512.K[it.start.val]! := K_index it.start (by omega) i11 i11_post
      have ht1 : t1.bv = h.bv + fips512.bigSigma1 e.bv + fips512.ch e.bv f.bv g.bv + i11.bv +
          w_t.bv := by
        simp only [t1_post, i12_post, i10_post, i5_post, core.num.U64.wrapping_add_bv_eq,
          i9_post1, i6_post1, i8_post1, i7_post, UScalar.bv_not, i4_post1, i2_post1, i_post,
          i1_post, i3_post, bv_rotate_right64, fips512.bigSigma1, fips512.ch]
        rfl
      have ht2 : t2.bv = fips512.bigSigma0 a.bv + fips512.maj a.bv b.bv c.bv := by
        simp only [t2_post, core.num.U64.wrapping_add_bv_eq, i22_post1, i20_post1, i21_post1,
          i18_post1, i19_post1, i17_post1, i15_post1, i16_post, i13_post, i14_post,
          bv_rotate_right64, fips512.bigSigma0, fips512.maj]
        rfl
      simp only [a1_post, e1_post, core.num.U64.wrapping_add_bv_eq]
      rw [hst']
      exact round_eq _ H _ w_t i11 a b c d e f g h t1 t2 hst hwt hk ht1 ht2
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.start.val = 80 by omega] at hst
      exact hst
  · exact hinv

set_option maxHeartbeats 1000000 in
/-- One block: FIPS 180-4's compression of it into `state`. -/
theorem block_spec (state : Std.Array U64 8#usize) (block : Std.Array U8 128#usize) :
    low.generic.sha512_rolled.sha512_compress_block state block ⦃ r =>
      r.val = processBlock state.val (blockWords block.val) ⦄ := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, hst⟩ := arr8 state
  unfold low.generic.sha512_rolled.sha512_compress_block
  step as ⟨sl, hsl⟩
  rw [hsl]
  step with as_chunks8_spec block as ⟨words, rest, hwl, hw, hrest⟩
  step as ⟨bempty, hbe⟩
  step
  step as ⟨a, ha⟩
  step as ⟨b, hb⟩
  step as ⟨c, hc⟩
  step as ⟨d, hd⟩
  step as ⟨e, he⟩
  step as ⟨f, hf⟩
  step as ⟨g, hg⟩
  step as ⟨h, hh⟩
  simp only [hst, List.getElem_cons_zero, List.getElem_cons_succ] at ha hb hc hd he hf hg hh
  subst s0 s1 s2 s3 s4 s5 s6 s7
  set H : List (BitVec 64) := [a.bv, b.bv, c.bv, d.bv, e.bv, f.bv, g.bv, h.bv]
  step with rounds_spec block words hwl hw H { start := 0#usize, «end» := 80#usize } a b c d e f g h
    (Array.repeat 16#usize 0#u64) ⟨by simp, by simp, last16_zero _ _, by simp [H]⟩
    as ⟨a5, b5, c5, d5, e5, f5, g5, h5, hr⟩
  step*
  have hinj : Function.Injective (List.map (fun x : U64 => x.bv)) :=
    List.map_injective_iff.mpr (fun x y h => (UScalar.eq_equiv_bv_eq x y).mpr h)
  have hr' : r.val.map (·.bv) = [a.bv + a5.bv, b.bv + b5.bv, c.bv + c5.bv, d.bv + d5.bv,
      e.bv + e5.bv, f.bv + f5.bv, g.bv + g5.bv, h.bv + h5.bv] := by
    simp only [r_post, state1_post, state2_post, state3_post, state4_post, state5_post, state6_post,
      state7_post, i_post, i1_post, i2_post, i3_post, i4_post, i5_post, i6_post, i7_post, i8_post,
      i9_post, i10_post, i11_post, i12_post, i13_post, i14_post, i15_post, Array.set_val_eq, hst]
    simp
  apply hinj
  rw [hr', processBlock, List.map_map, compressBlock_eq, hst,
    show [a, b, c, d, e, f, g, h].map (·.bv) = H by rfl, ← hr]
  simp [H, BitVec.add_comm]

end rind.mcu.sha512_rolled

namespace rind.mcu
open sha512_rolled rind.sha512_rounds

/-- The rolled block function computes FIPS 180-4's compression of each whole
block in turn. -/
theorem sha512_rolled_compress_blocks_spec (state : Std.Array U64 8#usize) (blocks : Slice U8)
    (hl : blocks.length % 128 = 0) :
    low.generic.sha512_rolled.sha512_compress_blocks state blocks ⦃ r =>
      r.val = compress state.val blocks.val ⦄ := by
  unfold low.generic.sha512_rolled.sha512_compress_blocks
  step*
  unfold low.generic.sha512_rolled.sha512_compress_blocks_loop
  apply loop.spec_decr_nat (fun p => p.1.length)
    (fun p => p.1.length % 128 = 0 ∧ compress p.2.val p.1.val = compress state.val blocks.val)
  · rintro ⟨rest, st⟩ ⟨hr, hc⟩
    simp only at hr hc ⊢
    unfold low.generic.sha512_rolled.sha512_compress_blocks_loop.body
    unfold core.slice.Slice.split_first_chunk
    split
    · rename_i h
      simp only [bind_ok]
      step with block_spec as ⟨st', hst'⟩
      have hrl : rest.val.length = rest.length := rfl
      have h128 : (128#usize).val = 128 := rfl
      refine ⟨?_, ?_, ?_⟩
      · simp only [Slice.length, Slice.from_val, List.length_drop, h128] at hr h ⊢; omega
      · rw [← hc, compress_block st.val rest.val (by simpa [Slice.length] using h), hst']
        simp only [Slice.from_val, Std.Array.from_val, h128]
      · simp only [Slice.length, Slice.from_val, List.length_drop, h128] at h ⊢; omega
    · rename_i h
      simp only [bind_ok, WP.spec_ok]
      have h0 : rest.val = [] := List.eq_nil_of_length_eq_zero (by
        simp only [Slice.length, show (128#usize).val = 128 from rfl] at hr h ⊢; omega)
      rw [← hc, h0, compress_nil]
  · exact ⟨hl, rfl⟩

end rind.mcu
