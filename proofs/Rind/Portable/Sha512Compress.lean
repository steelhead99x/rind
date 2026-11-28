import Rind.Portable.Blockwise
import Rind.Sha2Lemmas
import Rind.Sha2Rounds
open Aeneas Aeneas.Std Result rind.spec

/-!
# The portable backend's SHA-512 block function

`low::generic::sha512` (aws-lc's 64-bit `sha512_block_data_order_nohw`, in
Rust) computes cryptol-specs' `processBlocks`, `Rind.Sha2`'s `compress`, of
each whole block in turn: `generic_sha512_compress_blocks_spec`. The proof is
`Rind.Portable.Sha256Compress`'s over 64-bit words, eighty rounds, and four
passes of sixteen.
-/

namespace rind.portable.sha512_blocks
open rind.sha512_rounds

/-- One round, given the working variables after rounds `0` to `t - 1`. -/
theorem round_spec (W H : List (BitVec 64)) (t t' : Nat) (ht : t' = t + 1) (w k a b c d e f g h : U64)
    (hs : [a.bv, b.bv, c.bv, d.bv, e.bv, f.bv, g.bv, h.bv] = (List.range t).foldl (sha512Round W) H)
    (hw : w.bv = W[t]!) (hk : k.bv = fips512.K[t]!) :
    low.generic.sha512.round w k a b c d e f g h ⦃ r =>
      [r.2.bv, a.bv, b.bv, c.bv, r.1.bv, e.bv, f.bv, g.bv] =
        (List.range t').foldl (sha512Round W) H ⦄ := by
  rw [ht, List.range_succ, List.foldl_append, ← hs]
  unfold low.generic.sha512.round
  simp only [lift, bind_ok, WP.spec_ok, List.foldl_cons, List.foldl_nil, sha512Round]
  simp only [UScalar.bv_xor, UScalar.bv_and, core.num.U64.wrapping_add_bv_eq, bv_rotate_right64,
    ← hw, ← hk, fips512.bigSigma0, fips512.bigSigma1, ← ch_eq, ← maj_eq]
  simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, List.cons.injEq, and_true]
  constructor <;> ac_rfl


/-- The window `x` of the schedule `W` while the pass that writes words `i`
to `i + 15` is at slot `j`: slots before `j` hold this pass's words, the rest
the last pass's. -/
def Window (W : List (BitVec 64)) (i j : Nat) (x : Std.Array U64 16#usize) : Prop :=
  ∀ m < 16, x.val[m]!.bv = W[if m < j then i + m else i + m - 16]!

theorem window_read (W : List (BitVec 64)) (i j d : Nat) (x : Std.Array U64 16#usize)
    (hx : Window W i j x) (hj : j < 16) (hd : d < 16) :
    x.val[(j + d) % 16]!.bv = W[i + j + d - 16]! := by
  rw [hx _ (Nat.mod_lt _ (by omega))]
  congr 1
  by_cases h : j + d < 16
  · rw [Nat.mod_eq_of_lt h]; split <;> omega
  · rw [show (j + d) % 16 = j + d - 16 by omega]; split <;> omega

theorem window_set (W : List (BitVec 64)) (i : Nat) (j : Usize) (x : Std.Array U64 16#usize)
    (hx : Window W i j.val x) (hj : j.val < 16) (w : U64) (hw : w.bv = W[i + j.val]!) :
    Window W i (j.val + 1) (x.set j w) := by
  intro m hm
  rw [Array.set_val_eq]
  by_cases h : m = j.val
  · subst h
    rw [getElem!_pos _ _ (by simp; omega), List.getElem_set_self, hw]
    simp
  · rw [getElem!_pos _ _ (by simp; omega), List.getElem_set_ne (by omega),
      ← getElem!_pos _ _ (by simp; omega), hx m hm]
    congr 1
    split <;> split <;> omega

theorem window_get (W : List (BitVec 64)) (n j d k : Nat) (x : Std.Array U64 16#usize)
    (hx : Window W n j x) (hj : j < 16) (hd : d < 16) (hk : k = (j + d) % 16)
    (h : k < x.val.length) : (x.val[k]'h).bv = W[n + j + d - 16]! := by
  subst hk
  rw [← window_read W n j d x hx hj hd, getElem!_pos]

/-- The schedule step at slot `j` of the pass writing words `n` to `n + 15`. -/
theorem schedule_spec (M : List (BitVec 64)) (hM : M.length = 16) (n : Nat) (j : Usize)
    (x : Std.Array U64 16#usize) (hn : 16 ≤ n) (hj : j.val < 16) (hnj : n + j.val < 80)
    (hx : Window (fips512.schedule M) n j.val x) :
    low.generic.sha512.schedule x j ⦃ r =>
      r.1.bv = (fips512.schedule M)[n + j.val]! ∧
        Window (fips512.schedule M) n (j.val + 1) r.2 ⦄ := by
  unfold low.generic.sha512.schedule
  step*
  have hw : w.bv = (fips512.schedule M)[n + j.val]! := by
    have r1 := window_get _ n j.val 1 i1.val x hx hj (by omega) (by omega) (by simp; omega)
    have r14 := window_get _ n j.val 14 i3.val x hx hj (by omega) (by omega) (by simp; omega)
    have r9 := window_get _ n j.val 9 i16.val x hx hj (by omega) (by omega) (by simp; omega)
    have r0 := window_get _ n j.val 0 j.val x hx hj (by omega) (by omega) (by simp; omega)
    rw [← w1_post] at r1
    rw [← w14_post] at r14
    rw [← i17_post] at r9
    rw [← i12_post] at r0
    have e := schedule_succ M hM (n + j.val - 16) (by omega)
    rw [show n + j.val - 16 + 16 = n + j.val by omega,
      show n + j.val - 16 + 14 = n + j.val + 14 - 16 by omega,
      show n + j.val - 16 + 9 = n + j.val + 9 - 16 by omega,
      show n + j.val - 16 + 1 = n + j.val + 1 - 16 by omega,
      show n + j.val - 16 = n + j.val + 0 - 16 by omega] at e
    rw [e, ← r1, ← r14, ← r9, ← r0, w_post, i14_post, i13_post]
    simp only [core.num.U64.wrapping_add_bv_eq, s0_post1, s1_post1, i6_post1, i7_post1, i10_post1,
      i11_post1, i4_post, i5_post, i8_post, i9_post, bv_rotate_right64, fips512.smallSigma0,
      fips512.smallSigma1]
    simp
    ac_rfl
  refine ⟨hw, ?_⟩
  rw [x1_post]
  exact window_set _ n j x hx hj w hw

/-- FIPS 180-4 section 4.2.3's constants, as `sha512::K` holds them. -/
theorem K_spec : low.generic.sha512.K.val.map (·.bv) = fips512.K := by
  unfold low.generic.sha512.K; rfl

theorem K_at (n : Nat) (ht : n < 80) (k : U64) {h}
    (hk : k = low.generic.sha512.K.val[n]'h) : k.bv = fips512.K[n]! := by
  rw [← K_spec, hk, getElem!_pos _ n (by simp; omega), List.getElem_map]

theorem K_index (t : Usize) (n : Nat) (htn : t.val = n) (ht : n < 80) (k : U64)
    (hk : k = low.generic.sha512.K.val[t.val]'(by simp; omega)) : k.bv = fips512.K[n]! := by
  subst htn
  rw [← K_spec, hk, getElem!_pos _ t.val (by simp; omega), List.getElem_map]


theorem window_next (W : List (BitVec 64)) (n : Nat) (x : Std.Array U64 16#usize)
    (hx : Window W n 16 x) : Window W (n + 16) 0 x := by
  intro m hm; rw [hx m hm]; congr 1; split <;> split <;> omega

/-- What the loop over rounds 16 to 79 keeps: the window holds the last
pass's words and the working variables are the state after `i` rounds, before round `i`. -/
def RoundsInv (M H : List (BitVec 64))
    (p : Std.Array U64 16#usize × U64 × U64 × U64 × U64 × U64 × U64 × U64 × U64 × Usize) : Prop :=
  match p with
  | (x, a, b, c, d, e, f, g, h, i) =>
    16 ≤ i.val ∧ i.val ≤ 80 ∧ i.val % 16 = 0 ∧ Window (fips512.schedule M) i.val 0 x ∧
      [a.bv, b.bv, c.bv, d.bv, e.bv, f.bv, g.bv, h.bv] =
        (List.range i.val).foldl (sha512Round (fips512.schedule M)) H

/-- Rounds `i` to 79. -/
theorem rounds_spec (M : List (BitVec 64)) (hM : M.length = 16) (H : List (BitVec 64))
    (x : Std.Array U64 16#usize) (a b c d e f g h : U64) (i : Usize)
    (hinv : RoundsInv M H (x, a, b, c, d, e, f, g, h, i)) :
    low.generic.sha512.sha512_compress_blocks_loop0_loop1 x a b c d e f g h i ⦃ r =>
      [r.1.bv, r.2.1.bv, r.2.2.1.bv, r.2.2.2.1.bv, r.2.2.2.2.1.bv, r.2.2.2.2.2.1.bv,
        r.2.2.2.2.2.2.1.bv, r.2.2.2.2.2.2.2.bv] =
        (List.range 80).foldl (sha512Round (fips512.schedule M)) H ⦄ := by
  unfold low.generic.sha512.sha512_compress_blocks_loop0_loop1
  apply loop.spec_decr_nat (fun p => 80 - p.2.2.2.2.2.2.2.2.2.val) (RoundsInv M H)
  · rintro ⟨x, a, b, c, d, e, f, g, h, i⟩ ⟨hi, hi80, hi16, hx, hs⟩
    unfold low.generic.sha512.sha512_compress_blocks_loop0_loop1.body
    dsimp only
    split
    · rename_i hlt
      have hi64 : i.val ≤ 64 := by scalar_tac
      have hmax : i.val + 16 ≤ Usize.max := by scalar_tac
      step with schedule_spec M hM i.val 0#usize x (by omega) (by simp) (by simp; omega) (by simpa using hx) as ⟨w0, x1, hw0, hx1⟩
      step as ⟨t0, ht0⟩
      step with Array.index_usize_spec low.generic.sha512.K t0 (by simp; omega) as ⟨k0, hk0⟩
      step with round_spec (fips512.schedule M) H (i.val + 0) (i.val + 1) (by omega) w0 k0 a b c d e f g h (by simpa using hs)
        (by simpa using hw0) (K_index t0 _ (by simp [ht0]) (by omega) k0 hk0) as ⟨d1, h1, hs1⟩
      step with schedule_spec M hM i.val 1#usize x1 (by omega) (by simp) (by simp; omega) (by simpa using hx1) as ⟨w1, x2, hw1, hx2⟩
      step as ⟨t1, ht1⟩
      step with Array.index_usize_spec low.generic.sha512.K t1 (by simp; omega) as ⟨k1, hk1⟩
      step with round_spec (fips512.schedule M) H (i.val + 1) (i.val + 2) (by omega) w1 k1 h1 a b c d1 e f g hs1
        (by simpa using hw1) (K_index t1 _ (by simp [ht1]) (by omega) k1 hk1) as ⟨c1, g1, hs2⟩
      step with schedule_spec M hM i.val 2#usize x2 (by omega) (by simp) (by simp; omega) (by simpa using hx2) as ⟨w2, x3, hw2, hx3⟩
      step as ⟨t2, ht2⟩
      step with Array.index_usize_spec low.generic.sha512.K t2 (by simp; omega) as ⟨k2, hk2⟩
      step with round_spec (fips512.schedule M) H (i.val + 2) (i.val + 3) (by omega) w2 k2 g1 h1 a b c1 d1 e f hs2
        (by simpa using hw2) (K_index t2 _ (by simp [ht2]) (by omega) k2 hk2) as ⟨b1, f1, hs3⟩
      step with schedule_spec M hM i.val 3#usize x3 (by omega) (by simp) (by simp; omega) (by simpa using hx3) as ⟨w3, x4, hw3, hx4⟩
      step as ⟨t3, ht3⟩
      step with Array.index_usize_spec low.generic.sha512.K t3 (by simp; omega) as ⟨k3, hk3⟩
      step with round_spec (fips512.schedule M) H (i.val + 3) (i.val + 4) (by omega) w3 k3 f1 g1 h1 a b1 c1 d1 e hs3
        (by simpa using hw3) (K_index t3 _ (by simp [ht3]) (by omega) k3 hk3) as ⟨a1, e1, hs4⟩
      step with schedule_spec M hM i.val 4#usize x4 (by omega) (by simp) (by simp; omega) (by simpa using hx4) as ⟨w4, x5, hw4, hx5⟩
      step as ⟨t4, ht4⟩
      step with Array.index_usize_spec low.generic.sha512.K t4 (by simp; omega) as ⟨k4, hk4⟩
      step with round_spec (fips512.schedule M) H (i.val + 4) (i.val + 5) (by omega) w4 k4 e1 f1 g1 h1 a1 b1 c1 d1 hs4
        (by simpa using hw4) (K_index t4 _ (by simp [ht4]) (by omega) k4 hk4) as ⟨h2, d2, hs5⟩
      step with schedule_spec M hM i.val 5#usize x5 (by omega) (by simp) (by simp; omega) (by simpa using hx5) as ⟨w5, x6, hw5, hx6⟩
      step as ⟨t5, ht5⟩
      step with Array.index_usize_spec low.generic.sha512.K t5 (by simp; omega) as ⟨k5, hk5⟩
      step with round_spec (fips512.schedule M) H (i.val + 5) (i.val + 6) (by omega) w5 k5 d2 e1 f1 g1 h2 a1 b1 c1 hs5
        (by simpa using hw5) (K_index t5 _ (by simp [ht5]) (by omega) k5 hk5) as ⟨g2, c2, hs6⟩
      step with schedule_spec M hM i.val 6#usize x6 (by omega) (by simp) (by simp; omega) (by simpa using hx6) as ⟨w6, x7, hw6, hx7⟩
      step as ⟨t6, ht6⟩
      step with Array.index_usize_spec low.generic.sha512.K t6 (by simp; omega) as ⟨k6, hk6⟩
      step with round_spec (fips512.schedule M) H (i.val + 6) (i.val + 7) (by omega) w6 k6 c2 d2 e1 f1 g2 h2 a1 b1 hs6
        (by simpa using hw6) (K_index t6 _ (by simp [ht6]) (by omega) k6 hk6) as ⟨f2, b2, hs7⟩
      step with schedule_spec M hM i.val 7#usize x7 (by omega) (by simp) (by simp; omega) (by simpa using hx7) as ⟨w7, x8, hw7, hx8⟩
      step as ⟨t7, ht7⟩
      step with Array.index_usize_spec low.generic.sha512.K t7 (by simp; omega) as ⟨k7, hk7⟩
      step with round_spec (fips512.schedule M) H (i.val + 7) (i.val + 8) (by omega) w7 k7 b2 c2 d2 e1 f2 g2 h2 a1 hs7
        (by simpa using hw7) (K_index t7 _ (by simp [ht7]) (by omega) k7 hk7) as ⟨e2, a2, hs8⟩
      step with schedule_spec M hM i.val 8#usize x8 (by omega) (by simp) (by simp; omega) (by simpa using hx8) as ⟨w8, x9, hw8, hx9⟩
      step as ⟨t8, ht8⟩
      step with Array.index_usize_spec low.generic.sha512.K t8 (by simp; omega) as ⟨k8, hk8⟩
      step with round_spec (fips512.schedule M) H (i.val + 8) (i.val + 9) (by omega) w8 k8 a2 b2 c2 d2 e2 f2 g2 h2 hs8
        (by simpa using hw8) (K_index t8 _ (by simp [ht8]) (by omega) k8 hk8) as ⟨d3, h3, hs9⟩
      step with schedule_spec M hM i.val 9#usize x9 (by omega) (by simp) (by simp; omega) (by simpa using hx9) as ⟨w9, x10, hw9, hx10⟩
      step as ⟨t9, ht9⟩
      step with Array.index_usize_spec low.generic.sha512.K t9 (by simp; omega) as ⟨k9, hk9⟩
      step with round_spec (fips512.schedule M) H (i.val + 9) (i.val + 10) (by omega) w9 k9 h3 a2 b2 c2 d3 e2 f2 g2 hs9
        (by simpa using hw9) (K_index t9 _ (by simp [ht9]) (by omega) k9 hk9) as ⟨c3, g3, hs10⟩
      step with schedule_spec M hM i.val 10#usize x10 (by omega) (by simp) (by simp; omega) (by simpa using hx10) as ⟨w10, x11, hw10, hx11⟩
      step as ⟨t10, ht10⟩
      step with Array.index_usize_spec low.generic.sha512.K t10 (by simp; omega) as ⟨k10, hk10⟩
      step with round_spec (fips512.schedule M) H (i.val + 10) (i.val + 11) (by omega) w10 k10 g3 h3 a2 b2 c3 d3 e2 f2 hs10
        (by simpa using hw10) (K_index t10 _ (by simp [ht10]) (by omega) k10 hk10) as ⟨b3, f3, hs11⟩
      step with schedule_spec M hM i.val 11#usize x11 (by omega) (by simp) (by simp; omega) (by simpa using hx11) as ⟨w11, x12, hw11, hx12⟩
      step as ⟨t11, ht11⟩
      step with Array.index_usize_spec low.generic.sha512.K t11 (by simp; omega) as ⟨k11, hk11⟩
      step with round_spec (fips512.schedule M) H (i.val + 11) (i.val + 12) (by omega) w11 k11 f3 g3 h3 a2 b3 c3 d3 e2 hs11
        (by simpa using hw11) (K_index t11 _ (by simp [ht11]) (by omega) k11 hk11) as ⟨a3, e3, hs12⟩
      step with schedule_spec M hM i.val 12#usize x12 (by omega) (by simp) (by simp; omega) (by simpa using hx12) as ⟨w12, x13, hw12, hx13⟩
      step as ⟨t12, ht12⟩
      step with Array.index_usize_spec low.generic.sha512.K t12 (by simp; omega) as ⟨k12, hk12⟩
      step with round_spec (fips512.schedule M) H (i.val + 12) (i.val + 13) (by omega) w12 k12 e3 f3 g3 h3 a3 b3 c3 d3 hs12
        (by simpa using hw12) (K_index t12 _ (by simp [ht12]) (by omega) k12 hk12) as ⟨h4, d4, hs13⟩
      step with schedule_spec M hM i.val 13#usize x13 (by omega) (by simp) (by simp; omega) (by simpa using hx13) as ⟨w13, x14, hw13, hx14⟩
      step as ⟨t13, ht13⟩
      step with Array.index_usize_spec low.generic.sha512.K t13 (by simp; omega) as ⟨k13, hk13⟩
      step with round_spec (fips512.schedule M) H (i.val + 13) (i.val + 14) (by omega) w13 k13 d4 e3 f3 g3 h4 a3 b3 c3 hs13
        (by simpa using hw13) (K_index t13 _ (by simp [ht13]) (by omega) k13 hk13) as ⟨g4, c4, hs14⟩
      step with schedule_spec M hM i.val 14#usize x14 (by omega) (by simp) (by simp; omega) (by simpa using hx14) as ⟨w14, x15, hw14, hx15⟩
      step as ⟨t14, ht14⟩
      step with Array.index_usize_spec low.generic.sha512.K t14 (by simp; omega) as ⟨k14, hk14⟩
      step with round_spec (fips512.schedule M) H (i.val + 14) (i.val + 15) (by omega) w14 k14 c4 d4 e3 f3 g4 h4 a3 b3 hs14
        (by simpa using hw14) (K_index t14 _ (by simp [ht14]) (by omega) k14 hk14) as ⟨f4, b4, hs15⟩
      step with schedule_spec M hM i.val 15#usize x15 (by omega) (by simp) (by simp; omega) (by simpa using hx15) as ⟨w15, x16, hw15, hx16⟩
      step as ⟨t15, ht15⟩
      step with Array.index_usize_spec low.generic.sha512.K t15 (by simp; omega) as ⟨k15, hk15⟩
      step with round_spec (fips512.schedule M) H (i.val + 15) (i.val + 16) (by omega) w15 k15 b4 c4 d4 e3 f4 g4 h4 a3 hs15
        (by simpa using hw15) (K_index t15 _ (by simp [ht15]) (by omega) k15 hk15) as ⟨e4, a4, hs16⟩
      step as ⟨i', hi'⟩
      refine ⟨⟨by omega, by omega, by omega, ?_, ?_⟩, by omega⟩
      · rw [hi']; exact window_next _ _ _ (by simpa using hx16)
      · rw [hi']; exact hs16
    · rename_i hlt
      simp only [WP.spec_ok]
      rw [show i.val = 80 by scalar_tac] at hs
      exact hs
  · exact hinv

theorem first_word (M : List (BitVec 64)) (hM : M.length = 16) (x : Std.Array U64 16#usize)
    (hx : ∀ m < 16, x.val[m]!.bv = M[m]!) (j : Nat) (hj : j < 16)
    (w : U64) {h} (hw : w = x.val[j]'h) : w.bv = (fips512.schedule M)[j]! := by
  rw [schedule_lt M hM _ hj, ← hx _ hj, hw, getElem!_pos]


/-- Loads the block's words `iter.start` to 15 into `x`, which holds the earlier ones. -/
theorem load_spec (block : Slice U8) (hb : block.length = 128) (iter : core.ops.range.Range Usize)
    (x : Std.Array U64 16#usize) (hs : iter.start.val ≤ 16) (he : iter.end.val = 16)
    (hx : ∀ m < iter.start.val, x.val[m]!.bv = ((blockWords block.val).map (·.bv))[m]!) :
    low.generic.sha512.sha512_compress_blocks_loop0_loop0 iter block x ⦃ r =>
      ∀ m < 16, r.val[m]!.bv = ((blockWords block.val).map (·.bv))[m]! ⦄ := by
  unfold low.generic.sha512.sha512_compress_blocks_loop0_loop0
  apply loop.spec_decr_nat (fun p => 16 - p.1.start.val)
    (fun p => p.1.start.val ≤ 16 ∧ p.1.end.val = 16 ∧
      ∀ m < p.1.start.val, p.2.val[m]!.bv = ((blockWords block.val).map (·.bv))[m]!)
  · rintro ⟨it, y⟩ ⟨hs, he, hy⟩
    simp only at hs he hy ⊢
    unfold low.generic.sha512.sha512_compress_blocks_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step*
      refine ⟨by omega, by rw [hen]; exact he, ?_, by omega⟩
      intro m hm
      rw [a_post, Array.set_val_eq]
      by_cases h : m = it.start.val
      · subst h
        have hbl : block.val.length = 128 := by simpa [Slice.length] using hb
        have g : ∀ (n : Nat) (u : U8) (k : Usize) (hk : k.val < block.val.length)
            (hu : u = block.val[k.val]) (hn : k.val = n), block.val[n]! = u := by
          intro n u k hk hu hn; subst hn; rw [hu, getElem!_pos]
        have hw : ((blockWords block.val).map (·.bv))[it.start.val]! =
            (beWord ((block.val.drop (8 * it.start.val)).take 8)).bv := by
          rw [getElem!_pos _ _ (by simp [blockWords]; omega), List.getElem_map]
          simp only [blockWords, List.getElem_map, List.getElem_range]
        rw [getElem!_pos _ _ (by simp; omega), List.getElem_set_self, i16_post, hw, beWord,
          drop_take8 _ _ (by omega),
          g _ i1 i (by omega) i1_post (by omega), g _ i3 i2 (by omega) i3_post (by omega),
          g _ i5 i4 (by omega) i5_post (by omega), g _ i7 i6 (by omega) i7_post (by omega),
          g _ i9 i8 (by omega) i9_post (by omega), g _ i11 i10 (by omega) i11_post (by omega),
          g _ i13 i12 (by omega) i13_post (by omega), g _ i15 i14 (by omega) i15_post (by omega),
          cast_setWidth]
        rfl
      · rw [getElem!_pos _ _ (by simp; omega), List.getElem_set_ne (by omega),
          ← getElem!_pos _ _ (by simp; omega)]
        exact hy m (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro m hm; exact hy m (by omega)
  · exact ⟨hs, he, hx⟩

set_option maxHeartbeats 1000000 in
/-- One block at `off`, given the blocks before it compressed into `state`. -/
theorem block_spec (H0 : List U64) (blocks : Slice U8) (hb : blocks.length % 128 = 0)
    (state : Std.Array U64 8#usize) (s0 s1 s2 s3 s4 s5 s6 s7 : U64)
    (hst : state.val = [s0, s1, s2, s3, s4, s5, s6, s7]) (off : Usize) (hoff : off.val % 128 = 0)
    (hlt : off.val < blocks.length)
    (hs : [s0, s1, s2, s3, s4, s5, s6, s7] = compress H0 (blocks.val.take off.val)) :
    low.generic.sha512.sha512_compress_blocks_loop0.body blocks state off
      ⦃ r => ∃ st off', r = .cont (st, off') ∧ off'.val = off.val + 128 ∧
        st.val = compress H0 (blocks.val.take off'.val) ⦄ := by
  unfold low.generic.sha512.sha512_compress_blocks_loop0.body
  dsimp only
  split
  swap
  · rename_i h; exfalso; simp [Slice.len] at h; scalar_tac
  step as ⟨off', hoff'⟩
  step with core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec as ⟨block, hblk, hblen⟩
  have hbl : block.length = 128 := by rw [hblen]; scalar_tac
  step with load_spec block hbl { start := 0#usize, «end» := 16#usize } (Array.repeat 16#usize 0#u64)
    (by simp) (by simp) (by simp) as ⟨x1, hx1⟩
  set M := (blockWords block.val).map (·.bv) with hM_def
  have hM : M.length = 16 := by simp [M, blockWords_length]
  set W := fips512.schedule M
  set H : List (BitVec 64) := [s0.bv, s1.bv, s2.bv, s3.bv, s4.bv, s5.bv, s6.bv, s7.bv]
  step as ⟨a, ra⟩
  step as ⟨b, rb⟩
  step as ⟨c, rc⟩
  step as ⟨d, rd⟩
  step as ⟨e, re⟩
  step as ⟨f, rf⟩
  step as ⟨g, rg⟩
  step as ⟨h, rh⟩
  simp only [hst, List.getElem_cons_zero, List.getElem_cons_succ] at ra rb rc rd re rf rg rh
  subst ra rb rc rd re rf rg rh
  step as ⟨w0, hw0⟩
  step as ⟨k0, hk0⟩
  step with round_spec W H 0 1 rfl w0 k0 a b c d e f g h rfl
    (first_word M hM x1 hx1 0 (by omega) w0 hw0) (K_at 0 (by omega) k0 hk0) as ⟨d1, h1, hs1⟩
  step as ⟨w1, hw1⟩
  step as ⟨k1, hk1⟩
  step with round_spec W H 1 2 rfl w1 k1 h1 a b c d1 e f g hs1
    (first_word M hM x1 hx1 1 (by omega) w1 hw1) (K_at 1 (by omega) k1 hk1) as ⟨c1, g1, hs2⟩
  step as ⟨w2, hw2⟩
  step as ⟨k2, hk2⟩
  step with round_spec W H 2 3 rfl w2 k2 g1 h1 a b c1 d1 e f hs2
    (first_word M hM x1 hx1 2 (by omega) w2 hw2) (K_at 2 (by omega) k2 hk2) as ⟨b1, f1, hs3⟩
  step as ⟨w3, hw3⟩
  step as ⟨k3, hk3⟩
  step with round_spec W H 3 4 rfl w3 k3 f1 g1 h1 a b1 c1 d1 e hs3
    (first_word M hM x1 hx1 3 (by omega) w3 hw3) (K_at 3 (by omega) k3 hk3) as ⟨a1, e1, hs4⟩
  step as ⟨w4, hw4⟩
  step as ⟨k4, hk4⟩
  step with round_spec W H 4 5 rfl w4 k4 e1 f1 g1 h1 a1 b1 c1 d1 hs4
    (first_word M hM x1 hx1 4 (by omega) w4 hw4) (K_at 4 (by omega) k4 hk4) as ⟨h2, d2, hs5⟩
  step as ⟨w5, hw5⟩
  step as ⟨k5, hk5⟩
  step with round_spec W H 5 6 rfl w5 k5 d2 e1 f1 g1 h2 a1 b1 c1 hs5
    (first_word M hM x1 hx1 5 (by omega) w5 hw5) (K_at 5 (by omega) k5 hk5) as ⟨g2, c2, hs6⟩
  step as ⟨w6, hw6⟩
  step as ⟨k6, hk6⟩
  step with round_spec W H 6 7 rfl w6 k6 c2 d2 e1 f1 g2 h2 a1 b1 hs6
    (first_word M hM x1 hx1 6 (by omega) w6 hw6) (K_at 6 (by omega) k6 hk6) as ⟨f2, b2, hs7⟩
  step as ⟨w7, hw7⟩
  step as ⟨k7, hk7⟩
  step with round_spec W H 7 8 rfl w7 k7 b2 c2 d2 e1 f2 g2 h2 a1 hs7
    (first_word M hM x1 hx1 7 (by omega) w7 hw7) (K_at 7 (by omega) k7 hk7) as ⟨e2, a2, hs8⟩
  step as ⟨w8, hw8⟩
  step as ⟨k8, hk8⟩
  step with round_spec W H 8 9 rfl w8 k8 a2 b2 c2 d2 e2 f2 g2 h2 hs8
    (first_word M hM x1 hx1 8 (by omega) w8 hw8) (K_at 8 (by omega) k8 hk8) as ⟨d3, h3, hs9⟩
  step as ⟨w9, hw9⟩
  step as ⟨k9, hk9⟩
  step with round_spec W H 9 10 rfl w9 k9 h3 a2 b2 c2 d3 e2 f2 g2 hs9
    (first_word M hM x1 hx1 9 (by omega) w9 hw9) (K_at 9 (by omega) k9 hk9) as ⟨c3, g3, hs10⟩
  step as ⟨w10, hw10⟩
  step as ⟨k10, hk10⟩
  step with round_spec W H 10 11 rfl w10 k10 g3 h3 a2 b2 c3 d3 e2 f2 hs10
    (first_word M hM x1 hx1 10 (by omega) w10 hw10) (K_at 10 (by omega) k10 hk10) as ⟨b3, f3, hs11⟩
  step as ⟨w11, hw11⟩
  step as ⟨k11, hk11⟩
  step with round_spec W H 11 12 rfl w11 k11 f3 g3 h3 a2 b3 c3 d3 e2 hs11
    (first_word M hM x1 hx1 11 (by omega) w11 hw11) (K_at 11 (by omega) k11 hk11) as ⟨a3, e3, hs12⟩
  step as ⟨w12, hw12⟩
  step as ⟨k12, hk12⟩
  step with round_spec W H 12 13 rfl w12 k12 e3 f3 g3 h3 a3 b3 c3 d3 hs12
    (first_word M hM x1 hx1 12 (by omega) w12 hw12) (K_at 12 (by omega) k12 hk12) as ⟨h4, d4, hs13⟩
  step as ⟨w13, hw13⟩
  step as ⟨k13, hk13⟩
  step with round_spec W H 13 14 rfl w13 k13 d4 e3 f3 g3 h4 a3 b3 c3 hs13
    (first_word M hM x1 hx1 13 (by omega) w13 hw13) (K_at 13 (by omega) k13 hk13) as ⟨g4, c4, hs14⟩
  step as ⟨w14, hw14⟩
  step as ⟨k14, hk14⟩
  step with round_spec W H 14 15 rfl w14 k14 c4 d4 e3 f3 g4 h4 a3 b3 hs14
    (first_word M hM x1 hx1 14 (by omega) w14 hw14) (K_at 14 (by omega) k14 hk14) as ⟨f4, b4, hs15⟩
  step as ⟨w15, hw15⟩
  step as ⟨k15, hk15⟩
  step with round_spec W H 15 16 rfl w15 k15 b4 c4 d4 e3 f4 g4 h4 a3 hs15
    (first_word M hM x1 hx1 15 (by omega) w15 hw15) (K_at 15 (by omega) k15 hk15) as ⟨e4, a4, hs16⟩
  have hx16 : Window W 16 0 x1 := by
    intro m hm
    simp only [Nat.not_lt_zero, ↓reduceIte]
    rw [show 16 + m - 16 = m by omega, schedule_lt M hM m hm, hx1 m hm]
  step with rounds_spec M hM H x1 a4 b4 c4 d4 e4 f4 g4 h4 16#usize
    ⟨by simp, by simp, by simp, by simpa using hx16, by simpa using hs16⟩
    as ⟨a5, b5, c5, d5, e5, f5, g5, h5, hr⟩
  step*
  refine ⟨a6, off1, rfl, off1_post, ?_⟩
  have ha6 : a6.val.map (·.bv) = [a.bv + a5.bv, b.bv + b5.bv, c.bv + c5.bv, d.bv + d5.bv,
      e.bv + e5.bv, f.bv + f5.bv, g.bv + g5.bv, h.bv + h5.bv] := by
    simp only [a6_post, state1_post, state2_post, state3_post, state4_post, state5_post, state6_post, state7_post, i34_post, i35_post, i36_post, i37_post, i38_post, i39_post, i40_post, i41_post, i42_post, i43_post, i44_post, i45_post, i46_post, i47_post, i48_post, i49_post, Array.set_val_eq, hst]
    simp
  have hblock : block.val = (blocks.val.drop off.val).take 128 := by
    rw [hblk, List.slice, hoff']; congr 1; omega
  have htake : (blocks.val.take off.val).length % 128 = 0 := by
    rw [List.length_take]; simp only [Slice.length] at hlt; rw [Nat.min_eq_left (by omega)]
    exact hoff
  have hbl' : block.val.length = 128 := by simpa [Slice.length] using hbl
  rw [off1_post, List.take_add, ← hblock, compress_append _ _ _ htake, ← hs,
    compress_block _ _ (by omega), List.drop_of_length_le (by omega), compress_nil,
    List.take_of_length_le (by omega), processBlock]
  have hinj : Function.Injective (List.map (fun x : U64 => x.bv)) :=
    List.map_injective_iff.mpr (fun x y h => (UScalar.eq_equiv_bv_eq x y).mpr h)
  apply hinj
  rw [ha6, List.map_map, compressBlock_eq, show [a, b, c, d, e, f, g, h].map (·.bv) = H by rfl,
    ← hr]
  simp [H, BitVec.add_comm]
end rind.portable.sha512_blocks

namespace rind.portable
open sha512_blocks rind.sha512_rounds

/-- `generic::sha512`'s block function computes FIPS 180-4's compression of
each whole block in turn. -/
theorem generic_sha512_compress_blocks_spec (state : Std.Array U64 8#usize) (blocks : Slice U8)
    (hl : blocks.length % 128 = 0) :
    low.generic.sha512.sha512_compress_blocks state blocks ⦃ r =>
      r.val = compress state.val blocks.val ⦄ := by
  unfold low.generic.sha512.sha512_compress_blocks
  step*
  unfold low.generic.sha512.sha512_compress_blocks_loop0
  apply loop.spec_decr_nat (fun p => blocks.length - p.2.val)
    (fun p => p.2.val ≤ blocks.length ∧ p.2.val % 128 = 0 ∧
      p.1.val = compress state.val (blocks.val.take p.2.val))
  · rintro ⟨st, off⟩ ⟨hle, hoff, hs⟩
    simp only at hle hoff hs ⊢
    by_cases hlt : off.val < blocks.length
    · obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, hst⟩ := arr8 st
      apply WP.spec_mono (block_spec state.val blocks hl st s0 s1 s2 s3 s4 s5 s6 s7 hst off hoff hlt
        (by rw [← hst]; exact hs))
      rintro r ⟨st', off', rfl, ho, hw⟩
      have hlen : off.val + 128 ≤ blocks.length := by
        simp only [Slice.length] at hlt hl hoff ⊢; omega
      dsimp only
      exact ⟨⟨by omega, by omega, hw⟩, by omega⟩
    · unfold low.generic.sha512.sha512_compress_blocks_loop0.body
      dsimp only
      split
      · rename_i h; exfalso; simp [Slice.len] at h; scalar_tac
      simp only [WP.spec_ok]
      rw [hs, List.take_of_length_le (by simp only [Slice.length] at hlt; omega)]
  · refine ⟨by simp, by simp, ?_⟩
    simp

end rind.portable
