import Rind.Mcu.Blockwise
import Rind.Sha2Rounds
open Aeneas Aeneas.Std Result rind.spec

/-!
# ESP-IDF Xtensa's SHA-256 block function

`low/portable/sha256_iram.rs` computes FIPS 180-4's compression,
`sha256.compress`, of each whole block in turn:
`iram_sha256_compress_blocks_spec`. The translation reads its Rust in place of
its Xtensa `asm!`, the rotates and the block load, and
`Rind.Mcu.Sha256IramModel` models its cursors and window.

Its body loads the block's sixteen words through sixteen rounds, writing each
into the window, then runs a loop of three passes of sixteen rounds, each
round's schedule word written over the slot of the one sixteen before it. Every
round is a call to `round`, which returns the working variables rotated, so
`round_spec` takes the rounds folded so far and gives one more; `Last16` says
the window holds the sixteen schedule words before the round, and every slot
read was written, as `Window::get` requires.
-/

namespace rind.mcu.sha256_iram
open rind.sha256_rounds

theorem iram_ch_eq (e f g : BitVec 32) : g ^^^ (e &&& (f ^^^ g)) = ch e f g := by
  unfold ch; ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases e[i] <;> cases f[i] <;> cases g[i] <;> rfl

theorem iram_maj_eq (a b c : BitVec 32) : (a &&& b) ^^^ (c &&& (a ^^^ b)) = maj a b c := by
  unfold maj; ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

/-- One round, given the working variables after rounds `0` to `t - 1`. -/
theorem round_spec (W H : List (BitVec 32)) (t t' : Nat) (ht : t' = t + 1) (w k a b c d e f g h : U32)
    (hs : [a.bv, b.bv, c.bv, d.bv, e.bv, f.bv, g.bv, h.bv] = (List.range t).foldl (sha256Round W) H)
    (hw : w.bv = W[t]!) (hk : k.bv = sha256.K[t]!) :
    low.portable.sha.iram.round w k a b c d e f g h ⦃ r =>
      [r.1.bv, r.2.1.bv, r.2.2.1.bv, r.2.2.2.1.bv, r.2.2.2.2.1.bv, r.2.2.2.2.2.1.bv,
        r.2.2.2.2.2.2.1.bv, r.2.2.2.2.2.2.2.bv] =
        (List.range t').foldl (sha256Round W) H ⦄ := by
  rw [ht, List.range_succ, List.foldl_append, ← hs]
  unfold low.portable.sha.iram.round low.portable.sha.iram.bsig0 low.portable.sha.iram.bsig1
    low.portable.sha.iram.ch low.portable.sha.iram.maj low.portable.sha.iram.rotr
  simp only [lift, bind_ok, WP.spec_ok, List.foldl_cons, List.foldl_nil, sha256Round]
  simp only [UScalar.bv_xor, UScalar.bv_and, core.num.U32.wrapping_add_bv_eq, bv_rotate_right32,
    ← hw, ← hk, sha256.bigSigma0, sha256.bigSigma1]
  simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, ← iram_ch_eq, ← iram_maj_eq,
    List.cons.injEq, and_true, true_and]
  constructor <;> ac_rfl

/-- The window `x` before round `t`: each of the up to sixteen schedule words
before `t` written in its slot, `s mod 16`. -/
def Last16 (W : List (BitVec 32)) (t : Nat) (x : Std.Array (Option U32) 16#usize) : Prop :=
  ∀ s < t, t ≤ s + 16 → ∃ u : U32, x.val[s % 16]! = some u ∧ u.bv = W[s]!

theorem last16_zero (W : List (BitVec 32)) (x : Std.Array (Option U32) 16#usize) : Last16 W 0 x :=
  fun _ hs => absurd hs (Nat.not_lt_zero _)

/-- Round `t`'s word, written into slot `t mod 16`, keeps `Last16`. -/
theorem last16_set (W : List (BitVec 32)) (t : Nat) (x : Std.Array (Option U32) 16#usize)
    (hx : Last16 W t x) (i : Usize) (hi : i.val = t % 16) (w : U32) (hw : w.bv = W[t]!) :
    Last16 W (t + 1) (x.set i (some w)) := by
  intro s hs hts
  rw [Array.set_val_eq]
  by_cases h : s = t
  · subst h
    refine ⟨w, ?_, hw⟩
    rw [← hi, getElem!_pos _ _ (by simp; omega), List.getElem_set_self]
  · rw [getElem!_pos _ _ (by simp; omega), List.getElem_set_ne (by omega),
      ← getElem!_pos _ _ (by simp; omega)]
    exact hx s (by omega) (by omega)

theorem and15 (x : Usize) : (x &&& 15#usize).val = x.val % 16 := by
  rw [UScalar.val_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.val 4

@[step]
theorem window_set_spec (x : low.portable.sha.iram.Window) (i : Usize) (hi : i.val < 16) (w : U32) :
    low.portable.sha.iram.Window.set x i w ⦃ r => r = Std.Array.set x i (some w) ⦄ := by
  unfold low.portable.sha.iram.Window.set
  step*

/-- A word of the window, `d` rounds back, which was written. -/
theorem window_get_spec (W : List (BitVec 32)) (t d : Nat) (x : Std.Array (Option U32) 16#usize)
    (hx : Last16 W t x) (hd : 0 < d) (hd16 : d ≤ 16) (htd : d ≤ t) (i : Usize)
    (hi : i.val = (t - d) % 16) :
    low.portable.sha.iram.Window.get x i ⦃ u => u.bv = W[t - d]! ⦄ := by
  obtain ⟨u, hu, hub⟩ := hx (t - d) (by omega) (by omega)
  unfold low.portable.sha.iram.Window.get
  have hil : i.val < 16 := by omega
  step with Array.index_usize_spec x i (by simp; omega) as ⟨o, ho⟩
  rw [← hi, getElem!_pos _ _ (by simp; omega), ← ho] at hu
  simp [hu, hub]

theorem ssig0_spec (x : U32) :
    low.portable.sha.iram.ssig0 x ⦃ r => r.bv = sha256.smallSigma0 x.bv ⦄ := by
  unfold low.portable.sha.iram.ssig0 low.portable.sha.iram.rotr
  step*
  simp_all [sha256.smallSigma0, bv_rotate_right32]

theorem ssig1_spec (x : U32) :
    low.portable.sha.iram.ssig1 x ⦃ r => r.bv = sha256.smallSigma1 x.bv ⦄ := by
  unfold low.portable.sha.iram.ssig1 low.portable.sha.iram.rotr
  step*
  simp_all [sha256.smallSigma1, bv_rotate_right32]

/-- The schedule step at slot `t mod 16`, rounds 16 to 63. -/
theorem schedule_spec (M : List (BitVec 32)) (hM : M.length = 16) (t : Nat) (SLOT : Usize)
    (x : Std.Array (Option U32) 16#usize) (ht : 16 ≤ t) (ht64 : t < 64) (hs : SLOT.val = t % 16)
    (hx : Last16 (sha256.schedule M) t x) :
    low.portable.sha.iram.schedule SLOT x ⦃ r =>
      r.1.bv = (sha256.schedule M)[t]! ∧ Last16 (sha256.schedule M) (t + 1) r.2 ⦄ := by
  unfold low.portable.sha.iram.schedule
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step with window_get_spec _ t 2 x hx (by omega) (by omega) (by omega) i1
    (by rw [hi1, and15, hi, hs]; omega) as ⟨w14, hw14⟩
  step with ssig1_spec as ⟨s1, hs1⟩
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  step with window_get_spec _ t 7 x hx (by omega) (by omega) (by omega) i5
    (by rw [hi5, and15, hi4, hs]; omega) as ⟨w9, hw9⟩
  step as ⟨i7, hi7⟩
  step as ⟨i8, hi8⟩
  step as ⟨i9, hi9⟩
  step with window_get_spec _ t 15 x hx (by omega) (by omega) (by omega) i9
    (by rw [hi9, and15, hi8, hs]; omega) as ⟨w1, hw1⟩
  step with ssig0_spec as ⟨s0, hs0⟩
  step as ⟨i12, hi12⟩
  step with window_get_spec _ t 16 x hx (by omega) (by omega) (by omega) SLOT
    (by rw [hs]; omega) as ⟨w0, hw0⟩
  step as ⟨w, hw⟩
  have hwt : w.bv = (sha256.schedule M)[t]! := by
    have e := schedule_succ M hM (t - 16) (by omega)
    rw [show t - 16 + 16 = t by omega, show t - 16 + 14 = t - 2 by omega,
      show t - 16 + 9 = t - 7 by omega, show t - 16 + 1 = t - 15 by omega] at e
    rw [e, hw, hi12, hi7]
    simp only [core.num.U32.wrapping_add_bv_eq, hs0, hs1, hw14, hw9, hw1, hw0]
  step with window_set_spec x SLOT (by omega) w as ⟨x1, hx1⟩
  refine ⟨hwt, ?_⟩
  rw [hx1]
  exact last16_set _ t x hx SLOT hs w hwt

/-- FIPS 180-4 section 4.2.2's constants, as `sha256_k::K` holds them. -/
theorem K_spec : low.generic.sha256_k.K.val.map (·.bv) = sha256.K := by
  unfold low.generic.sha256_k.K; rfl

theorem K_at (n : Nat) (ht : n < 64) (k : U32) {h}
    (hk : k = low.generic.sha256_k.K.val[n]'h) : k.bv = sha256.K[n]! := by
  rw [← K_spec, hk, getElem!_pos _ n (by simp; omega), List.getElem_map]

/-- `RoundConstants::get::<I>` at index `off` of `sha256_k::K`. -/
theorem rc_get_spec (off : Nat) (I : Usize) (h : off + I.val < 64) :
    low.portable.sha.iram.RoundConstants.get I (low.generic.sha256_k.K, off) ⦃ u =>
      u.bv = sha256.K[off + I.val]! ⦄ := by
  simp only [low.portable.sha.iram.RoundConstants.get, h, _root_.dite_true, WP.spec_ok]
  rw [← K_spec, getElem!_pos _ _ (by simp; omega), List.getElem_map]

/-- The block's word `m`, FIPS 180-4 section 5.2.1. -/
theorem words_get (b : List U8) (hb : b.length = 64) (m : Nat) (hm : m < 16) :
    (rind.spec.words (bv b))[m]! =
      be32 b[4 * m]!.bv b[4 * m + 1]!.bv b[4 * m + 2]!.bv b[4 * m + 3]!.bv := by
  have hg : ∀ n < 64, (bv b)[n]! = b[n]!.bv := fun n hn => by
    rw [getElem!_pos _ n (by simp [bv_length]; omega), getElem!_pos _ n (by omega)]
    simp [bv]
  rw [rind.spec.words, getElem!_pos _ m (by simp [bv_length, hb]; omega), List.getElem_map,
    List.getElem_range, hg _ (by omega), hg _ (by omega), hg _ (by omega), hg _ (by omega)]

/-- `as_chunks::<4>` of a block: its sixteen words' bytes. -/
theorem as_chunks4_spec (block : Std.Array U8 64#usize) :
    core.slice.Slice.as_chunks 4#usize (Array.to_slice block) ⦃ p =>
      p.1.val.length = 16 ∧
      ∀ i (h : i < p.1.val.length), (p.1.val[i]).val = (block.val.drop (i * 4)).take 4 ⦄ := by
  have hbl : block.val.length = 64 := block.property
  simp only [core.slice.Slice.as_chunks, show (4#usize).val ≠ 0 by simp, ite_false, WP.spec_ok]
  refine ⟨by simp [Slice.from_val, Slice.length, hbl], fun i h => ?_⟩
  simp only [Slice.from_val, List.getElem_ofFn, Std.Array.from_val, Array.val_to_slice,
    Fin.val_cast, show (4#usize).val = 4 from rfl]

/-- Four bytes from `k`. -/
theorem drop_take4 (l : List U8) (k : Nat) (h : k + 4 ≤ l.length) :
    (l.drop k).take 4 = [l[k]!, l[k + 1]!, l[k + 2]!, l[k + 3]!] := by
  apply List.ext_getElem (by simp; omega)
  intro n h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  rw [List.getElem_take, List.getElem_drop]
  rcases n with _|_|_|_|n
  all_goals first
    | omega
    | (simp only [List.getElem_cons_succ, List.getElem_cons_zero]
       rw [getElem!_pos l _ (by simp at h1; omega)]
       try rfl)

/-- `message_word::<BYTE>`, the Rust that stands for the Xtensa `l32i` and
byte swap: the block's big-endian word `BYTE / 4`. -/
theorem message_word_spec (block : Std.Array U8 64#usize) (m : Nat) (hm : m < 16) (BYTE : Usize)
    (hB : BYTE.val = 4 * m) :
    low.portable.sha.iram.message_word BYTE block ⦃ w =>
      w.bv = (rind.spec.words (bv block.val))[m]! ⦄ := by
  have hbl : block.val.length = 64 := block.property
  unfold low.portable.sha.iram.message_word
  step as ⟨sl, hsl⟩
  rw [hsl]
  step with as_chunks4_spec block as ⟨ws, rest, hwl, hw⟩
  step as ⟨i, hi⟩
  have him : i.val = m := by rw [hi, hB]; omega
  step with Slice.index_usize_spec as ⟨a, ha⟩
  rw [words_get _ hbl m hm]
  have hav : a.val = [block.val[4 * m]!, block.val[4 * m + 1]!, block.val[4 * m + 2]!,
      block.val[4 * m + 3]!] := by
    rw [ha, hw _ _, him, Nat.mul_comm m 4, drop_take4 _ _ (by omega)]
  unfold core.num.U32.from_be_bytes
  rw [rind.sha512_rounds.cast_setWidth, hav]
  simp only [be32]
  exact BitVec.setWidth_eq _

/-- `RoundConstants::next` from `off`, sixteen words on. -/
theorem rc_next_spec (k : Std.Array U32 64#usize) (off : Nat) (h : off + 16 ≤ 64) :
    low.portable.sha.iram.RoundConstants.next (k, off) ⦃ c => c = (k, off + 16) ⦄ := by
  simp [low.portable.sha.iram.RoundConstants.next, h]

/-- What the loop over rounds 16 to 63 keeps: `n` passes done, the cursor at
the next pass's constants, the window, and the working variables. -/
def RoundsInv (M H : List (BitVec 32))
    (p : U32 × U32 × U32 × U32 × U32 × U32 × U32 × U32 × low.portable.sha.iram.Window ×
      low.portable.sha.iram.RoundConstants × U32) : Prop :=
  match p with
  | (a, b, c, d, e, f, g, h, x, kp, n) =>
    n.val ≤ 3 ∧ kp = (low.generic.sha256_k.K, 16 * (n.val + 1)) ∧
      Last16 (sha256.schedule M) (16 * (n.val + 1)) x ∧
      [a.bv, b.bv, c.bv, d.bv, e.bv, f.bv, g.bv, h.bv] =
        (List.range (16 * (n.val + 1))).foldl (sha256Round (sha256.schedule M)) H

set_option maxHeartbeats 4000000 in
/-- Rounds `16 (n + 1)` to 63. -/
theorem rounds_spec (M : List (BitVec 32)) (hM : M.length = 16) (H : List (BitVec 32))
    (a b c d e f g h : U32) (x : low.portable.sha.iram.Window)
    (kp : low.portable.sha.iram.RoundConstants) (n : U32)
    (hinv : RoundsInv M H (a, b, c, d, e, f, g, h, x, kp, n)) :
    low.portable.sha.iram.sha256_compress_block_loop a b c d e f g h x kp n ⦃ r =>
      [r.1.bv, r.2.1.bv, r.2.2.1.bv, r.2.2.2.1.bv, r.2.2.2.2.1.bv, r.2.2.2.2.2.1.bv,
        r.2.2.2.2.2.2.1.bv, r.2.2.2.2.2.2.2.bv] =
        (List.range 64).foldl (sha256Round (sha256.schedule M)) H ⦄ := by
  set W := sha256.schedule M
  unfold low.portable.sha.iram.sha256_compress_block_loop
  apply loop.spec_decr_nat (fun p => 3 - p.2.2.2.2.2.2.2.2.2.2.val) (RoundsInv M H)
  · rintro ⟨a, b, c, d, e, f, g, h, x, kp, n⟩ ⟨hn, hkp, hx, hs⟩
    subst hkp
    unfold low.portable.sha.iram.sha256_compress_block_loop.body
    dsimp only
    split
    · rename_i hlt
      have hn3 : n.val < 3 := by scalar_tac
      step with rc_get_spec (16 * (n.val + 1)) 0#usize (by simp; omega) as ⟨kk0, hkk0⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 0) 0#usize x (by omega) (by omega) (by simp)
        (by simpa using hx) as ⟨ww0, x1, hww0, hl1⟩
      step with round_spec W H (16 * (n.val + 1) + 0) (16 * (n.val + 1) + 0 + 1) rfl ww0 kk0
        a b c d e f g h (by simpa using hs) hww0
        (by simpa using hkk0) as ⟨a1, b1, c1, d1, e1, f1, g1, h1, hs1⟩
      step with rc_get_spec (16 * (n.val + 1)) 1#usize (by simp; omega) as ⟨kk1, hkk1⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 1) 1#usize x1 (by omega) (by omega) (by simp)
        (by simpa using hl1) as ⟨ww1, x2, hww1, hl2⟩
      step with round_spec W H (16 * (n.val + 1) + 1) (16 * (n.val + 1) + 1 + 1) rfl ww1 kk1
        a1 b1 c1 d1 e1 f1 g1 h1 (by simpa using hs1) hww1
        (by simpa using hkk1) as ⟨a2, b2, c2, d2, e2, f2, g2, h2, hs2⟩
      step with rc_get_spec (16 * (n.val + 1)) 2#usize (by simp; omega) as ⟨kk2, hkk2⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 2) 2#usize x2 (by omega) (by omega) (by simp)
        (by simpa using hl2) as ⟨ww2, x3, hww2, hl3⟩
      step with round_spec W H (16 * (n.val + 1) + 2) (16 * (n.val + 1) + 2 + 1) rfl ww2 kk2
        a2 b2 c2 d2 e2 f2 g2 h2 (by simpa using hs2) hww2
        (by simpa using hkk2) as ⟨a3, b3, c3, d3, e3, f3, g3, h3, hs3⟩
      step with rc_get_spec (16 * (n.val + 1)) 3#usize (by simp; omega) as ⟨kk3, hkk3⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 3) 3#usize x3 (by omega) (by omega) (by simp)
        (by simpa using hl3) as ⟨ww3, x4, hww3, hl4⟩
      step with round_spec W H (16 * (n.val + 1) + 3) (16 * (n.val + 1) + 3 + 1) rfl ww3 kk3
        a3 b3 c3 d3 e3 f3 g3 h3 (by simpa using hs3) hww3
        (by simpa using hkk3) as ⟨a4, b4, c4, d4, e4, f4, g4, h4, hs4⟩
      step with rc_get_spec (16 * (n.val + 1)) 4#usize (by simp; omega) as ⟨kk4, hkk4⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 4) 4#usize x4 (by omega) (by omega) (by simp)
        (by simpa using hl4) as ⟨ww4, x5, hww4, hl5⟩
      step with round_spec W H (16 * (n.val + 1) + 4) (16 * (n.val + 1) + 4 + 1) rfl ww4 kk4
        a4 b4 c4 d4 e4 f4 g4 h4 (by simpa using hs4) hww4
        (by simpa using hkk4) as ⟨a5, b5, c5, d5, e5, f5, g5, h5, hs5⟩
      step with rc_get_spec (16 * (n.val + 1)) 5#usize (by simp; omega) as ⟨kk5, hkk5⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 5) 5#usize x5 (by omega) (by omega) (by simp)
        (by simpa using hl5) as ⟨ww5, x6, hww5, hl6⟩
      step with round_spec W H (16 * (n.val + 1) + 5) (16 * (n.val + 1) + 5 + 1) rfl ww5 kk5
        a5 b5 c5 d5 e5 f5 g5 h5 (by simpa using hs5) hww5
        (by simpa using hkk5) as ⟨a6, b6, c6, d6, e6, f6, g6, h6, hs6⟩
      step with rc_get_spec (16 * (n.val + 1)) 6#usize (by simp; omega) as ⟨kk6, hkk6⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 6) 6#usize x6 (by omega) (by omega) (by simp)
        (by simpa using hl6) as ⟨ww6, x7, hww6, hl7⟩
      step with round_spec W H (16 * (n.val + 1) + 6) (16 * (n.val + 1) + 6 + 1) rfl ww6 kk6
        a6 b6 c6 d6 e6 f6 g6 h6 (by simpa using hs6) hww6
        (by simpa using hkk6) as ⟨a7, b7, c7, d7, e7, f7, g7, h7, hs7⟩
      step with rc_get_spec (16 * (n.val + 1)) 7#usize (by simp; omega) as ⟨kk7, hkk7⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 7) 7#usize x7 (by omega) (by omega) (by simp)
        (by simpa using hl7) as ⟨ww7, x8, hww7, hl8⟩
      step with round_spec W H (16 * (n.val + 1) + 7) (16 * (n.val + 1) + 7 + 1) rfl ww7 kk7
        a7 b7 c7 d7 e7 f7 g7 h7 (by simpa using hs7) hww7
        (by simpa using hkk7) as ⟨a8, b8, c8, d8, e8, f8, g8, h8, hs8⟩
      step with rc_get_spec (16 * (n.val + 1)) 8#usize (by simp; omega) as ⟨kk8, hkk8⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 8) 8#usize x8 (by omega) (by omega) (by simp)
        (by simpa using hl8) as ⟨ww8, x9, hww8, hl9⟩
      step with round_spec W H (16 * (n.val + 1) + 8) (16 * (n.val + 1) + 8 + 1) rfl ww8 kk8
        a8 b8 c8 d8 e8 f8 g8 h8 (by simpa using hs8) hww8
        (by simpa using hkk8) as ⟨a9, b9, c9, d9, e9, f9, g9, h9, hs9⟩
      step with rc_get_spec (16 * (n.val + 1)) 9#usize (by simp; omega) as ⟨kk9, hkk9⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 9) 9#usize x9 (by omega) (by omega) (by simp)
        (by simpa using hl9) as ⟨ww9, x10, hww9, hl10⟩
      step with round_spec W H (16 * (n.val + 1) + 9) (16 * (n.val + 1) + 9 + 1) rfl ww9 kk9
        a9 b9 c9 d9 e9 f9 g9 h9 (by simpa using hs9) hww9
        (by simpa using hkk9) as ⟨a10, b10, c10, d10, e10, f10, g10, h10, hs10⟩
      step with rc_get_spec (16 * (n.val + 1)) 10#usize (by simp; omega) as ⟨kk10, hkk10⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 10) 10#usize x10 (by omega) (by omega) (by simp)
        (by simpa using hl10) as ⟨ww10, x11, hww10, hl11⟩
      step with round_spec W H (16 * (n.val + 1) + 10) (16 * (n.val + 1) + 10 + 1) rfl ww10 kk10
        a10 b10 c10 d10 e10 f10 g10 h10 (by simpa using hs10) hww10
        (by simpa using hkk10) as ⟨a11, b11, c11, d11, e11, f11, g11, h11, hs11⟩
      step with rc_get_spec (16 * (n.val + 1)) 11#usize (by simp; omega) as ⟨kk11, hkk11⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 11) 11#usize x11 (by omega) (by omega) (by simp)
        (by simpa using hl11) as ⟨ww11, x12, hww11, hl12⟩
      step with round_spec W H (16 * (n.val + 1) + 11) (16 * (n.val + 1) + 11 + 1) rfl ww11 kk11
        a11 b11 c11 d11 e11 f11 g11 h11 (by simpa using hs11) hww11
        (by simpa using hkk11) as ⟨a12, b12, c12, d12, e12, f12, g12, h12, hs12⟩
      step with rc_get_spec (16 * (n.val + 1)) 12#usize (by simp; omega) as ⟨kk12, hkk12⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 12) 12#usize x12 (by omega) (by omega) (by simp)
        (by simpa using hl12) as ⟨ww12, x13, hww12, hl13⟩
      step with round_spec W H (16 * (n.val + 1) + 12) (16 * (n.val + 1) + 12 + 1) rfl ww12 kk12
        a12 b12 c12 d12 e12 f12 g12 h12 (by simpa using hs12) hww12
        (by simpa using hkk12) as ⟨a13, b13, c13, d13, e13, f13, g13, h13, hs13⟩
      step with rc_get_spec (16 * (n.val + 1)) 13#usize (by simp; omega) as ⟨kk13, hkk13⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 13) 13#usize x13 (by omega) (by omega) (by simp)
        (by simpa using hl13) as ⟨ww13, x14, hww13, hl14⟩
      step with round_spec W H (16 * (n.val + 1) + 13) (16 * (n.val + 1) + 13 + 1) rfl ww13 kk13
        a13 b13 c13 d13 e13 f13 g13 h13 (by simpa using hs13) hww13
        (by simpa using hkk13) as ⟨a14, b14, c14, d14, e14, f14, g14, h14, hs14⟩
      step with rc_get_spec (16 * (n.val + 1)) 14#usize (by simp; omega) as ⟨kk14, hkk14⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 14) 14#usize x14 (by omega) (by omega) (by simp)
        (by simpa using hl14) as ⟨ww14, x15, hww14, hl15⟩
      step with round_spec W H (16 * (n.val + 1) + 14) (16 * (n.val + 1) + 14 + 1) rfl ww14 kk14
        a14 b14 c14 d14 e14 f14 g14 h14 (by simpa using hs14) hww14
        (by simpa using hkk14) as ⟨a15, b15, c15, d15, e15, f15, g15, h15, hs15⟩
      step with rc_get_spec (16 * (n.val + 1)) 15#usize (by simp; omega) as ⟨kk15, hkk15⟩
      step with schedule_spec M hM (16 * (n.val + 1) + 15) 15#usize x15 (by omega) (by omega) (by simp)
        (by simpa using hl15) as ⟨ww15, x16, hww15, hl16⟩
      step with round_spec W H (16 * (n.val + 1) + 15) (16 * (n.val + 1) + 15 + 1) rfl ww15 kk15
        a15 b15 c15 d15 e15 f15 g15 h15 (by simpa using hs15) hww15
        (by simpa using hkk15) as ⟨a16, b16, c16, d16, e16, f16, g16, h16, hs16⟩
      step with rc_next_spec low.generic.sha256_k.K (16 * (n.val + 1)) (by omega) as ⟨kp1, hkp1⟩
      step as ⟨n1, hn1⟩
      have he : 16 * (n1.val + 1) = 16 * (n.val + 1) + 15 + 1 := by rw [hn1]; ring
      refine ⟨⟨by omega, by rw [hkp1, he], by rw [he]; exact hl16, by rw [he]; exact hs16⟩, by omega⟩
    · rename_i hlt
      simp only [WP.spec_ok]
      rw [show n.val = 3 by scalar_tac] at hs
      exact hs
  · exact hinv

/-- The cursor at the table's start. -/
theorem rc_first : low.portable.sha.iram.RoundConstants.first low.generic.sha256_k.K =
    ok (low.generic.sha256_k.K, 0) := rfl

theorem window_new : low.portable.sha.iram.Window.new = ok (Std.Array.repeat 16#usize none) := rfl

set_option maxHeartbeats 4000000 in
/-- One block: FIPS 180-4's compression of it into `state`. -/
theorem block_spec (state : Std.Array U32 8#usize) (block : Std.Array U8 64#usize) :
    low.portable.sha.iram.sha256_compress_block state block ⦃ r =>
      words r.val = sha256.compress (words state.val) (bv block.val) ⦄ := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, hst⟩ := arr8 state
  have hbl : block.val.length = 64 := block.property
  set M := rind.spec.words (bv block.val) with hM_def
  have hM : M.length = 16 := by simp [M, rind.spec.words, bv_length, hbl]
  set W := sha256.schedule M
  unfold low.portable.sha.iram.sha256_compress_block
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
  set H : List (BitVec 32) := [a.bv, b.bv, c.bv, d.bv, e.bv, f.bv, g.bv, h.bv]
  have hs0 : [a.bv, b.bv, c.bv, d.bv, e.bv, f.bv, g.bv, h.bv] = (List.range 0).foldl (sha256Round W) H := rfl
  rw [window_new, bind_ok, rc_first, bind_ok]
  generalize hx0 : Std.Array.repeat 16#usize (none : Option U32) = x0
  have hl0 : Last16 W 0 x0 := last16_zero _ _
  step with rc_get_spec 0 0#usize (by simp) as ⟨kk0, hkk0⟩
  step with message_word_spec block 0 (by omega) 0#usize (by simp) as ⟨ww0, hww0⟩
  have hw0 : ww0.bv = W[0]! := by rw [schedule_lt M hM _ (by omega)]; exact hww0
  step with window_set_spec x0 0#usize (by simp) ww0 as ⟨x1, hx1⟩
  have hl1 : Last16 W 1 x1 := by
    rw [hx1]; exact last16_set W 0 x0 hl0 _ (by simp) _ hw0
  step with round_spec W H 0 1 rfl ww0 kk0 a b c d e f g h hs0 hw0
    (by simpa using hkk0) as ⟨a1, b1, c1, d1, e1, f1, g1, h1, hs1⟩
  step with rc_get_spec 0 1#usize (by simp) as ⟨kk1, hkk1⟩
  step with message_word_spec block 1 (by omega) 4#usize (by simp) as ⟨ww1, hww1⟩
  have hw1 : ww1.bv = W[1]! := by rw [schedule_lt M hM _ (by omega)]; exact hww1
  step with window_set_spec x1 1#usize (by simp) ww1 as ⟨x2, hx2⟩
  have hl2 : Last16 W 2 x2 := by
    rw [hx2]; exact last16_set W 1 x1 hl1 _ (by simp) _ hw1
  step with round_spec W H 1 2 rfl ww1 kk1 a1 b1 c1 d1 e1 f1 g1 h1 hs1 hw1
    (by simpa using hkk1) as ⟨a2, b2, c2, d2, e2, f2, g2, h2, hs2⟩
  step with rc_get_spec 0 2#usize (by simp) as ⟨kk2, hkk2⟩
  step with message_word_spec block 2 (by omega) 8#usize (by simp) as ⟨ww2, hww2⟩
  have hw2 : ww2.bv = W[2]! := by rw [schedule_lt M hM _ (by omega)]; exact hww2
  step with window_set_spec x2 2#usize (by simp) ww2 as ⟨x3, hx3⟩
  have hl3 : Last16 W 3 x3 := by
    rw [hx3]; exact last16_set W 2 x2 hl2 _ (by simp) _ hw2
  step with round_spec W H 2 3 rfl ww2 kk2 a2 b2 c2 d2 e2 f2 g2 h2 hs2 hw2
    (by simpa using hkk2) as ⟨a3, b3, c3, d3, e3, f3, g3, h3, hs3⟩
  step with rc_get_spec 0 3#usize (by simp) as ⟨kk3, hkk3⟩
  step with message_word_spec block 3 (by omega) 12#usize (by simp) as ⟨ww3, hww3⟩
  have hw3 : ww3.bv = W[3]! := by rw [schedule_lt M hM _ (by omega)]; exact hww3
  step with window_set_spec x3 3#usize (by simp) ww3 as ⟨x4, hx4⟩
  have hl4 : Last16 W 4 x4 := by
    rw [hx4]; exact last16_set W 3 x3 hl3 _ (by simp) _ hw3
  step with round_spec W H 3 4 rfl ww3 kk3 a3 b3 c3 d3 e3 f3 g3 h3 hs3 hw3
    (by simpa using hkk3) as ⟨a4, b4, c4, d4, e4, f4, g4, h4, hs4⟩
  step with rc_get_spec 0 4#usize (by simp) as ⟨kk4, hkk4⟩
  step with message_word_spec block 4 (by omega) 16#usize (by simp) as ⟨ww4, hww4⟩
  have hw4 : ww4.bv = W[4]! := by rw [schedule_lt M hM _ (by omega)]; exact hww4
  step with window_set_spec x4 4#usize (by simp) ww4 as ⟨x5, hx5⟩
  have hl5 : Last16 W 5 x5 := by
    rw [hx5]; exact last16_set W 4 x4 hl4 _ (by simp) _ hw4
  step with round_spec W H 4 5 rfl ww4 kk4 a4 b4 c4 d4 e4 f4 g4 h4 hs4 hw4
    (by simpa using hkk4) as ⟨a5, b5, c5, d5, e5, f5, g5, h5, hs5⟩
  step with rc_get_spec 0 5#usize (by simp) as ⟨kk5, hkk5⟩
  step with message_word_spec block 5 (by omega) 20#usize (by simp) as ⟨ww5, hww5⟩
  have hw5 : ww5.bv = W[5]! := by rw [schedule_lt M hM _ (by omega)]; exact hww5
  step with window_set_spec x5 5#usize (by simp) ww5 as ⟨x6, hx6⟩
  have hl6 : Last16 W 6 x6 := by
    rw [hx6]; exact last16_set W 5 x5 hl5 _ (by simp) _ hw5
  step with round_spec W H 5 6 rfl ww5 kk5 a5 b5 c5 d5 e5 f5 g5 h5 hs5 hw5
    (by simpa using hkk5) as ⟨a6, b6, c6, d6, e6, f6, g6, h6, hs6⟩
  step with rc_get_spec 0 6#usize (by simp) as ⟨kk6, hkk6⟩
  step with message_word_spec block 6 (by omega) 24#usize (by simp) as ⟨ww6, hww6⟩
  have hw6 : ww6.bv = W[6]! := by rw [schedule_lt M hM _ (by omega)]; exact hww6
  step with window_set_spec x6 6#usize (by simp) ww6 as ⟨x7, hx7⟩
  have hl7 : Last16 W 7 x7 := by
    rw [hx7]; exact last16_set W 6 x6 hl6 _ (by simp) _ hw6
  step with round_spec W H 6 7 rfl ww6 kk6 a6 b6 c6 d6 e6 f6 g6 h6 hs6 hw6
    (by simpa using hkk6) as ⟨a7, b7, c7, d7, e7, f7, g7, h7, hs7⟩
  step with rc_get_spec 0 7#usize (by simp) as ⟨kk7, hkk7⟩
  step with message_word_spec block 7 (by omega) 28#usize (by simp) as ⟨ww7, hww7⟩
  have hw7 : ww7.bv = W[7]! := by rw [schedule_lt M hM _ (by omega)]; exact hww7
  step with window_set_spec x7 7#usize (by simp) ww7 as ⟨x8, hx8⟩
  have hl8 : Last16 W 8 x8 := by
    rw [hx8]; exact last16_set W 7 x7 hl7 _ (by simp) _ hw7
  step with round_spec W H 7 8 rfl ww7 kk7 a7 b7 c7 d7 e7 f7 g7 h7 hs7 hw7
    (by simpa using hkk7) as ⟨a8, b8, c8, d8, e8, f8, g8, h8, hs8⟩
  step with rc_get_spec 0 8#usize (by simp) as ⟨kk8, hkk8⟩
  step with message_word_spec block 8 (by omega) 32#usize (by simp) as ⟨ww8, hww8⟩
  have hw8 : ww8.bv = W[8]! := by rw [schedule_lt M hM _ (by omega)]; exact hww8
  step with window_set_spec x8 8#usize (by simp) ww8 as ⟨x9, hx9⟩
  have hl9 : Last16 W 9 x9 := by
    rw [hx9]; exact last16_set W 8 x8 hl8 _ (by simp) _ hw8
  step with round_spec W H 8 9 rfl ww8 kk8 a8 b8 c8 d8 e8 f8 g8 h8 hs8 hw8
    (by simpa using hkk8) as ⟨a9, b9, c9, d9, e9, f9, g9, h9, hs9⟩
  step with rc_get_spec 0 9#usize (by simp) as ⟨kk9, hkk9⟩
  step with message_word_spec block 9 (by omega) 36#usize (by simp) as ⟨ww9, hww9⟩
  have hw9 : ww9.bv = W[9]! := by rw [schedule_lt M hM _ (by omega)]; exact hww9
  step with window_set_spec x9 9#usize (by simp) ww9 as ⟨x10, hx10⟩
  have hl10 : Last16 W 10 x10 := by
    rw [hx10]; exact last16_set W 9 x9 hl9 _ (by simp) _ hw9
  step with round_spec W H 9 10 rfl ww9 kk9 a9 b9 c9 d9 e9 f9 g9 h9 hs9 hw9
    (by simpa using hkk9) as ⟨a10, b10, c10, d10, e10, f10, g10, h10, hs10⟩
  step with rc_get_spec 0 10#usize (by simp) as ⟨kk10, hkk10⟩
  step with message_word_spec block 10 (by omega) 40#usize (by simp) as ⟨ww10, hww10⟩
  have hw10 : ww10.bv = W[10]! := by rw [schedule_lt M hM _ (by omega)]; exact hww10
  step with window_set_spec x10 10#usize (by simp) ww10 as ⟨x11, hx11⟩
  have hl11 : Last16 W 11 x11 := by
    rw [hx11]; exact last16_set W 10 x10 hl10 _ (by simp) _ hw10
  step with round_spec W H 10 11 rfl ww10 kk10 a10 b10 c10 d10 e10 f10 g10 h10 hs10 hw10
    (by simpa using hkk10) as ⟨a11, b11, c11, d11, e11, f11, g11, h11, hs11⟩
  step with rc_get_spec 0 11#usize (by simp) as ⟨kk11, hkk11⟩
  step with message_word_spec block 11 (by omega) 44#usize (by simp) as ⟨ww11, hww11⟩
  have hw11 : ww11.bv = W[11]! := by rw [schedule_lt M hM _ (by omega)]; exact hww11
  step with window_set_spec x11 11#usize (by simp) ww11 as ⟨x12, hx12⟩
  have hl12 : Last16 W 12 x12 := by
    rw [hx12]; exact last16_set W 11 x11 hl11 _ (by simp) _ hw11
  step with round_spec W H 11 12 rfl ww11 kk11 a11 b11 c11 d11 e11 f11 g11 h11 hs11 hw11
    (by simpa using hkk11) as ⟨a12, b12, c12, d12, e12, f12, g12, h12, hs12⟩
  step with rc_get_spec 0 12#usize (by simp) as ⟨kk12, hkk12⟩
  step with message_word_spec block 12 (by omega) 48#usize (by simp) as ⟨ww12, hww12⟩
  have hw12 : ww12.bv = W[12]! := by rw [schedule_lt M hM _ (by omega)]; exact hww12
  step with window_set_spec x12 12#usize (by simp) ww12 as ⟨x13, hx13⟩
  have hl13 : Last16 W 13 x13 := by
    rw [hx13]; exact last16_set W 12 x12 hl12 _ (by simp) _ hw12
  step with round_spec W H 12 13 rfl ww12 kk12 a12 b12 c12 d12 e12 f12 g12 h12 hs12 hw12
    (by simpa using hkk12) as ⟨a13, b13, c13, d13, e13, f13, g13, h13, hs13⟩
  step with rc_get_spec 0 13#usize (by simp) as ⟨kk13, hkk13⟩
  step with message_word_spec block 13 (by omega) 52#usize (by simp) as ⟨ww13, hww13⟩
  have hw13 : ww13.bv = W[13]! := by rw [schedule_lt M hM _ (by omega)]; exact hww13
  step with window_set_spec x13 13#usize (by simp) ww13 as ⟨x14, hx14⟩
  have hl14 : Last16 W 14 x14 := by
    rw [hx14]; exact last16_set W 13 x13 hl13 _ (by simp) _ hw13
  step with round_spec W H 13 14 rfl ww13 kk13 a13 b13 c13 d13 e13 f13 g13 h13 hs13 hw13
    (by simpa using hkk13) as ⟨a14, b14, c14, d14, e14, f14, g14, h14, hs14⟩
  step with rc_get_spec 0 14#usize (by simp) as ⟨kk14, hkk14⟩
  step with message_word_spec block 14 (by omega) 56#usize (by simp) as ⟨ww14, hww14⟩
  have hw14 : ww14.bv = W[14]! := by rw [schedule_lt M hM _ (by omega)]; exact hww14
  step with window_set_spec x14 14#usize (by simp) ww14 as ⟨x15, hx15⟩
  have hl15 : Last16 W 15 x15 := by
    rw [hx15]; exact last16_set W 14 x14 hl14 _ (by simp) _ hw14
  step with round_spec W H 14 15 rfl ww14 kk14 a14 b14 c14 d14 e14 f14 g14 h14 hs14 hw14
    (by simpa using hkk14) as ⟨a15, b15, c15, d15, e15, f15, g15, h15, hs15⟩
  step with rc_get_spec 0 15#usize (by simp) as ⟨kk15, hkk15⟩
  step with message_word_spec block 15 (by omega) 60#usize (by simp) as ⟨ww15, hww15⟩
  have hw15 : ww15.bv = W[15]! := by rw [schedule_lt M hM _ (by omega)]; exact hww15
  step with window_set_spec x15 15#usize (by simp) ww15 as ⟨x16, hx16⟩
  have hl16 : Last16 W 16 x16 := by
    rw [hx16]; exact last16_set W 15 x15 hl15 _ (by simp) _ hw15
  step with round_spec W H 15 16 rfl ww15 kk15 a15 b15 c15 d15 e15 f15 g15 h15 hs15 hw15
    (by simpa using hkk15) as ⟨a16, b16, c16, d16, e16, f16, g16, h16, hs16⟩
  step with rc_next_spec low.generic.sha256_k.K 0 (by omega) as ⟨kp1, hkp1⟩
  step with rounds_spec M hM H a16 b16 c16 d16 e16 f16 g16 h16 x16 kp1 0#u32
    ⟨by simp, by rw [hkp1]; rfl, by simpa using hl16, by simpa using hs16⟩
    as ⟨a17, b17, c17, d17, e17, f17, g17, h17, hr⟩
  step*
  have hr' : words r.val = [a.bv + a17.bv, b.bv + b17.bv, c.bv + c17.bv, d.bv + d17.bv,
      e.bv + e17.bv, f.bv + f17.bv, g.bv + g17.bv, h.bv + h17.bv] := by
    simp only [r_post, state1_post, state2_post, state3_post, state4_post, state5_post, state6_post,
      state7_post, i_post, i1_post, i2_post, i3_post, i4_post, i5_post, i6_post, i7_post, i8_post,
      i9_post, i10_post, i11_post, i12_post, i13_post, i14_post, i15_post, Array.set_val_eq, hst]
    simp [words]
  rw [hr', compress_eq, hst, show words [a, b, c, d, e, f, g, h] = H by rfl, ← hr]
  simp [H, BitVec.add_comm]

/-- `Blocks::block` at `off`: the 64 bytes there. -/
theorem blocks_block_spec (s : Slice U8) (off : Nat) (h : off + 64 ≤ s.length) :
    low.portable.sha.iram.Blocks.block (s, off) ⦃ b => b.val = (s.val.drop off).take 64 ⦄ := by
  simp [low.portable.sha.iram.Blocks.block, h, Std.Array.from_val]

/-- `Blocks::next` from `off`, 64 bytes on. -/
theorem blocks_next_spec (s : Slice U8) (off : Nat) (h : off + 64 ≤ s.length) :
    low.portable.sha.iram.Blocks.next (s, off) ⦃ c => c = (s, off + 64) ⦄ := by
  simp [low.portable.sha.iram.Blocks.next, h]

end rind.mcu.sha256_iram

namespace rind.mcu
open sha256_iram rind.sha256_rounds

/-- The IRAM body's block function computes FIPS 180-4's compression of each
whole block in turn, every cursor and window read inside what the models
allow. -/
theorem iram_sha256_compress_blocks_spec :
    Compresses sha256.compress low.portable.sha.iram.sha256_update_nblocks := by
  intro h0 bs hl
  unfold low.portable.sha.iram.sha256_update_nblocks
  rw [show low.portable.sha.iram.Blocks.new bs = ok (bs, 0) from rfl, bind_ok]
  step as ⟨whole, hwhole⟩
  have hw' : whole.val = bs.length / 64 := by rw [hwhole, Slice.len_val]
  unfold low.portable.sha.iram.sha256_update_nblocks_loop
  apply loop.spec_decr_nat (fun p => whole.val - p.2.2.val)
    (fun p => p.2.2.val ≤ whole.val ∧ p.2.1 = (bs, 64 * p.2.2.val) ∧
      words p.1.val =
        (rind.spec.blocks 64 (bv (bs.val.take (64 * p.2.2.val)))).foldl sha256.compress (words h0.val))
  · rintro ⟨st, cur, n⟩ ⟨hn, hcur, hs⟩
    simp only at hn hcur hs ⊢
    subst hcur
    unfold low.portable.sha.iram.sha256_update_nblocks_loop.body
    split
    · rename_i hlt
      have hlt' : n.val < whole.val := by scalar_tac
      have hle : 64 * n.val + 64 ≤ bs.length := by omega
      step with blocks_block_spec bs (64 * n.val) hle as ⟨block, hblock⟩
      step with block_spec as ⟨st1, hst1⟩
      step with blocks_next_spec bs (64 * n.val) hle as ⟨cur1, hcur1⟩
      step as ⟨n1, hn1⟩
      have he : 64 * n1.val = 64 * n.val + 64 := by rw [hn1]; ring
      have htake : (bv (bs.val.take (64 * n.val))).length % 64 = 0 := by
        rw [bv_length, List.length_take]; simp only [Slice.length] at hle
        rw [Nat.min_eq_left (by omega)]; omega
      have hbl : (bv block.val).length = 64 := by rw [bv_length]; simp
      split_ands
      · omega
      · rw [hcur1, he]
      swap
      · omega
      rw [he, List.take_add, bv, List.map_append, ← bv, ← bv, ← hblock,
        blocks_append (by omega) _ _ htake, blocks_single (bv block.val) hbl,
        List.foldl_append, ← hs, List.foldl_cons, List.foldl_nil, hst1]
    · rename_i hlt
      have hge : whole.val ≤ n.val := by scalar_tac
      simp only [WP.spec_ok]
      have hlen : bs.val.length ≤ 64 * n.val := by simp only [Slice.length] at hl hw'; omega
      rw [hs, List.take_of_length_le hlen]
  · refine ⟨by simp, by simp, ?_⟩
    simp [bv, blocks_nil]

end rind.mcu
