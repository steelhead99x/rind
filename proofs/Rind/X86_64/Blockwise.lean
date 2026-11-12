import Rind.X86_64.Funs
import Rind.HashSpec
import Rind.Bytes
open Aeneas Aeneas.Std Result

/-!
# Merkle-Damgard padding and buffering, `low::generic::blockwise`

What `split_tail`, `pad`, and `Blockwise` compute, for any hash whose block
function, or `UpdateBlocks` impl, adds whole blocks to what its state has
absorbed.
-/

namespace rind.x86_64

/-- The zero bytes FIPS 180-4's padding puts between the 0x80 byte and an
`L`-byte length after `n` bytes, for `N`-byte blocks. -/
def padZeros (N L n : Nat) : Nat := (N - (n + 1 + L) % N) % N

@[step]
theorem as_flattened_mut_spec {T : Type} {N : Usize} (s : Slice (Std.Array T N))
    (h : (s.val.flatMap (·.val)).length ≤ Usize.max) :
    core.slice.SliceArray.as_flattened_mut s ⦃ f _ => f.val = s.val.flatMap (·.val) ⦄ := by
  unfold core.slice.SliceArray.as_flattened_mut
  simp only
  rw [dite_eq_left_of_eq_true (eq_true h)]
  simp

/-- `pad`'s length: the rest, the 0x80 byte, the zeros, and the length fill
one or two whole blocks. -/
theorem padded_eq {N L n : Nat} (_hN : 0 < N) (hL : L + 1 ≤ N) (hr : n + 1 + L ≤ 2 * N) :
    (if n % N + 1 + L ≤ N then n / N * N + N else n / N * N + 2 * N) =
      n + 1 + L + padZeros N L n := by
  unfold padZeros
  rcases Nat.lt_or_ge n N with h | h
  · have h1 : n / N = 0 := Nat.div_eq_of_lt h
    have h2 : n % N = n := Nat.mod_eq_of_lt h
    rw [h1, h2]
    by_cases h3 : n + 1 + L ≤ N
    · rcases Nat.lt_or_ge (n + 1 + L) N with h4 | h4
      · rw [Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt (by omega)]; simp [h3]
      · have : n + 1 + L = N := by omega
        rw [this, Nat.mod_self]; simp
    · have h4 : (n + 1 + L) % N = n + 1 + L - N := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [h4, Nat.mod_eq_of_lt (by omega)]; simp [h3]; omega
  · have h1 : n / N = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h2 : n % N = n - N := by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [h1, h2, ite_eq_left (show n - N + 1 + L ≤ N by omega)]
    rcases Nat.lt_or_ge (n + 1 + L) (2 * N) with h3 | h3
    · have h4 : (n + 1 + L) % N = n + 1 + L - N := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [h4, Nat.mod_eq_of_lt (by omega)]; omega
    · have : n + 1 + L = 2 * N := by omega
      rw [this, Nat.mul_mod_left, Nat.sub_zero, Nat.mod_self]; omega

theorem padded_le {N L n : Nat} (hN : 0 < N) (hL : L + 1 ≤ N) (hr : n + 1 + L ≤ 2 * N) :
    n + 1 + L + padZeros N L n ≤ 2 * N := by
  rw [← padded_eq hN hL hr]
  rcases Nat.lt_or_ge n N with h | h
  · rw [Nat.div_eq_of_lt h]; split <;> omega
  · have h2 : n % N = n - N := by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega), h2]; split <;> omega

theorem setSlice!_eq {α : Type} (s s' : List α) (i : Nat) (h : i + s'.length ≤ s.length) :
    s.setSlice! i s' = s.take i ++ s' ++ s.drop (i + s'.length) := by
  simp only [List.setSlice!]
  rw [Nat.min_eq_left (by omega), List.take_length]

/-- What `pad` writes into its zeroed buffer of `P` bytes. -/
theorem pad_list (r len : List U8) (P : Nat) (hP : r.length + 1 + len.length ≤ P) :
    (((List.replicate P 0#u8).setSlice! 0 r).set r.length 128#u8).setSlice! (P - len.length) len =
      r ++ [128#u8] ++ List.replicate (P - len.length - 1 - r.length) 0#u8 ++ len := by
  obtain ⟨Z, rfl⟩ : ∃ Z, P = r.length + 1 + Z + len.length :=
    ⟨P - len.length - 1 - r.length, by omega⟩
  have hA : (List.replicate (r.length + 1 + Z + len.length) 0#u8).setSlice! 0 r =
      r ++ List.replicate (Z + len.length + 1) 0#u8 := by
    rw [setSlice!_eq _ _ _ (by simp; omega)]
    simp only [List.take_zero, List.nil_append, Nat.zero_add, List.drop_replicate]
    congr 2
    omega
  have hB : (r ++ List.replicate (Z + len.length + 1) 0#u8).set r.length 128#u8 =
      (r ++ 128#u8 :: List.replicate Z 0#u8) ++ List.replicate len.length 0#u8 := by
    rw [List.set_append_right _ _ (by simp), Nat.sub_self, List.replicate_succ,
      List.set_cons_zero, List.replicate_add]
    simp
  have hC : r.length + 1 + Z + len.length - len.length =
      (r ++ 128#u8 :: List.replicate Z 0#u8).length := by simp; omega
  rw [hA, hB, hC, setSlice!_eq _ _ _ (by simp; omega)]
  rw [List.take_left', List.drop_eq_nil_of_le (by simp; omega)]
  · have : (r ++ 128#u8 :: List.replicate Z 0#u8).length - 1 - r.length = Z := by simp
    rw [this]
    simp
  · rfl

theorem pad_spec {N L : Usize} (rest : Slice U8) (length : Std.Array U8 L)
    (hN : 0 < N.val) (hN2 : 2 * N.val ≤ Usize.max) (hL : L.val + 1 ≤ N.val)
    (hr : rest.length + 1 + L.val ≤ 2 * N.val) :
    low.generic.blockwise.pad rest length (Std.Array.repeat 2#usize (Std.Array.repeat N 0#u8))
      ⦃ s _ => s.val = rest.val ++ [128#u8] ++ List.replicate (padZeros N L rest.length) 0#u8 ++
        length.val ⦄ := by
  unfold low.generic.blockwise.pad
  have hlen : rest.len.val = rest.length := by simp [Slice.len, Slice.length]
  have hpad := padded_eq hN hL hr
  have hP2 := padded_le hN hL hr
  have hd : rest.length / N.val ≤ 1 :=
    Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
  have hdm := Nat.div_mul_le_self rest.length N.val
  have hzero : (Std.Array.repeat 2#usize (Std.Array.repeat N 0#u8)).val.flatMap (·.val) =
      List.replicate (2 * N.val) 0#u8 := by
    simp only [Std.Array.repeat, Std.Array.from_val, Nat.two_mul]
    simp [List.replicate_succ]
  step*
  apply WP.spec_bind (Pₘ := fun (padded : Usize) =>
    padded.val = rest.length + 1 + L.val + padZeros N L rest.length)
  · have hxN : rest.length / N.val * N.val ≤ N.val :=
      (Nat.mul_le_mul_right _ hd).trans (by simp)
    split
    · rename_i hc
      have hc' : rest.length % N.val + 1 + L.val ≤ N.val := by
        have := hc; simp only [UScalar.le_equiv] at this; simp only [hlen] at *; omega
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      step as ⟨z, hz⟩
      rw [hz, hy, hx, hlen, ← hpad, ite_eq_left hc']
    · rename_i hc
      have hc' : ¬ rest.length % N.val + 1 + L.val ≤ N.val := by
        have := hc; simp only [UScalar.le_equiv] at this; simp only [hlen] at *; omega
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      step as ⟨w, hw⟩
      step as ⟨z, hz⟩
      rw [hz, hy, hx, hlen, hw, ← hpad, ite_eq_right hc']
  · intro padded hP
    step*
    · simp only [s4_post1, last3_post, s5_post, Slice.length, Slice.set_val_eq, List.length_set,
        s2_post2, List.length_setSlice!, last1_post1.symm.trans rfl, i6_post, Std.Array.to_slice,
        Slice.from_val]
      have h1 := last1_post1
      simp only [Slice.length] at h1 hP
      rw [h1]
      simp
      omega
    · have hs1 : s1.val = List.replicate (2 * N.val) 0#u8 := by rw [s1_post, s_post, hzero]
      have hl1 : last1.val = List.replicate padded.val 0#u8 := by
        rw [last1_post, hs1]; simp [List.slice]; omega
      rw [s4_post2, s6_post, s5_post, last3_post, Slice.set_val_eq, s2_post2, s3_post, hl1, i6_post]
      have hL' : length.val.length = L.val := by simp
      have hr' : rest.len.val = rest.val.length := hlen
      rw [hr', ← hL', Std.Array.to_slice]
      simp only [Slice.length] at hP
      have hz : padded.val - length.val.length - 1 - rest.val.length =
          padZeros N length.val.length rest.val.length := by rw [hL']; omega
      rw [Slice.from_val, pad_list _ _ _ (by rw [hL']; omega), hz]

theorem padZeros_lt (N L n : Nat) (hN : 0 < N) : padZeros N L n < N := Nat.mod_lt _ hN

/-- The padding of `x` bytes ends on a block boundary. -/
theorem pad_mod {N L : Nat} (x : Nat) (hN : 0 < N) : (x + 1 + L + padZeros N L x) % N = 0 := by
  unfold padZeros
  have hr := Nat.mod_lt (x + 1 + L) hN
  rw [Nat.add_mod, Nat.mod_mod]
  rcases Nat.eq_zero_or_pos ((x + 1 + L) % N) with h | h
  · rw [h, Nat.sub_zero, Nat.mod_self]; simp
  · rw [Nat.mod_eq_of_lt (show N - (x + 1 + L) % N < N by omega),
      show (x + 1 + L) % N + (N - (x + 1 + L) % N) = N by omega, Nat.mod_self]

/-- Dropping whole blocks off the front leaves the padding unchanged. -/
theorem padZeros_sub {N L n start : Nat} (h : start % N = 0) (hs : start ≤ n) :
    padZeros N L (n - start) = padZeros N L n := by
  unfold padZeros
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  rw [show n + 1 + L = n - N * q + 1 + L + N * q by omega, Nat.add_mul_mod_self_left]

/-- `split_tail` leaves whole blocks, then a rest that `pad` fits in two
blocks, padded as the whole message would be. -/
@[step]
theorem split_tail_spec {N L : Usize} (message : Slice U8) (hN : 0 < N.val)
    (hN2 : 2 * N.val ≤ Usize.max) (hL : L.val + 1 ≤ N.val) :
    low.generic.blockwise.split_tail N L message ⦃ blocks rest =>
      blocks.length % N.val = 0 ∧ blocks.val ++ rest.val = message.val ∧
      rest.length + 1 + L.val ≤ 2 * N.val ∧
      padZeros N L rest.length = padZeros N L message.length ⦄ := by
  unfold low.generic.blockwise.split_tail
  have hlen : message.len.val = message.length := by simp [Slice.len, Slice.length]
  have hmod := Nat.mod_add_div message.length N.val
  have hlt := Nat.mod_lt message.length hN
  step*
  apply WP.spec_bind (Pₘ := fun (start : Usize) => start.val % N.val = 0 ∧
    start.val ≤ message.length ∧ message.length - start.val + 1 + L.val ≤ 2 * N.val)
  · have hq : (N.val * (message.length / N.val)) % N.val = 0 := Nat.mul_mod_right _ _
    have hq1 : (N.val * (message.length / N.val) - N.val) % N.val = 0 := by
      rw [← Nat.mul_sub_one]; exact Nat.mul_mod_right _ _
    simp only [hlen] at tail_post
    split
    · rename_i hc
      have hc' : message.length % N.val + 1 + L.val ≤ N.val := by
        simp only [UScalar.le_equiv] at hc; omega
      split
      · rename_i hge
        have hge' : N.val ≤ message.length := by
          simp only [GE.ge, UScalar.le_equiv] at hge; omega
        have hNq : N.val ≤ N.val * (message.length / N.val) :=
          Nat.le_mul_of_pos_right _ (Nat.div_pos hge' hN)
        step as ⟨i5, h5⟩
        step as ⟨st, hst⟩
        have : st.val = N.val * (message.length / N.val) - N.val := by omega
        exact ⟨by rw [this]; exact hq1, by omega, by omega⟩
      · rename_i hge
        have hge' : ¬ N.val ≤ message.length := by
          simp only [GE.ge, UScalar.le_equiv] at hge; omega
        step as ⟨st, hst⟩
        have : st.val = N.val * (message.length / N.val) := by omega
        exact ⟨by rw [this]; exact hq, by omega, by omega⟩
    · rename_i hc
      have hc' : ¬ message.length % N.val + 1 + L.val ≤ N.val := by
        simp only [UScalar.le_equiv] at hc; omega
      step as ⟨st, hst⟩
      have : st.val = N.val * (message.length / N.val) := by omega
      exact ⟨by rw [this]; exact hq, by omega, by omega⟩
  · intro start ⟨hs0, hs1, hs2⟩
    step*
    refine ⟨by rw [blocks_post]; exact hs0, ?_, by rw [blocks_post1]; omega, ?_⟩
    · rw [blocks_post2, blocks_post3, List.take_append_drop]
    · rw [blocks_post1]; exact padZeros_sub hs0 hs1

/-- What a hash does after `split_tail`: compresses the whole blocks, if any,
then the rest with its padding. -/
theorem compress_tail_spec {S : Type} {N L : Usize} (F : S → Slice U8 → Result S)
    (R : List U8 → S → Prop) (bound : Nat)
    (hC : ∀ p s (b : Slice U8), R p s → b.length % N.val = 0 → p.length + b.length ≤ bound →
      F s b ⦃ s' => R (p ++ b.val) s' ⦄)
    (p : List U8) (message blocks rest : Slice U8) (length : Std.Array U8 L) (state : S)
    (hR : R p state) (hN : 0 < N.val) (hN2 : 2 * N.val ≤ Usize.max) (hL : L.val + 1 ≤ N.val)
    (hsplit : blocks.length % N.val = 0 ∧ blocks.val ++ rest.val = message.val ∧
      rest.length + 1 + L.val ≤ 2 * N.val ∧
      padZeros N L rest.length = padZeros N L message.length)
    (hb : p.length + message.length + 1 + L.val + padZeros N L message.length ≤ bound) :
    (do
      let b ← core.slice.Slice.is_empty blocks
      let state1 ← if b then ok state else F state blocks
      let a := Std.Array.repeat N 0#u8
      let last := Std.Array.repeat 2#usize a
      let (s, _) ← low.generic.blockwise.pad rest length last
      F state1 s) ⦃ s' =>
      R (p ++ message.val ++ [128#u8] ++ List.replicate (padZeros N L message.length) 0#u8 ++
        length.val) s' ⦄ := by
  obtain ⟨hbl, hbr, hrl, hpz⟩ := hsplit
  have hml : message.length = blocks.length + rest.length := by
    simp only [Slice.length]; rw [← hbr, List.length_append]
  step*
  apply WP.spec_bind (Pₘ := fun s1 => R (p ++ blocks.val) s1)
  · split
    · rename_i hb0
      have : blocks.val = [] := by
        rw [b_post] at hb0; exact List.eq_nil_of_length_eq_zero hb0
      simp only [this, List.append_nil, WP.spec_ok, hR]
    · exact hC _ _ _ hR hbl (by omega)
  · intro s1 hs1R
    step with pad_spec rest length hN hN2 hL hrl as ⟨s, _, hs⟩
    have hsl : s.length = rest.length + 1 + L.val + padZeros N.val L.val rest.length := by
      simp only [Slice.length] at *; rw [hs]; simp; omega
    apply WP.spec_mono (hC _ _ _ hs1R ?_ ?_)
    · intro s' h
      rw [hs, hpz] at h
      simp only [List.append_assoc] at h ⊢
      rw [← hbr]
      simpa only [List.append_assoc] using h
    · rw [hsl]; exact pad_mod _ hN
    · have h3 := hsl
      simp only [List.length_append, Slice.length] at *
      omega

/-- `bw` holds the input `p` that `s` has not absorbed, by `R`, up to a block. -/
def Buffered {N : Usize} {S : Type} (R : List U8 → S → Prop) (p : List U8)
    (bw : low.generic.blockwise.Blockwise N) (s : S) : Prop :=
  bw.used.val ≤ N.val ∧ ∃ q, R q s ∧ q ++ bw.buffer.val.take bw.used.val = p

theorem complete_blocks_spec {S : Type} {N : Usize}
    (inst : low.generic.blockwise.UpdateBlocks S) (R : List U8 → S → Prop) (bound : Nat)
    (hC : ∀ p s (b : Slice U8), R p s → b.length % N.val = 0 → p.length + b.length ≤ bound →
      inst.update_blocks s b ⦃ s' => R (p ++ b.val) s' ⦄)
    (p : List U8) (bw : low.generic.blockwise.Blockwise N) (bytes : Slice U8) (state : S)
    (hB : Buffered R p bw state) (hN : 0 < N.val)
    (hlong : N.val - bw.used.val < bytes.length) (hb : p.length + bytes.length ≤ bound) :
    low.generic.blockwise.Blockwise.complete_blocks inst bw bytes state ⦃ bw' s' =>
      Buffered R (p ++ bytes.val) bw' s' ⦄ := by
  obtain ⟨hu, q, hq, hqp⟩ := hB
  unfold low.generic.blockwise.Blockwise.complete_blocks
  apply WP.spec_bind (Pₘ := fun (r : Std.Array U8 N × Slice U8 × S) =>
    ∃ q', R q' r.2.2 ∧ q' ++ r.2.1.val = p ++ bytes.val ∧ 0 < r.2.1.length)
  · split
    · rename_i hpos
      have hbl : bw.buffer.val.length = N.val := by simp
      step*
      all_goals
        have h2 : s2.val = bw.buffer.val.take bw.used.val ++ head.val := by
          rw [s2_post, Std.Array.to_slice, Slice.from_val, s_post2, s1_post,
            setSlice!_eq _ _ _ (by simp only [Slice.length] at head_post; omega),
            List.drop_eq_nil_of_le (by simp only [Slice.length] at head_post; omega)]
          simp
      all_goals
        have hs2 : s2.val.length = N.val := by
          have := head_post
          simp only [Slice.length] at this
          rw [h2, List.length_append, List.length_take, hbl, this, i_post]; omega
      · simp only [Slice.length]; rw [hs2, Nat.mod_self]
      · have hp : p.length = q.length + bw.used.val := by rw [← hqp]; simp; omega
        simp only [Slice.length] at hb hlong ⊢
        rw [hs2]; omega
      · refine ⟨q ++ s2.val, state2_post, ?_, ?_⟩
        · rw [h2, head_post3, head_post2, ← hqp]
          simp only [List.append_assoc]
          rw [List.take_append_drop]
        · have := head_post1
          simp only [Slice.length] at this hlong ⊢
          omega
    · rename_i hpos
      have h0 : bw.used.val = 0 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨q, hq, ?_, by omega⟩
      rw [← hqp, h0]; simp
  · rintro ⟨a, bytes1, state1⟩ ⟨q', hq', hqb, hpos⟩
    simp only at hq' hqb hpos
    have hl1 : bytes1.len.val = bytes1.length := by simp [Slice.len, Slice.length]
    have hdm := Nat.div_mul_le_self (bytes1.length - 1) N.val
    have hmod := Nat.mod_add_div' (bytes1.length - 1) N.val
    have hlt := Nat.mod_lt (bytes1.length - 1) hN
    have hlen := congrArg List.length hqb
    simp only [List.length_append] at hlen
    step*
    apply WP.spec_bind (Pₘ := fun st2 => R (q' ++ whole.val) st2)
    · split
      · rename_i hb0
        have : whole.val = [] := by
          rw [b_post] at hb0; exact List.eq_nil_of_length_eq_zero hb0
        simp only [this, List.append_nil, WP.spec_ok, hq']
      · apply hC _ _ _ hq'
        · rw [whole_post, i3_post]; exact Nat.mul_mod_left _ _
        · have := whole_post
          rw [this, i3_post, i2_post, i1_post, hl1]
          simp only [Slice.length] at *
          omega
    · intro st2 hst2
      step*
      have hrl : rest.val.length = (bytes1.length - 1) % N.val + 1 := by
        have := whole_post1
        rw [i3_post, i2_post, i1_post, hl1] at this
        simp only [Slice.length] at *
        omega
      have hrlen : rest.len.val = rest.val.length := by simp [Slice.len]
      have hml := Nat.mod_lt (bytes1.length - 1) hN
      have hal : a.val.length = N.val := by simp
      refine ⟨?_, q' ++ whole.val, hst2, ?_⟩
      · show rest.len.val ≤ N.val
        omega
      · simp only
        rw [s_post2, s1_post, setSlice!_eq _ _ _ (by omega), hrlen]
        simp only [List.take_zero, List.nil_append, Nat.zero_add]
        rw [List.take_left' rfl, List.append_assoc, whole_post2, whole_post3,
          List.take_append_drop, hqb]

theorem update_spec {S : Type} {N : Usize}
    (inst : low.generic.blockwise.UpdateBlocks S) (R : List U8 → S → Prop) (bound : Nat)
    (hC : ∀ p s (b : Slice U8), R p s → b.length % N.val = 0 → p.length + b.length ≤ bound →
      inst.update_blocks s b ⦃ s' => R (p ++ b.val) s' ⦄)
    (p : List U8) (bw : low.generic.blockwise.Blockwise N) (bytes : Slice U8) (state : S)
    (hB : Buffered R p bw state) (hN : 0 < N.val) (hb : p.length + bytes.length ≤ bound) :
    low.generic.blockwise.Blockwise.update inst bw bytes state ⦃ bw' s' =>
      Buffered R (p ++ bytes.val) bw' s' ⦄ := by
  have hB' := hB
  obtain ⟨hu, q, hq, hqp⟩ := hB'
  have hbl : bw.buffer.val.length = N.val := by simp
  have hl : bytes.len.val = bytes.length := by simp [Slice.len, Slice.length]
  unfold low.generic.blockwise.Blockwise.update
  step*
  case h2 =>
    exact complete_blocks_spec inst R bound hC p bw bytes state hB hN
      (by simp only [UScalar.le_equiv] at *; omega) hb
  · scalar_tac
  · refine ⟨by scalar_tac, q, hq, ?_⟩
    simp only
    rw [s_post2, s1_post, setSlice!_eq _ _ _ (by scalar_tac),
      List.take_left' (by simp; scalar_tac), ← hqp, List.append_assoc]

theorem buffered_spec {N : Usize} (bw : low.generic.blockwise.Blockwise N) (h : bw.used.val ≤ N.val) :
    low.generic.blockwise.Blockwise.buffered bw ⦃ s => s.val = bw.buffer.val.take bw.used.val ⦄ := by
  unfold low.generic.blockwise.Blockwise.buffered
  step*
  simp_all [List.slice]

/-! ## Hash values over whole blocks -/

/-- Translated bytes as the spec reads them. -/
def bv (l : List U8) : List Byte := l.map (·.bv)

theorem bv_length (x : List U8) : (bv x).length = x.length := List.length_map ..

theorem bv_inj (x y : List U8) : bv x = bv y ↔ x = y := by
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun a b hab => by cases a; cases b; simp_all) h
  · rintro rfl; rfl

/-- Translated words as the spec reads them. -/
def words (l : List U32) : List (BitVec 32) := l.map (·.bv)

theorem blocks_nil (n : Nat) : rind.spec.blocks n [] = [] := by
  unfold rind.spec.blocks; simp; omega

theorem blocks_append {n : Nat} (hn : 0 < n) (a b : List Byte) (ha : a.length % n = 0) :
    rind.spec.blocks n (a ++ b) = rind.spec.blocks n a ++ rind.spec.blocks n b := by
  induction h : a.length using Nat.strong_induction_on generalizing a with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have : a = [] := List.eq_nil_of_length_eq_zero h
      subst this
      rw [List.nil_append, blocks_nil, List.nil_append]
    · have hka : n ≤ a.length := by
        have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero ha); omega
      rw [rind.spec.blocks, ite_eq_left ⟨hn, by simp; omega⟩, rind.spec.blocks.eq_def n a,
        ite_eq_left ⟨hn, hka⟩, List.take_append_of_le_length hka, List.drop_append_of_le_length hka,
        ih (k - n) (by omega) (a.drop n) (by simp; rw [Nat.sub_mod_eq_zero_of_mod_eq]; simp [ha]) (by simp; omega)]
      rfl

/-- A routine that adds whole blocks to a hash value as `compress`, a block
function, does. -/
def Compresses {n : Usize} (compress : List (BitVec 32) → List Byte → List (BitVec 32))
    (f : Std.Array U32 n → Slice U8 → Result (Std.Array U32 n)) : Prop :=
  ∀ h (b : Slice U8), b.length % 64 = 0 →
    f h b ⦃ h' => words h'.val = (rind.spec.blocks 64 (bv b.val)).foldl compress (words h.val) ⦄

/-- Hash value `h` has absorbed `p`, whole blocks from `h0` by `compress`. -/
def Absorbed {n : Usize} (compress : List (BitVec 32) → List Byte → List (BitVec 32))
    (h0 : List (BitVec 32)) (p : List U8) (h : Std.Array U32 n) : Prop :=
  words h.val = (rind.spec.blocks 64 (bv p)).foldl compress h0 ∧ p.length % 64 = 0

theorem absorbed_append {n : Usize} {compress : List (BitVec 32) → List Byte → List (BitVec 32)}
    {h0 : List (BitVec 32)} {p : List U8} {h h' : Std.Array U32 n} {b : List U8}
    (hR : Absorbed compress h0 p h) (hb : b.length % 64 = 0)
    (hh : words h'.val = (rind.spec.blocks 64 (bv b)).foldl compress (words h.val)) :
    Absorbed compress h0 (p ++ b) h' := by
  refine ⟨?_, by simp [Nat.add_mod, hR.2, hb]⟩
  rw [hh, hR.1]
  unfold bv
  rw [List.map_append, blocks_append (by decide) _ _ (by simp [hR.2]), List.foldl_append]

/-! ## SHA-256's digest -/

/-- The bytes `u32::to_be_bytes` writes. -/
def beBytes32 (w : U32) : List U8 := w.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)

theorem sha256_digest_loop_spec
    (it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Std.U32))
    (r : Std.Array U8 32#usize) (V : List U32) (hVl : V.length = 8)
    (hV : it.iter.slice.val = V) (hi : it.iter.i = it.count.val) (hk : it.count.val ≤ 8)
    (hr : r.val.take (4 * it.count.val) = (V.take it.count.val).flatMap beBytes32) :
    low.generic.blockwise.sha256_digest_loop it r ⦃ r' => r'.val = V.flatMap beBytes32 ⦄ := by
  unfold low.generic.blockwise.sha256_digest_loop
  apply loop.spec_decr_nat (fun x => 8 - x.1.count.val)
    (fun x => x.1.iter.slice.val = V ∧ x.1.iter.i = x.1.count.val ∧ x.1.count.val ≤ 8 ∧
      x.2.val.take (4 * x.1.count.val) = (V.take x.1.count.val).flatMap beBytes32)
  · rintro ⟨it, r⟩ ⟨hV, hi, hk, hr⟩
    simp only at hV hi hk hr ⊢
    unfold low.generic.blockwise.sha256_digest_loop.body
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorSliceIter.next]
    have hsl : it.iter.slice.len.val = 8 := by simp [Slice.len, hV, hVl]
    split
    · rename_i hlt
      have hk4 : it.count.val < 8 := by omega
      step*
      · rw [s_post1, s1_post]
        simp [i3_post, i2_post, i1_post, Slice.length]
        omega
      · have ha8 : (a.val).length = 4 := a.property
        have hw : it.iter.slice[it.iter.i] = V[it.count.val] := by
          subst hV
          show it.iter.slice.val[it.iter.i]'(by simp [Slice.len] at hlt; omega) = _
          simp only [hi]
        refine ⟨hV, by omega, by omega, ?_, by omega⟩
        rw [s_post2, s2_post, s1_post]
        have hr32 : (r.val).length = 32 := r.property
        have := rind.spec.take_setSlice! r.val a.val (i1.val) (by rw [ha8, i1_post]; omega)
        simp only [Array.val_to_slice, ha8] at this ⊢
        rw [show 4 * x.val = i1.val + 4 by rw [x_post, i1_post]; ring, this, i1_post,
          show it.count.val * 4 = 4 * it.count.val by ring, hr, x_post, List.take_add_one,
          List.flatMap_append, List.getElem?_eq_getElem (by omega)]
        simp [a_post, hw, beBytes32]
    · rename_i hlt
      have hk4 : it.count.val = 8 := by omega
      have hr32 : (r.val).length = 32 := r.property
      rw [hk4, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hr
      simpa [WP.spec_ok] using hr
  · exact ⟨hV, hi, hk, hr⟩

theorem bv_flatMap_beBytes (V : List U32) :
    bv (V.flatMap beBytes32) = (words V).flatMap BitVec.toBEBytes := by
  induction V with
  | nil => rfl
  | cons w V ih =>
    simp only [List.flatMap_cons, bv, List.map_append, words, List.map_cons] at ih ⊢
    rw [ih]
    simp [beBytes32, List.map_map, Function.comp_def]

/-- The digest is the hash value's words, big-endian. -/
theorem sha256_digest_spec (h : Std.Array U32 8#usize) :
    low.generic.blockwise.sha256_digest h ⦃ r =>
      bv r.val = (words h.val).flatMap BitVec.toBEBytes ⦄ := by
  unfold low.generic.blockwise.sha256_digest
  simp only [core.slice.Slice.iter]
  step*
  have hv : (h.val).length = 8 := h.property
  apply WP.spec_mono (sha256_digest_loop_spec iter _ h.val hv ?_ ?_ ?_ ?_)
  · intro r hr
    rw [hr, bv_flatMap_beBytes]
  all_goals simp [iter_post, iter_post1, s_post, Array.val_to_slice]

/-- SHA-256's digest of `P`, whole blocks, then `m`, padded and closed by
`length`. -/
def sha256Finished (P m length : List U8) : List Byte :=
  ((rind.spec.blocks 64 (bv (P ++ m ++ [128#u8] ++ List.replicate (padZeros 64 8 m.length) 0#u8 ++
    length))).foldl rind.spec.sha256.compress rind.spec.sha256.H0).flatMap BitVec.toBEBytes

/-- A routine's digest from a hash value that has absorbed `P`, over whole
blocks `b` and then `rest`, is `P`'s followed by `b ++ rest`. -/
theorem sha256Finished_split {P b rest length : List U8} {state : Std.Array U32 8#usize}
    (hR : Absorbed rind.spec.sha256.compress rind.spec.sha256.H0 P state) (hb : b.length % 64 = 0) :
    ((rind.spec.blocks 64 (bv (b ++ rest ++ [128#u8] ++
      List.replicate (padZeros 64 8 rest.length) 0#u8 ++ length))).foldl rind.spec.sha256.compress
        (words state.val)).flatMap BitVec.toBEBytes = sha256Finished P (b ++ rest) length := by
  have hz : padZeros 64 8 (b ++ rest).length = padZeros 64 8 rest.length := by
    have := padZeros_sub (N := 64) (L := 8) (n := (b ++ rest).length) (start := b.length) hb
      (by simp)
    rw [← this]
    simp
  unfold sha256Finished
  rw [hz, hR.1, ← List.foldl_append, ← blocks_append (by decide) _ _ (by simp [bv, hR.2])]
  simp [bv, List.map_append, List.append_assoc]

end rind.x86_64
