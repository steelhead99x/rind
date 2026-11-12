import Rind.X86_64.RsaMont
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# RSA's public operation on x86_64

`RsaPublicKey::public_op` raises a signature to the public exponent modulo
the modulus by square-and-multiply in the Montgomery domain, over whichever
Montgomery products `MontProducts` states.
-/

namespace rind.x86_64

abbrev RsaInt := low.posint.PosInt 128#usize

/-- The words of `p` below `k`. -/
def lowWords {N : Usize} (p : low.posint.PosInt N) (k : Nat) : List U64 := p.words.val.take k

theorem getElem!_set_of_lt {α : Type} [Inhabited α] (l : List α) (i p : Nat) (a : α) (hp : p < l.length) :
    (l.set i a)[p]! = if p = i then a else l[p]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = p
  · subst h; simp [hp]
  · simp [h, Ne.symm h]

theorem take_setSlice_zero {α : Type} (l s : List α) (h : s.length ≤ l.length) :
    (l.setSlice! 0 s).take s.length = s := by
  simp [List.setSlice!, Nat.min_eq_left h]

theorem drop_setSlice_zero {α : Type} (l s : List α) (h : s.length ≤ l.length) :
    (l.setSlice! 0 s).drop s.length = l.drop s.length := by
  simp [List.setSlice!, Nat.min_eq_left h]

/-- A Montgomery product into `out` sets its words below `n`'s width, which
`f` returns, and keeps the rest. -/
theorem mont_into_post (out n : RsaInt) (back : Slice U64 → Std.Array U64 128#usize)
    (hback : ∀ s' : Slice U64, (back s').val = out.words.val.setSlice! 0 s'.val)
    (hk : n.used.val ≤ 128) (s3 : Slice U64) (hs3 : s3.length = n.used.val) :
    lowWords ({ words := back s3, used := n.used } : RsaInt) n.used = s3.val ∧
      List.drop n.used.val (back s3).val = List.drop n.used.val out.words.val := by
  have hl : s3.val.length ≤ out.words.val.length := by simp [Slice.length] at hs3; simp; omega
  have hs3' : s3.val.length = n.used.val := hs3
  refine ⟨?_, ?_⟩
  · simp only [lowWords, hback, ← hs3']; exact take_setSlice_zero _ _ hl
  · rw [hback, ← hs3']; exact drop_setSlice_zero _ _ hl

theorem mont_sqr_into_spec (self out n : RsaInt) (n0 : U64) (hP : MontProducts n.used.val)
    (hk : n.used.val ≤ 128)
    (hargs : MontArgs (lowWords self n.used) (lowWords self n.used) (lowWords n n.used) n0) :
    low.posint.PosInt.mont_sqr_into self out n n0 ⦃ r =>
      r.used = n.used ∧
      MontResult (lowWords self n.used) (lowWords self n.used) (lowWords n n.used) (lowWords r n.used) ∧
      r.words.val.drop n.used = out.words.val.drop n.used ⦄ := by
  unfold low.posint.PosInt.mont_sqr_into low.posint.PosInt.as_mut_words
    low.posint.PosInt.as_words_with_len_of low.posint.PosInt.as_words
  have hsq := hP.2
  step*
  obtain ⟨s, back⟩ := x
  dsimp only at *
  step*
  · simpa [lowWords, s1_post, s2_post] using hargs
  · obtain ⟨h1, h2⟩ := mont_into_post out n back x_post2 hk s3 (by have := s3_post.1; simp only [Slice.length] at this s2_post1 ⊢; omega)
    refine ⟨?_, h2⟩
    rw [h1]
    simpa [lowWords, s1_post, s2_post] using s3_post

theorem mont_mul_into_spec (self v out n : RsaInt) (n0 : U64) (hP : MontProducts n.used.val)
    (hk : n.used.val ≤ 128)
    (hargs : MontArgs (lowWords self n.used) (lowWords v n.used) (lowWords n n.used) n0) :
    low.posint.PosInt.mont_mul_into self v out n n0 ⦃ r =>
      r.used = n.used ∧
      MontResult (lowWords self n.used) (lowWords v n.used) (lowWords n n.used) (lowWords r n.used) ∧
      r.words.val.drop n.used = out.words.val.drop n.used ⦄ := by
  unfold low.posint.PosInt.mont_mul_into low.posint.PosInt.as_mut_words
    low.posint.PosInt.as_words_with_len_of low.posint.PosInt.as_words
  have hmul := hP.1
  step*
  obtain ⟨s, back⟩ := x
  dsimp only at *
  step*
  · simpa [lowWords, s1_post, s2_post, s3_post] using hargs
  · obtain ⟨h1, h2⟩ := mont_into_post out n back x_post2 hk s4 (by have := s4_post.1; simp only [Slice.length] at this s3_post1 ⊢; omega)
    refine ⟨?_, h2⟩
    rw [h1]
    simpa [lowWords, s1_post, s2_post, s3_post] using s4_post

/-! ## Square-and-multiply, `public_op`'s loop -/

theorem lowWords_length (p : RsaInt) {k : Nat} (hk : k ≤ 128) : (lowWords p k).length = k := by
  simp [lowWords]; omega

/-- A Montgomery product's arguments, from their values. -/
theorem mont_args_of (x y n : RsaInt) (n0 : U64) (hk : n.used.val ≤ 128) (hk2 : 2 ≤ n.used.val)
    (hodd : wordsNat (lowWords n n.used) % 2 = 1)
    (hn0 : (wordsNat (lowWords n n.used) * n0.val + 1) % 2 ^ 64 = 0)
    (hx : wordsNat (lowWords x n.used) < wordsNat (lowWords n n.used))
    (hy : wordsNat (lowWords y n.used) < wordsNat (lowWords n n.used)) :
    MontArgs (lowWords x n.used) (lowWords y n.used) (lowWords n n.used) n0 := by
  refine ⟨?_, ?_, ?_, hodd, hn0, hx, hy⟩ <;> simp only [lowWords_length _ hk] <;> omega

/-- A Montgomery product's result, as a congruence. -/
theorem mont_result_of {x y m r : List U64} (h : MontResult x y m r) :
    wordsNat r < wordsNat m ∧ wordsNat r * 2 ^ (64 * m.length) ≡ wordsNat x * wordsNat y [MOD wordsNat m] :=
  ⟨h.2.1, h.2.2⟩

/-- `e &&& (1 << bit)` is `1 << bit` when `e`'s bit is set. -/
theorem and_mask_eq (e mask : U64) (bit : Nat) (hm : mask.val = 2 ^ bit) :
    (e &&& mask) = mask ↔ e.val / 2 ^ bit % 2 = 1 := by
  rw [UScalar.eq_equiv, UScalar.val_and, hm, Nat.and_two_pow, Nat.testBit_eq_decide_div_mod_eq]
  constructor
  · intro h
    by_contra hb
    simp [hb] at h
  · intro h; simp [h]


@[step]
theorem rev_next_u32_spec (r : core.iter.adapters.rev.Rev (core.ops.range.Range U32)) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepU32) r ⦃ o r' =>
      r'.iter.start = r.iter.start ∧
        (if r.iter.start.val < r.iter.end.val then o = some r'.iter.end ∧ r'.iter.end.val + 1 = r.iter.end.val
          else o = none) ⦄ := by
  unfold core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  simp only [
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back, core.iter.range.StepU32,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.backward_checked]
  by_cases hlt : r.iter.start.val < r.iter.end.val
  · have hb : liftFun2 core.cmp.impls.PartialOrdU32.lt r.iter.start r.iter.end = ok true := by
      simp [liftFun2, core.cmp.impls.PartialOrdU32.lt, hlt]
    have h1 : (1#usize).val ≤ r.iter.end.val := by simp; omega
    simp only [hb, bind_ok, ↓reduceIte, hlt]
    rw [dite_eq_left_of_eq_true (eq_true h1)]
    simp [UScalar.ofNatCore_val_eq]; omega
  · have hb : liftFun2 core.cmp.impls.PartialOrdU32.lt r.iter.start r.iter.end = ok false := by
      simp [liftFun2, core.cmp.impls.PartialOrdU32.lt, hlt]
    simp [hb, hlt, WP.spec_ok]

/-- What `public_op`'s loop keeps, with `j` of `e`'s bits left: its
accumulator, `a` or `b` as `in_a` says, is `C^(e / 2^j)` in the Montgomery
domain, or `C^e` out of it once the last bit is done, and both are zero
above the modulus's width. -/
def ExpInv (n : RsaInt) (e : Nat) (C : Nat) (j : Nat) (a b : RsaInt) (in_a : Bool) : Prop :=
  let k := n.used.val
  let N := wordsNat (lowWords n k)
  let acc := if in_a then a else b
  acc.used = n.used ∧ wordsNat (lowWords acc k) < N ∧
    (if j = 0 then wordsNat (lowWords acc k) ≡ C ^ e [MOD N]
      else wordsNat (lowWords acc k) ≡ C ^ (e / 2 ^ j) * 2 ^ (64 * k) [MOD N])

set_option hygiene false in
/-- The rest of an iteration of `public_op`'s loop, once the square `sq` is
in the accumulator and `other` is spare: tests the bit and, when set,
multiplies, by `c` for the last bit and `c_mont` for any other. -/
local macro "exp_bit" sq:ident other:ident hu:ident hN:ident : tactic => `(tactic| (
  step as ⟨mask, hmask1, hmask⟩
  step as ⟨i2, hi2, hi2'⟩
  have hmaskv : mask.val = 2 ^ j := by
    rw [hmask1, ← hj, Nat.one_shiftLeft]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (show j < 64 by omega))
      (by simp [U64.size, U64.numBits]))
  have hbitiff : i2 = mask ↔ e.val / 2 ^ j % 2 = 1 := by
    rw [show i2 = e &&& mask by rw [UScalar.eq_equiv]; exact hi2]; exact and_mask_eq e mask j hmaskv
  split
  · rename_i hset
    have hb1 := hbitiff.mp hset
    split
    · rename_i hz
      have hj0 : j = 0 := by rw [UScalar.eq_equiv] at hz; simp at hz; omega
      simp only [bind_ok, Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte]
      step with mont_mul_into_spec $sq c $other n n0 hP hk (mont_args_of $sq c n n0 hk hk2 hodd hn0 $hN hc)
        as ⟨r, hru, hrr, _⟩
      obtain ⟨hrN, hrv⟩ := mont_result_of hrr
      rw [hmlen] at hrv
      have hM := mont_exp_out hR hS hrv
      have hexp : 2 * (e.val / 2 ^ (j + 1)) + 1 = e.val := by
        have h := hdiv; rw [hb1] at h; rw [← h, hj0, pow_zero, Nat.div_one]
      rw [hexp] at hM
      refine ⟨by rw [hst]; exact hs, by omega, ?_, by omega⟩
      simp only [ExpInv, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
      refine ⟨hru, hrN, ?_⟩
      rw [← hj]
      simp only [hj0, ↓reduceIte]
      exact hM
    · rename_i hz
      have hj0 : j ≠ 0 := by rw [UScalar.eq_equiv] at hz; simp at hz; omega
      simp only [bind_ok, Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte]
      step with mont_mul_into_spec $sq cm $other n n0 hP hk (mont_args_of $sq cm n n0 hk hk2 hodd hn0 $hN hcm)
        as ⟨r, hru, hrr, _⟩
      obtain ⟨hrN, hrv⟩ := mont_result_of hrr
      rw [hmlen] at hrv
      have hM := mont_exp_mul hR hS hcmv hrv
      have hexp : e.val / 2 ^ j = 2 * (e.val / 2 ^ (j + 1)) + 1 := by
        have h := hdiv; rw [hb1] at h; exact h
      refine ⟨by rw [hst]; exact hs, by omega, ?_, by omega⟩
      simp only [ExpInv, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
      refine ⟨hru, hrN, ?_⟩
      rw [← hj]
      simp only [hj0, ↓reduceIte, hexp]
      exact hM
  · rename_i hnot
    have hb0 : e.val / 2 ^ j % 2 = 0 := by have := mt hbitiff.mpr hnot; omega
    have hj0 : j ≠ 0 := by
      intro h0; rw [h0, pow_zero, Nat.div_one] at hb0; omega
    have hexp : e.val / 2 ^ j = 2 * (e.val / 2 ^ (j + 1)) := by
      have h := hdiv; rw [hb0, Nat.add_zero] at h; exact h
    simp only [WP.spec_ok]
    refine ⟨by rw [hst]; exact hs, by omega, ?_, by omega⟩
    simp only [ExpInv, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true, Bool.not_true,
      Bool.not_false]
    refine ⟨$hu, $hN, ?_⟩
    rw [← hj]
    simp only [hj0, ↓reduceIte, hexp]
    exact hS))

theorem public_op_loop_spec (n : RsaInt) (e n0 : U64) (c cm : RsaInt)
    (hP : MontProducts n.used.val) (hk : n.used.val ≤ 128) (hk2 : 2 ≤ n.used.val)
    (hodd : wordsNat (lowWords n n.used) % 2 = 1)
    (hn0 : (wordsNat (lowWords n n.used) * n0.val + 1) % 2 ^ 64 = 0)
    (he : e.val % 2 = 1)
    (hc : wordsNat (lowWords c n.used) < wordsNat (lowWords n n.used))
    (hcm : wordsNat (lowWords cm n.used) < wordsNat (lowWords n n.used))
    (hcmv : wordsNat (lowWords cm n.used) ≡ wordsNat (lowWords c n.used) * 2 ^ (64 * n.used.val)
      [MOD wordsNat (lowWords n n.used)])
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range U32)) (hs : iter.iter.start.val = 0)
    (hend : iter.iter.end.val < 64) (a b : RsaInt) (in_a : Bool)
    (hinv : ExpInv n e.val (wordsNat (lowWords c n.used)) iter.iter.end.val a b in_a) :
    mid.rsa_pub.RsaPublicKey.public_op_loop iter n e n0 c cm a b in_a ⦃ r =>
      ExpInv n e.val (wordsNat (lowWords c n.used)) 0 r.1 r.2.1 r.2.2 ⦄ := by
  unfold mid.rsa_pub.RsaPublicKey.public_op_loop
  apply loop.spec_decr_nat (fun x => x.1.iter.end.val)
    (fun x => x.1.iter.start.val = 0 ∧ x.1.iter.end.val < 64 ∧
      ExpInv n e.val (wordsNat (lowWords c n.used)) x.1.iter.end.val x.2.1 x.2.2.1 x.2.2.2)
  · rintro ⟨it, a1, b1, in1⟩ ⟨hs, he, hinv⟩
    simp only at hs he hinv
    unfold mid.rsa_pub.RsaPublicKey.public_op_loop.body
    step as ⟨o, iter1, hst, ho⟩
    cases o with
    | none =>
      have h0 : it.iter.end.val = 0 := by
        split at ho
        · simp at ho
        · omega
      rw [h0] at hinv
      simpa using hinv
    | some bit =>
      have hlt : it.iter.start.val < it.iter.end.val := by
        by_contra hc; simp [hc] at ho
      simp only [hlt, ↓reduceIte, Option.some.injEq] at ho
      obtain ⟨rfl, hbe⟩ := ho
      set j := iter1.iter.end.val with hj
      clear_value j
      set k := n.used.val
      set N := wordsNat (lowWords n n.used)
      set C := wordsNat (lowWords c n.used)
      have hR : Nat.Coprime (2 ^ (64 * k)) N := coprime_two_pow_odd hodd _
      have hmlen : (lowWords n n.used).length = k := lowWords_length n hk
      have hdiv := div_two_pow_succ e.val j
      rw [← hbe] at hinv
      cases in1
      · simp only [ExpInv, Bool.false_eq_true, ↓reduceIte, show j + 1 ≠ 0 by omega] at hinv
        obtain ⟨hbu, hbN, hbC⟩ := hinv
        simp only [Bool.false_eq_true, ↓reduceIte]
        step with mont_sqr_into_spec b1 a1 n n0 hP hk (mont_args_of b1 b1 n n0 hk hk2 hodd hn0 hbN hbN)
          as ⟨a2, ha2u, ha2r, _⟩
        obtain ⟨ha2N, ha2v⟩ := mont_result_of ha2r
        rw [hmlen] at ha2v
        have hS := mont_exp_sqr hR hbC ha2v
        exp_bit a2 b1 ha2u ha2N
      · simp only [ExpInv, ↓reduceIte, show j + 1 ≠ 0 by omega] at hinv
        obtain ⟨hau, haN, haC⟩ := hinv
        simp only [↓reduceIte]
        step with mont_sqr_into_spec a1 b1 n n0 hP hk (mont_args_of a1 a1 n n0 hk hk2 hodd hn0 haN haN)
          as ⟨b2, hb2u, hb2r, _⟩
        obtain ⟨hb2N, hb2v⟩ := mont_result_of hb2r
        rw [hmlen] at hb2v
        have hS := mont_exp_sqr hR haC hb2v
        exp_bit b2 a1 hb2u hb2N
  · exact ⟨hs, hend, hinv⟩

/-! ## `public_op` -/

theorem less_than_spec (x y : RsaInt) (hx : x.used.val ≤ 128) (hy : y.used.val ≤ 128) :
    low.posint.PosInt.less_than x y ⦃ b =>
      b = decide (wordsNat (lowWords x x.used) < wordsNat (lowWords y y.used)) ⦄ := by
  unfold low.posint.PosInt.less_than low.posint.PosInt.as_words
  step*
  have hs : s.val = lowWords x x.used := by simp [lowWords, s_post]
  have hs1 : s1.val = lowWords y y.used := by simp [lowWords, s1_post]
  rw [hs, hs1] at i_post
  by_cases h : wordsNat (lowWords x x.used) < wordsNat (lowWords y y.used)
  · simp only [h, ↓reduceIte] at i_post
    simp only [h, decide_true, decide_eq_true_eq]; scalar_tac
  · simp only [h, ↓reduceIte] at i_post
    simp only [h, decide_false, decide_eq_false_iff_not]; scalar_tac

@[step]
theorem clone_spec {N : Usize} (x : low.posint.PosInt N) :
    low.posint.PosInt.Insts.CoreCloneClone.clone x ⦃ r => r = x ⦄ := by
  unfold low.posint.PosInt.Insts.CoreCloneClone.clone
  step*
  subst a_post
  simp [core.clone.impls.CloneUsize.clone, lift, WP.spec_ok]

@[step]
theorem ilog2_spec (x : U64) (hx : x.val ≠ 0) :
    core.num.U64.ilog2 x ⦃ r => r.val = x.val.log2 ⦄ := by
  unfold core.num.U64.ilog2
  simp only [hx, ↓reduceIte, WP.spec_ok]
  have h64 : x.val.log2 < 64 := (Nat.log2_lt hx).mpr (by have := x.hBounds; simpa using this)
  show (BitVec.ofNat 32 x.val.log2).toNat = _
  rw [BitVec.toNat_ofNat]; omega

theorem mont_neg_inverse_spec (n : RsaInt) (hk : 1 ≤ n.used.val) (hk' : n.used.val ≤ 128)
    (hodd : wordsNat (lowWords n n.used) % 2 = 1) :
    low.posint.PosInt.mont_neg_inverse n ⦃ r =>
      (wordsNat (lowWords n n.used) * r.val + 1) % 2 ^ 64 = 0 ⦄ := by
  unfold low.posint.PosInt.mont_neg_inverse
  step*
  have hslen : s.length = 1 := by simp [Slice.length, s_post]
  have hs2 : s2.val = [r] := by
    have hl : s2.val.length = 1 := by simpa [Slice.length, hslen] using s2_post
    obtain ⟨w, hw⟩ := List.length_eq_one_iff.mp hl
    simp [to_slice_mut_back_post, Array.from_slice_val _ _ (show s2.val.length = (1#usize).val by simpa using hl),
      hw] at r_post
    rw [hw, r_post]
  have hs1 : wordsNat s1.val = wordsNat n.words.val % 2 ^ 64 := by
    simp [s1_post, wordsNat_take_mod]
  have hN : wordsNat (lowWords n n.used) % 2 ^ 64 = wordsNat n.words.val % 2 ^ 64 := by
    rw [lowWords, wordsNat_take_mod, Nat.mod_mod_of_dvd]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hodd1 : wordsNat s1.val % 2 = 1 := by
    rw [hs1, Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2 ^ 64), ← Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2 ^ 64), ← hN,
      Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2 ^ 64), hodd]
  have h := s2_post1 hodd1
  rw [hslen, hs2, wordsNat_cons, wordsNat_nil, hs1, ← hN] at h
  simpa [Nat.add_mod, Nat.mul_mod] using h

/-- What `RsaPublicKey::new` establishes about a key: the modulus `n` of
`k` words is odd, `n0` is `-n⁻¹ mod 2^64`, the montifier is `R² mod n` for
`R = 2^(64k)`, the exponent is odd and above one, and the modulus has 1024
to 8192 bits. -/
def PubKeyInv (key : mid.rsa_pub.RsaPublicKey) : Prop :=
  let k := key.n.used.val
  let N := wordsNat (lowWords key.n k)
  2 ≤ k ∧ k ≤ 128 ∧ N % 2 = 1 ∧ (N * key.n0.val + 1) % 2 ^ 64 = 0 ∧
    wordsNat (lowWords key.montifier k) = 2 ^ (128 * k) % N ∧ key.e.val % 2 = 1 ∧ 3 ≤ key.e.val ∧
    1024 ≤ N.size ∧ N.size ≤ 8192

theorem div_pow_log2 (e : Nat) (he : e ≠ 0) : e / 2 ^ e.log2 = 1 := by
  apply Nat.div_eq_of_lt_le
  · simpa using Nat.log2_self_le he
  · have := Nat.lt_log2_self (n := e); rw [Nat.pow_succ] at this; omega

/-- RSAVP1: `public_op` raises `c` to the public exponent modulo the
modulus, or refuses a `c` not below it. -/
theorem public_op_spec (key : mid.rsa_pub.RsaPublicKey) (hinv : PubKeyInv key)
    (hP : MontProducts key.n.used.val) (c : RsaInt) (hcu : c.used.val ≤ 128)
    (hcz : wordsNat (c.words.val.drop c.used.val) = 0) :
    mid.rsa_pub.RsaPublicKey.public_op key c ⦃ r => match r with
      | .Ok m => wordsNat (lowWords c c.used) < wordsNat (lowWords key.n key.n.used) ∧
          m.used = key.n.used ∧
          wordsNat (lowWords m key.n.used) =
            wordsNat (lowWords c c.used) ^ key.e.val % wordsNat (lowWords key.n key.n.used)
      | .Err _ => wordsNat (lowWords key.n key.n.used) ≤ wordsNat (lowWords c c.used) ⦄ := by
  obtain ⟨hk2, hk, hodd, hn0, hmont, he, he3, _⟩ := hinv
  unfold mid.rsa_pub.RsaPublicKey.public_op
  step with less_than_spec c key.n hcu hk as ⟨b, hb⟩
  unfold low.ct.into_public
  simp only [bind_ok]
  split
  · rename_i hlt
    rw [hb] at hlt
    have hlt : wordsNat (lowWords c c.used) < wordsNat (lowWords key.n key.n.used) := by simpa using hlt
    have hNR : wordsNat (lowWords key.n key.n.used) < 2 ^ (64 * key.n.used.val) := by
      have := wordsNat_lt' (lowWords key.n key.n.used); rwa [lowWords_length _ hk] at this
    have hR : Nat.Coprime (2 ^ (64 * key.n.used.val)) (wordsNat (lowWords key.n key.n.used)) :=
      coprime_two_pow_odd hodd _
    -- `expand` keeps `c`'s value, which its words above `used` hold none of.
    unfold low.posint.PosInt.expand
    have hcw : wordsNat c.words.val = wordsNat (lowWords c c.used) := by
      rw [wordsNat_take_drop c.words.val c.used, hcz, Nat.mul_zero, Nat.add_zero]; rfl
    have hc1 : wordsNat (lowWords ({ c with used := key.n.used } : RsaInt) key.n.used) =
        wordsNat (lowWords c c.used) := by
      simp only [lowWords]; rw [wordsNat_take_mod, hcw]
      exact Nat.mod_eq_of_lt (lt_trans hlt hNR)
    -- `to_montgomery` takes `c` to `c·R`.
    unfold low.posint.PosInt.to_montgomery low.posint.PosInt.mont_mul low.posint.PosInt.zero
    step with mont_neg_inverse_spec key.n (by omega) hk hodd as ⟨n0', hn0'⟩
    have hmlt : wordsNat (lowWords key.montifier key.n.used) < wordsNat (lowWords key.n key.n.used) := by
      rw [hmont]; exact Nat.mod_lt _ (by omega)
    step with mont_mul_into_spec _ key.montifier _ key.n n0' hP hk
      (mont_args_of _ _ key.n n0' hk hk2 hodd hn0' (by rw [hc1]; exact hlt) hmlt) as ⟨cm, hcmu, hcmr, _⟩
    obtain ⟨hcmN, hcmv⟩ := mont_result_of hcmr
    rw [lowWords_length _ hk, hc1, hmont] at hcmv
    have hcmC : wordsNat (lowWords cm key.n.used) ≡
        wordsNat (lowWords c c.used) * 2 ^ (64 * key.n.used.val) [MOD wordsNat (lowWords key.n key.n.used)] := by
      apply mont_cancel hR
      refine hcmv.trans ?_
      unfold Nat.ModEq
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      congr 1; ring
    step as ⟨a, ha⟩
    subst ha
    step with ilog2_spec key.e (by omega) as ⟨L, hL⟩
    step as ⟨iter, hiter⟩
    have hL1 : 1 ≤ L.val := by
      rw [hL]; exact Nat.le_log2 (by omega) |>.mpr (by omega)
    have hL64 : L.val < 64 := by
      rw [hL]; exact (Nat.log2_lt (by omega)).mpr (by have := key.e.hBounds; simpa using this)
    step with public_op_loop_spec key.n key.e key.n0 _ a hP hk hk2 hodd hn0 he (by rw [hc1]; exact hlt)
      hcmN (by rw [hc1]; exact hcmC) iter (by rw [hiter]; rfl) (by rw [hiter]; exact hL64) a _ true
      (by
        rw [hiter]
        simp only [ExpInv, ↓reduceIte, show L.val ≠ 0 by omega]
        refine ⟨hcmu, hcmN, ?_⟩
        rw [hL, div_pow_log2 _ (by omega), pow_one, hc1]
        exact hcmC) as ⟨a1, b3, in_a, hres⟩
    simp only [ExpInv, ↓reduceIte, hc1] at hres
    obtain ⟨hu, hN, hv⟩ := hres
    split <;> rename_i hin <;> simp only [hin, ↓reduceIte] at hu hN hv <;> simp only [WP.spec_ok] <;>
      exact ⟨hlt, hu, (Nat.mod_eq_of_lt hN).symm.trans hv⟩
  · rename_i hge
    rw [hb] at hge
    simp only [WP.spec_ok]
    simpa using hge

end rind.x86_64
