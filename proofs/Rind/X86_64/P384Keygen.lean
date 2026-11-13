import Rind.X86_64.P384
import Rind.P384Comb
import Rind.X86_64.P384Table
open Aeneas Aeneas.Std Result rind.spec rind.spec.comb384

/-!
# P-384 key generation, proven from rind's comb to s2n-bignum's contracts

`p384_generate`, `p384_from_scalar`, and `p384_public_key` state what the
agreement API's P-384 keys hold, through the dispatch `Rind.X86_64.Dispatch`
models and the draws `Rind.X86_64.P384Dispatch` models: a scalar in [1, n)
and X9.62's encoding of that scalar times G.

rind computes k·G with `JacobianMontPoint::base_multiply`, the comb whose
arithmetic `Rind.P384Comb` proves, over the tables `Rind.X86_64.P384Table`
checks, adding with s2n-bignum's `p384_montjmixadd` and doubling with its
`p384_montjdouble`. Their contracts need the points they add to differ,
which `comb_ne` proves for a scalar below n.

The theorems take `AffSelect`, what the table lookup computes, as a
hypothesis: rind's AVX2, SSE2, and NEON selects are not modelled yet.
`admin/prove` writes the aarch64 proof from this file by renaming the target.
-/

set_option exponentiation.threshold 400

namespace rind.x86_64

/-! ## What the theorems state -/

/-- `b` is X9.62's uncompressed encoding of `d` times the generator. -/
def p384PublicKey (d : Nat) (b : List U8) : Prop :=
  b.length = 97 ∧ b.head? = some 4#u8 ∧ p384Pow p384G d = some (p384Coords b)

/-- `key` is a P-384 key whose scalar is `d`, holding its public key: X9.62's
uncompressed encoding of `d` times the generator. -/
def p384Key (d : Nat) (key : high.agreement.PrivateKey) : Prop :=
  ∃ k : high.agreement.Keyed high.curve.P384 mid.p384.PrivateKey, key.«private» = .P384 k ∧
    wordsNat k.key.scalar.val = d ∧
    high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref key.«public» ⦃ b =>
      p384PublicKey d b.val ⦄

/-- P-384 key generation's outcome, for the system source's successive
draws: a `p384Key` whose scalar is the first of `n` draws, from the `i`th,
whose bytes, read big-endian, are in [1, n), unless a draw fails first;
refused if none is. -/
def p384Keygen (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8) (i : Nat) :
    Nat → core.result.Result high.agreement.PrivateKey error.Error → Prop
  | 0, key => key = .Err .RngFailed
  | n + 1, key =>
    match draws i with
    | (.Err _, _) => key = .Err .RngFailed
    | (.Ok _, out) =>
      if 0 < beNat out.val ∧ beNat out.val < n384 then
        ∃ key', key = .Ok key' ∧ p384Key (beNat out.val) key'
      else p384Keygen draws (i + 1) n key

namespace P384

/-- What `bignum_aff_point_select_p384` computes, viewing `table` as 16 rows
of 12 words: row `index`, counting from 1, or zeros for any other index.
rind selects with SIMD vectors (AVX2 or SSE2 on x86-64, NEON on Arm), through
raw-pointer loads Aeneas cannot translate, and no hand model of them is proven
yet, so the theorems below take this as a hypothesis. -/
def AffSelect : Prop :=
  ∀ (z : Std.Array U64 12#usize) (table : Slice U64) (index : U8), table.length = 192 →
    low.x86_64.bignum_point_select.bignum_aff_point_select_p384 z table index ⦃ r =>
      r.val = if 1 ≤ index.val ∧ index.val ≤ 16 then (table.val.drop (12 * (index.val - 1))).take 12
        else List.replicate 12 0#u64 ⦄

/-! ## Limbs -/

theorem wordsNat_inj : ∀ (a b : List U64), a.length = b.length → wordsNat a = wordsNat b → a = b
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    simp only [wordsNat, List.map_cons, Nat.ofDigits_cons] at h
    have hx := x.hBounds
    have hy := y.hBounds
    simp only [UScalarTy.numBits] at hx hy
    have e : x.val = y.val := by omega
    have e' : wordsNat xs = wordsNat ys := by simp only [wordsNat]; omega
    rw [UScalar.eq_of_val_eq e, wordsNat_inj xs ys (by simpa using hl) e']

/-! ## Selects and negation -/

/-- Indexing an array with `..`, as `&a[..]` and `&mut a[..]` do. -/
theorem full_index {T : Type} {N : Usize} (a : Std.Array T N) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFullSlice T)) a () =
        ok a.to_slice ∧
      core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeFullSlice T)) a () =
        ok (a.to_slice, fun s => Std.Array.from_slice a s) := by
  simp [core.array.Array.index, core.array.Array.index_mut, core.ops.index.IndexSlice,
    core.ops.index.IndexMutSlice, core.slice.index.Slice.index, core.slice.index.Slice.index_mut]

/-- A slice `bignum_mux` filled, written back over an array, is the array whose
limbs it holds. -/
theorem from_slice_of_wordsNat {N : Usize} (a q : Std.Array U64 N) (r : Slice U64) (hl : r.length = N.val)
    (h : wordsNat r.val = wordsNat q.val) : a.from_slice r = q := by
  have hl' : r.val.length = N.val := by simpa [Slice.length] using hl
  apply Std.Array.ext
  rw [Array.from_slice_val _ _ (by simp [hl']), wordsNat_inj r.val q.val (by rw [hl', q.property]) h]

@[step]
theorem jac_select_spec (p0 p1 : mid.p384.JacobianMontPoint) (s : U8) :
    mid.p384.JacobianMontPoint.select p0 p1 s ⦃ r => r = if s.val = 0 then p0 else p1 ⦄ := by
  unfold mid.p384.JacobianMontPoint.select mid.p384.JacobianMontPoint.zero
  simp only [full_index]
  step as ⟨sel, hsel⟩
  step with bignum_mux_spec sel (Array.repeat 18#usize 0#u64).to_slice p1.xyz.to_slice p0.xyz.to_slice
    (by simp) (by simp) as ⟨r, hrl, hrv⟩
  have hs : sel.val = s.val := by rw [hsel, UScalar.cast_val_eq]; scalar_tac
  have hl : r.length = (18#usize).val := by simpa using hrl
  rw [hs] at hrv
  by_cases h0 : s.val = 0
  · simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte, Array.val_to_slice] at hrv ⊢
    rw [from_slice_of_wordsNat _ p0.xyz r hl hrv]
  · simp only [h0, ne_eq, not_false_eq_true, ↓reduceIte, Array.val_to_slice] at hrv ⊢
    rw [from_slice_of_wordsNat _ p1.xyz r hl hrv]

@[step]
theorem fe_select_spec (p0 p1 : mid.p384.FieldElement) (s : U8) :
    mid.p384.FieldElement.select p0 p1 s ⦃ r => r = if s.val = 0 then p0 else p1 ⦄ := by
  unfold mid.p384.FieldElement.select mid.p384.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  simp only [full_index, bind_ok]
  step as ⟨sel, hsel⟩
  step with bignum_mux_spec sel (Array.repeat 6#usize core.default.DefaultU64.default).to_slice
    p1.to_slice p0.to_slice (by simp) (by simp) as ⟨r, hrl, hrv⟩
  have hs : sel.val = s.val := by rw [hsel, UScalar.cast_val_eq]; scalar_tac
  have hl : r.length = (6#usize).val := by simpa using hrl
  rw [hs] at hrv
  by_cases h0 : s.val = 0
  · simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte, Array.val_to_slice] at hrv ⊢
    exact from_slice_of_wordsNat _ p0 r hl hrv
  · simp only [h0, ne_eq, not_false_eq_true, ↓reduceIte, Array.val_to_slice] at hrv ⊢
    exact from_slice_of_wordsNat _ p1 r hl hrv

@[step]
theorem fe_negate_spec (a : mid.p384.FieldElement) (ha : feNat a ≤ p384) :
    mid.p384.FieldElement.negate_mod_p a ⦃ r => feNat r = (p384 - feNat a) % p384 ⦄ := by
  unfold mid.p384.FieldElement.negate_mod_p mid.p384.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

/-- `maybe_negate_y` keeps x and negates y mod p when `sign` is nonzero. -/
@[step]
theorem maybe_negate_y_spec (pt : mid.p384.AffineMontPoint) (sign : U8) (hy : (pairNat6 pt.xy.val).2 ≤ p384) :
    mid.p384.AffineMontPoint.maybe_negate_y pt sign ⦃ r =>
      pairNat6 r.xy.val = ((pairNat6 pt.xy.val).1,
        if sign.val = 0 then (pairNat6 pt.xy.val).2 else (p384 - (pairNat6 pt.xy.val).2) % p384) ⦄ := by
  unfold mid.p384.AffineMontPoint.maybe_negate_y
  have hl : (pt.xy.val).length = 12 := pt.xy.property
  step as ⟨fy, hfy⟩
  step with fe_negate_spec fy (by rw [hfy]; exact hy) as ⟨ny, hny⟩
  step as ⟨sel, hsel⟩
  step*
  · simp [mid.p384.AffineMontPoint.Y]
  · simp [mid.p384.AffineMontPoint.Y]
  · simp [s_post1, s1_post, mid.p384.AffineMontPoint.Y]
  · have hsl : sel.val.length = 6 := sel.property
    have hv : (index_mut_back s2).val = pt.xy.val.take 6 ++ sel.val := by
      rw [s_post2, s2_post, s1_post, Array.val_to_slice]
      simp only [mid.p384.AffineMontPoint.Y]
      generalize pt.xy.val = l at hl ⊢
      match l, hl with
      | [a, b, c, d, e, f, g, h', i, j, k, m], _ =>
        generalize sel.val = q at hsl ⊢
        match q, hsl with
        | [a', b', c', d', e', f'], _ => simp [List.setSlice!]
    rw [hv, pairNat6_append _ _ (by simp [hl]) hsl]
    simp only [pairNat6, Prod.mk.injEq, true_and]
    rw [hsel]
    split_ifs
    · exact hfy
    · exact hny.trans (by rw [hfy]; rfl)

@[step]
theorem lookup_comb_spec (hsel : AffSelect) (table : Std.Array U64 192#usize) (index : U8) :
    mid.p384.AffineMontPoint.lookup_comb table index ⦃ r =>
      r.xy.val = if 1 ≤ index.val ∧ index.val ≤ 16 then (table.val.drop (12 * (index.val - 1))).take 12
        else List.replicate 12 0#u64 ⦄ := by
  unfold mid.p384.AffineMontPoint.lookup_comb mid.p384.AffineMontPoint.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  simp only [lift, bind_ok]
  step with hsel _ table.to_slice index (by simp) as ⟨r, hr⟩
  simpa using hr

/-! ## Points -/

/-- `pt` holds `P` in Jacobian Montgomery form, as s2n-bignum's routines read it. -/
def jrep (P : nist.Point) (pt : mid.p384.JacobianMontPoint) : Prop :=
  p384Represents P (tripleNat6 pt.xyz.val)

@[step]
theorem infinity_spec : mid.p384.JacobianMontPoint.infinity ⦃ pt => jrep none pt ⦄ := by
  unfold mid.p384.JacobianMontPoint.infinity
  simp only [WP.spec_ok, jrep, p384Represents, tripleNat6, Array.make]
  refine ⟨by simp [wordsNat, Nat.ofDigits, p384], by simp [wordsNat, Nat.ofDigits, p384],
    by simp [wordsNat, Nat.ofDigits, p384], ?_⟩
  simp [wordsNat, Nat.ofDigits, nist.ofJacobian]

/-- `add_inplace_affine` keeps the point for a zero digit, and otherwise adds
the affine point, which must differ from it. -/
@[step]
theorem add_inplace_affine_spec (_h : Runs) (pt : mid.p384.JacobianMontPoint) (p : mid.p384.AffineMontPoint)
    (digit : U8) :
    mid.p384.JacobianMontPoint.add_inplace_affine pt p digit ⦃ r =>
      (digit.val = 0 → r = pt) ∧
        (digit.val ≠ 0 → ∀ P1 P2, jrep P1 pt → p384Represents2 P2 (pairNat6 p.xy.val) → P1 ≠ P2 →
          jrep (p384Add P1 P2) r) ⦄ := by
  unfold mid.p384.JacobianMontPoint.add_inplace_affine
  step as ⟨inf, hinf⟩
  step as ⟨a, ha⟩
  step as ⟨r, hr⟩
  rw [hr]
  refine ⟨fun h0 => by simp [h0], fun h0 P1 P2 h1 h2 hne => ?_⟩
  simp only [h0, ↓reduceIte, jrep]
  exact ha P1 P2 h1 h2 hne

theorem double_inplace_n_spec (_h : Runs) (iter : core.ops.range.Range Usize) (pt : mid.p384.JacobianMontPoint)
    (P : nist.Point) (hP : jrep P pt) (hle : iter.start.val ≤ iter.end.val) :
    mid.p384.JacobianMontPoint.double_inplace_n_loop iter pt ⦃ r =>
      jrep (Nat.iterate (fun Q => p384Add Q Q) (iter.end.val - iter.start.val) P) r ⦄ := by
  unfold mid.p384.JacobianMontPoint.double_inplace_n_loop
  apply loop.spec_decr_nat (fun x => x.1.end.val - x.1.start.val)
    (fun x => iter.start.val ≤ x.1.start.val ∧ x.1.start.val ≤ x.1.end.val ∧ x.1.end.val = iter.end.val ∧
      jrep (Nat.iterate (fun Q => p384Add Q Q) (x.1.start.val - iter.start.val) P) x.2)
  · rintro ⟨it, q⟩ ⟨hs0, hs, he, hq⟩
    simp only at hs0 hs he hq ⊢
    unfold mid.p384.JacobianMontPoint.double_inplace_n_loop.body
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨a, ha⟩
      have he1' : iter1.end.val = it.end.val := by rw [he1]
      refine ⟨by omega, by omega, by rw [he1, he], ?_, by omega⟩
      rw [show iter1.start.val - iter.start.val = (it.start.val - iter.start.val) + 1 by omega,
        Function.iterate_succ_apply']
      exact ha _ hq
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      rwa [show iter.end.val = it.start.val by omega]
  · exact ⟨le_rfl, hle, rfl, by simpa using hP⟩

/-! ## Booth recoding -/

theorem bv_window_hi (a b : BitVec 64) (s : Nat) (hs1 : 58 < s) (hs : s < 64) :
    ((a >>> s ||| b <<< (64 - s)) &&& 63#64).toNat = (a.toNat + 2 ^ 64 * b.toNat) / 2 ^ s % 64 := by
  have h : (a >>> s ||| b <<< (64 - s)) &&& 63#64 = ((b ++ a) >>> s).setWidth 64 &&& 63#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h63 : (63#64).getLsbD i = decide (i < 6) := by
      rw [show (63#64) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
      simp [hi]
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_append, h63]
    by_cases h6 : i < 6
    · simp only [h6, decide_true, Bool.and_true, hi]
      by_cases ht : i < 64 - s
      · have : s + i < 64 := by omega
        simp [ht, this]
      · simp only [ht, show ¬ s + i < 64 by omega, decide_false, Bool.not_false, Bool.true_and]
        simp [BitVec.getLsbD_of_ge a (s + i) (by omega), show i - (64 - s) = s + i - 64 by omega]
    · simp [h6]
  rw [h, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt a.isLt, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show (63#64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 6 ∣ 2 ^ 64)]
  ring_nf

theorem bv_window_lo (a : BitVec 64) (s : Nat) :
    ((a >>> s) &&& 63#64).toNat = a.toNat / 2 ^ s % 64 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (63#64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem wordsNat_chunk (l : List U64) (hl : l.length = 6) (i : Nat) (hi : i < 6) :
    wordsNat l / 2 ^ (64 * i) % 2 ^ 128 =
      (l[i]!).val + 2 ^ 64 * (if i + 1 < 6 then (l[i + 1]!).val else 0) := by
  match l, hl with
  | [a0, a1, a2, a3, a4, a5], _ =>
    have h0 := a0.hBounds; have h1 := a1.hBounds; have h2 := a2.hBounds
    have h3 := a3.hBounds; have h4 := a4.hBounds; have h5 := a5.hBounds
    simp only [UScalarTy.numBits] at h0 h1 h2 h3 h4 h5
    simp only [wordsNat, List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil]
    interval_cases i <;> simp <;> omega


theorem window_bits (k w A B : Nat) (hAB : k / 2 ^ (64 * ((5 * w - 1) / 64)) % 2 ^ 128 = A + 2 ^ 64 * B) :
    k / 2 ^ (5 * w - 1) % 64 = (A + 2 ^ 64 * B) / 2 ^ ((5 * w - 1) % 64) % 64 := by
  set bit := 5 * w - 1
  have hs : bit % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hb : 2 ^ bit = 2 ^ (64 * (bit / 64)) * 2 ^ (bit % 64) := by
    rw [← pow_add, Nat.div_add_mod]
  have hd : 2 ^ (bit % 64) * 64 ∣ 2 ^ 128 := by
    rw [show (64 : Nat) = 2 ^ 6 by norm_num, ← pow_add]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [hb, ← Nat.div_div_eq_div_mul, ← Nat.mod_mul_right_div_self, ← Nat.mod_mod_of_dvd _ hd, hAB,
    Nat.mod_mul_right_div_self]

theorem window_lo (A B s : Nat) (hs : s ≤ 58) : (A + 2 ^ 64 * B) / 2 ^ s % 64 = A / 2 ^ s % 64 := by
  have hd : 2 ^ s * 64 ∣ 2 ^ 64 := by
    rw [show (64 : Nat) = 2 ^ 6 by norm_num, ← pow_add]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self A, Nat.add_mod,
    Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hd B), add_zero, Nat.mod_mod]

def recodeD (x : BitVec 8) : BitVec 8 :=
  let sign := ~~~((x >>> 5) - 1)
  let d := ((1#16 <<< 6) - x.setWidth 16 - 1).setWidth 8
  let d1 := (d &&& sign) ||| (x &&& ~~~sign)
  (d1 >>> 1) + (d1 &&& 1)

def recodeS (x : BitVec 8) : BitVec 8 := ~~~((x >>> 5) - 1) &&& 1

theorem recode_ok : ∀ x : BitVec 8, x.toNat < 64 →
    (recodeD x).toNat = boothD x.toNat ∧ (recodeS x).toNat = boothS x.toNat := by
  decide

theorem booth_recode_w5_spec (v : U8) (hv : v.val < 64) :
    mid.p384.booth_recode_w5 v ⦃ d s => d.val = boothD v.val ∧ s.val = boothS v.val ⦄ := by
  unfold mid.p384.booth_recode_w5
  step*
  have hd : d2.bv = recodeD v.bv := by
    simp [d2_post, i9_post1, i10_post1, d1_post1, i6_post1, i8_post1, i7_post, d_post, i5_post, i4_post,
      i3_post, i2_post1, sign_post, i1_post, i_post1, recodeD, UScalar.cast_bv_eq]
  have hs : i11.bv = recodeS v.bv := by
    simp [i11_post1, sign_post, i1_post, i_post1, recodeS]
  have h := recode_ok v.bv (by simpa using hv)
  simp only [UScalar.val, hd, hs]
  exact h


/-- The first `n` of `windows` hold `k`'s Booth digits and signs. -/
def WindowsOk (k : Nat) (windows : Std.Array (U8 × U8) 77#usize) (n : Nat) : Prop :=
  ∀ i < n, ((windows.val[i]!).1).val = boothD (window k i) ∧ ((windows.val[i]!).2).val = boothS (window k i)

theorem window_lt (k w : Nat) : window k w < 64 := by
  unfold window; split <;> exact Nat.mod_lt _ (by norm_num)

theorem windowsOk_update (k : Nat) (windows : Std.Array (U8 × U8) 77#usize) (n : Nat) (hn : n < 77)
    (h : WindowsOk k windows n) (p : U8 × U8) (hp1 : p.1.val = boothD (window k n))
    (hp2 : p.2.val = boothS (window k n)) (idx : Usize) (hidx : idx.val = n) (w : Std.Array (U8 × U8) 77#usize)
    (hw : w = windows.set idx p) :
    WindowsOk k w (n + 1) := by
  have hl : windows.val.length = 77 := windows.property
  intro i hi
  rw [hw, Std.Array.set_val_eq, hidx]
  by_cases hin : i = n
  · subst hin
    simp_lists [hp1, hp2]
  · have h' := h i (by omega)
    simp_lists
    rwa [getElem!_pos _ _ (by omega)] at h'

theorem booth_w5_loop_spec (a : Std.Array U64 6#usize) (iter : core.ops.range.Range Usize)
    (windows : Std.Array (U8 × U8) 77#usize) (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ 77)
    (he : iter.end.val = 77) (hw : WindowsOk (wordsNat a.val) windows iter.start.val) :
    mid.p384.Scalar.booth_w5_loop iter a windows ⦃ r => WindowsOk (wordsNat a.val) r 77 ⦄ := by
  unfold mid.p384.Scalar.booth_w5_loop
  apply loop.spec_decr_nat (fun x => 77 - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ 77 ∧ x.1.end.val = 77 ∧
      WindowsOk (wordsNat a.val) x.2 x.1.start.val)
  · rintro ⟨it, ws⟩ ⟨hs1, hs, he, hw⟩
    simp only at hs1 hs he hw ⊢
    unfold mid.p384.Scalar.booth_w5_loop.body
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      have he1' : iter1.end.val = it.end.val := by rw [he1]
      step as ⟨i, hi⟩
      step as ⟨bit, hbit, hbit1⟩
      step as ⟨word, hword⟩
      step as ⟨shift, hshift⟩
      step as ⟨i1, hi1⟩
      step as ⟨value, hvalue0, hvalue⟩
      have hl : a.val.length = 6 := a.property
      have hwd : word.val < 6 := by omega
      have hchunk := wordsNat_chunk a.val hl word.val hwd
      have hwv : word.val = (5 * it.start.val - 1) / 64 := by omega
      have hsv : shift.val = (5 * it.start.val - 1) % 64 := by omega
      have hbits := window_bits (wordsNat a.val) it.start.val _ _ (by rw [← hwv]; exact hchunk)
      have hwin : window (wordsNat a.val) it.start.val = wordsNat a.val / 2 ^ (5 * it.start.val - 1) % 64 := by
        unfold window; simp [show it.start.val ≠ 0 by omega]
      have hA : i1 = a.val[word.val]! := by rw [hi1]; exact (getElem!_pos _ _ (by omega)).symm
      apply WP.spec_bind (Pₘ := fun x : core.ops.range.Range Usize × U64 =>
        x.1 = iter1 ∧ (x.2 &&& 63#u64).val = window (wordsNat a.val) it.start.val)
      · rw [hwin, hbits, ← hsv, ← hA]
        split
        · rename_i h58
          have h58' : 58 < shift.val := by scalar_tac
          split
          · rename_i h5
            have h5' : word.val < 5 := by scalar_tac
            step as ⟨w1, hw1⟩
            step as ⟨b1, hb1⟩
            step as ⟨t, ht, ht1⟩
            step as ⟨y, hy, hy1⟩
            simp only [show word.val + 1 < 6 by omega, ↓reduceIte]
            have hb : b1 = a.val[word.val + 1]! := by
              rw [hb1, getElem!_pos _ _ (by omega)]; simp only [hw1]
            show ((value ||| y) &&& 63#u64).bv.toNat = _
            rw [UScalar.bv_and, UScalar.bv_or, hvalue, hy1, ht, ← hb]
            exact bv_window_hi i1.bv b1.bv shift.val h58' (by omega)
          · rename_i h5
            have h5' : word.val = 5 := by scalar_tac
            simp only [bind_ok, WP.spec_ok, true_and]
            simp only [show ¬ (word.val + 1 < 6) by omega, ↓reduceIte, mul_zero, add_zero]
            show (value &&& 63#u64).bv.toNat = _
            rw [UScalar.bv_and, hvalue]
            exact bv_window_lo i1.bv shift.val
        · rename_i h58
          have h58' : shift.val ≤ 58 := by scalar_tac
          simp only [WP.spec_ok, true_and]
          rw [window_lo _ _ _ h58']
          show (value &&& 63#u64).bv.toNat = _
          rw [UScalar.bv_and, hvalue]
          exact bv_window_lo i1.bv shift.val
      · rintro ⟨iter2, value1⟩ ⟨hit, hv1⟩
        simp only at hit hv1 ⊢
        subst hit
        step as ⟨i2, hi2⟩
        step as ⟨i3, hi3⟩
        have hi3v : i3.val = window (wordsNat a.val) it.start.val := by
          rw [hi3, UScalar.cast_val_eq, hi2, hv1]
          exact Nat.mod_eq_of_lt (lt_of_lt_of_le (window_lt _ _) (by decide))
        step with booth_recode_w5_spec i3 (by rw [hi3v]; exact window_lt _ _) as ⟨p, hd, hsg⟩
        step as ⟨a1, ha1⟩
        refine ⟨by omega, by omega, by rw [he1', he], ?_, by omega⟩
        rw [hst]
        exact windowsOk_update _ ws _ (by omega) hw p (by rw [hd, hi3v]) (by rw [hsg, hi3v]) _ rfl a1 ha1
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      rwa [show (77 : Nat) = it.start.val by omega]
  · exact ⟨hs1, hs, he, hw⟩

theorem booth_w5_spec (k : mid.p384.Scalar) :
    mid.p384.Scalar.booth_w5 k ⦃ r => WindowsOk (wordsNat k.val) r 77 ⦄ := by
  unfold mid.p384.Scalar.booth_w5
  have hl : k.val.length = 6 := k.property
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1'⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have hW : wordsNat k.val % 2 ^ 64 = i.val := by
    have h := wordsNat_chunk k.val hl 0 (by norm_num)
    rw [hi, ← getElem!_pos _ _ (by omega)]
    simp only [mul_zero, pow_zero, Nat.div_one, zero_add, show 1 < 6 by norm_num, ↓reduceIte] at h
    have hb := (k.val[0]!).hBounds
    simp only [UScalarTy.numBits] at hb
    omega
  have hi3v : i3.val = window (wordsNat k.val) 0 := by
    rw [hi3, UScalar.cast_val_eq, hi2, UScalar.val_and, hi1,
      show (63#u64).val = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
    simp only [window, ↓reduceIte, pow_one]
    rw [U64.size_def]; simp only [U64.numBits, UScalarTy.numBits]
    omega
  step with booth_recode_w5_spec i3 (by rw [hi3v]; exact window_lt _ _) as ⟨p, hd, hsg⟩
  step as ⟨a, ha⟩
  apply booth_w5_loop_spec k _ a (by simp) (by simp) (by simp)
  have := windowsOk_update (wordsNat k.val) (Array.repeat 77#usize (0#u8, 0#u8)) 0 (by norm_num)
    (fun i hi => absurd hi (Nat.not_lt_zero _)) p (by rw [hd, hi3v]) (by rw [hsg, hi3v]) _ rfl a ha
  simpa using this

/-! ## The comb -/

theorem pairNat6_take12 (l : List U64) : pairNat6 (l.take 12) = pairNat6 l := by
  simp [pairNat6, List.take_take, List.drop_take]

theorem boothD_le (v : Nat) (hv : v < 64) : boothD v ≤ 16 := by
  unfold boothD; split <;> omega

theorem rep2_neg (P : nist.Point) (x y : Nat) (h : p384Represents2 P (x, y)) :
    p384Represents2 (p384Neg P) (x, (p384 - y) % p384) := by
  obtain ⟨hx, hy, rfl⟩ := h
  refine ⟨hx, Nat.mod_lt _ p384_pos, ?_⟩
  simp only [p384Neg, nist.neg, Option.some.injEq, Prod.mk.injEq, true_and]
  have h1 : (((p384 - y % p384) % p384 : Nat) : ZMod p384) = -(y : ZMod p384) := nist.natCast_neg_mod y
  have h2 : (((p384 - p384RInv * y % p384 % p384) % p384 : Nat) : ZMod p384) = -((p384RInv * y : Nat) : ZMod p384) :=
    by rw [Nat.mod_mod]; exact nist.natCast_neg_mod _
  simp only at hy h1
  rw [Nat.mod_eq_of_lt hy] at h1
  have L : p384RInv * ((p384 - y) % p384) % p384 = ((p384RInv * ((p384 - y) % p384) : Nat) : ZMod p384).val :=
    (ZMod.val_natCast _ _).symm
  have R : (p384 - p384RInv * y % p384 % p384) % p384 =
      (((p384 - p384RInv * y % p384 % p384) % p384 : Nat) : ZMod p384).val :=
    (ZMod.val_cast_of_lt (Nat.mod_lt _ p384_pos)).symm
  rw [L, R, h2, Nat.cast_mul, h1]
  push_cast; ring_nf

theorem fromM_inj (X Y : p384Curve.Point) (h : nist.fromM X = nist.fromM Y) : X = Y := by
  cases X <;> cases Y <;> simp [nist.fromM] at h ⊢
  exact ⟨ZMod.val_injective _ h.1, ZMod.val_injective _ h.2⟩

/-- The point `a·X`. -/
abbrev gpt (X : p384Curve.Point) (a : Int) : nist.Point := nist.fromM (a • X)

theorem entry_point (X : p384Curve.Point) (hX : nist.fromM X = p384G) (j d s : Nat) :
    (if s = 0 then p384Pow p384G (d * 2 ^ (20 * j)) else p384Neg (p384Pow p384G (d * 2 ^ (20 * j)))) =
      gpt X (signed d s * 32 ^ (4 * j)) := by
  rw [← hX, p384Pow, nist.pow_fromM, ← natCast_zsmul]
  have h32 : ((d * 2 ^ (20 * j) : Nat) : Int) = (d : Int) * 32 ^ (4 * j) := by
    push_cast; congr 1; rw [show (32 : Int) = 2 ^ 5 by norm_num, ← pow_mul]; congr 1; omega
  unfold signed
  split_ifs
  · rw [h32]
  · rw [p384Neg, nist.neg_fromM, ← neg_zsmul, h32, neg_mul]

theorem gpt_ne (X : p384Curve.Point) (hord : addOrderOf X = n384) (a b : Int) (h : ¬ a ≡ b [ZMOD n384]) :
    gpt X a ≠ gpt X b := by
  intro he
  apply h
  have := fromM_inj _ _ he
  rw [zsmul_eq_zsmul_iff_modEq, hord] at this
  exact this

theorem comb_inner_spec (h : Runs) (hsel : AffSelect) (X : p384Curve.Point) (hX : nist.fromM X = p384G) (hord : addOrderOf X = n384)
    (htab : CombTabulated mid.p384.precomp.CURVE_GENERATOR_PRECOMP_COMB)
    (k : Nat) (hk : k < n384) (windows : Std.Array (U8 × U8) 77#usize) (hw : WindowsOk k windows 77)
    (tooth : Usize) (ht : tooth.val < 4) (iter : core.ops.range.Range Usize) (hs : iter.start.val ≤ 20)
    (he : iter.end.val = 20) (result : mid.p384.JacobianMontPoint)
    (hres : jrep (gpt X (combAcc (digit k) tooth.val iter.start.val)) result) :
    mid.p384.JacobianMontPoint.base_multiply_loop0_loop0 iter windows result tooth ⦃ r =>
      jrep (gpt X (combAcc (digit k) tooth.val 20)) r ⦄ := by
  unfold mid.p384.JacobianMontPoint.base_multiply_loop0_loop0
  have hk384 : k < 2 ^ 384 := lt_trans hk (by simp [n384])
  apply loop.spec_decr_nat (fun x => 20 - x.1.start.val)
    (fun x => x.1.start.val ≤ 20 ∧ x.1.end.val = 20 ∧
      jrep (gpt X (combAcc (digit k) tooth.val x.1.start.val)) x.2)
  · rintro ⟨it, res⟩ ⟨hs, he, hres⟩
    simp only at hs he hres ⊢
    unfold mid.p384.JacobianMontPoint.base_multiply_loop0_loop0.body
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      have he1' : iter1.end.val = it.end.val := by rw [he1]
      have hj : it.start.val < 20 := by omega
      have hacc := combAcc_succ (digit k) _ _ ht hj
      rw [← hst] at hacc
      step as ⟨i, hi⟩
      step as ⟨w, hwv⟩
      split
      · rename_i hw77
        have hw77' : 4 * it.start.val + tooth.val < 77 := by scalar_tac
        simp only [hw77', ↓reduceIte] at hacc
        have hwn : w.val = 4 * it.start.val + tooth.val := by scalar_tac
        step as ⟨pr, hpr⟩
        obtain ⟨dg, sg⟩ := pr
        step as ⟨tbl, htbl⟩
        step as ⟨tmp, htmp⟩
        set j := it.start.val with hjdef
        set t := tooth.val with htdef
        have hwk := hw (4 * j + t) hw77'
        have hpr' : windows.val[w.val]! = (dg, sg) := by
          rw [getElem!_pos _ _ (by rw [windows.property]; scalar_tac)]; exact hpr.symm
        have hpr'' : windows.val[4 * j + t]! = (dg, sg) := by rw [← hwn]; exact hpr'
        rw [hpr''] at hwk
        obtain ⟨hdg, hsg⟩ := hwk
        simp only at hdg hsg
        have hdig : digit k (4 * j + t) = signed dg.val sg.val := by rw [digit, hdg, hsg]
        have hd16 : dg.val ≤ 16 := by rw [hdg]; exact boothD_le _ (window_lt _ _)
        have htbl' : tbl.val = (mid.p384.precomp.CURVE_GENERATOR_PRECOMP_COMB.val[j]!).val := by
          rw [htbl, getElem!_pos _ _ (by rw [Std.Array.property]; scalar_tac)]
        by_cases hd0 : dg.val = 0
        · have hz : pairNat6 tmp.xy.val = (0, 0) := by
            rw [htmp]; simp [hd0, pairNat6, wordsNat, Nat.ofDigits]
          step with maybe_negate_y_spec tmp sg (by rw [hz]; exact Nat.zero_le _) as ⟨tmp1, htmp1⟩
          step as ⟨r1, hr0, hr1⟩
          refine ⟨by omega, by rw [he1', he], ?_, by omega⟩
          rw [hacc, hdig, hd0, hr0 hd0]
          simpa [signed] using hres
        · have hentry := htab j hj dg.val (by omega) hd16
          rw [ite_eq_left ⟨by omega, hd16⟩] at htmp
          rw [← htbl', ← pairNat6_take12, ← htmp] at hentry
          have hy := hentry.2.1
          step with maybe_negate_y_spec tmp sg (le_of_lt hy) as ⟨tmp1, htmp1⟩
          have hP2 : p384Represents2 (gpt X (digit k (4 * j + t) * 32 ^ (4 * j))) (pairNat6 tmp1.xy.val) := by
            rw [hdig, ← entry_point X hX j dg.val sg.val, htmp1]
            split_ifs with hs0
            · exact hentry
            · exact rep2_neg _ _ _ hentry
          have hne : digit k (4 * j + t) ≠ 0 := by
            rw [hdig]; unfold signed; split <;> omega
          have hne' := gpt_ne X hord _ _ (comb_ne (digit k) (fun w _ => digit_abs k w) (digit_76 k hk384) k
            (booth_sum k hk384) hk t j ht hj hw77' hne)
          step as ⟨r1, hr0, hr1⟩
          refine ⟨by omega, by rw [he1', he], ?_, by omega⟩
          rw [hacc, gpt, add_zsmul, ← nist.fromM_add]
          exact hr1 hd0 _ _ hres hP2 hne'
      · rename_i hw77
        have hw77' : ¬ 4 * it.start.val + tooth.val < 77 := by scalar_tac
        simp only [hw77', ↓reduceIte, add_zero] at hacc
        simp only [WP.spec_ok]
        exact ⟨by omega, by rw [he1', he], by rw [hacc]; exact hres, by omega⟩
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      rwa [show (20 : Nat) = it.start.val by omega]
  · exact ⟨hs, he, hres⟩


@[step]
theorem rev_next_spec (r : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) r ⦃ o r' =>
      r'.iter.start = r.iter.start ∧
        (if r.iter.start.val < r.iter.end.val then o = some r'.iter.end ∧ r'.iter.end.val + 1 = r.iter.end.val
          else o = none) ⦄ := by
  unfold core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  simp only [
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.backward_checked]
  by_cases hlt : r.iter.start.val < r.iter.end.val
  · have hb : liftFun2 core.cmp.impls.PartialOrdUsize.lt r.iter.start r.iter.end = ok true := by
      simp [liftFun2, core.cmp.impls.PartialOrdUsize.lt, hlt]
    have h1 : (1#usize).val ≤ r.iter.end.val := by simp; omega
    simp only [hb, bind_ok, ↓reduceIte, h1, ↓reduceDIte, hlt]
    simp [UScalar.ofNatCore_val_eq]; omega
  · have hb : liftFun2 core.cmp.impls.PartialOrdUsize.lt r.iter.start r.iter.end = ok false := by
      simp [liftFun2, core.cmp.impls.PartialOrdUsize.lt, hlt]
    simp [hb, hlt, WP.spec_ok]

theorem iterate_double (X : p384Curve.Point) (n : Nat) (a : Int) :
    (fun Q => p384Add Q Q)^[n] (gpt X a) = gpt X (2 ^ n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, gpt, p384Add, nist.fromM_add, ← add_zsmul, pow_succ]
    ring_nf

/-- The accumulator once tooth `m`'s pass finishes, before the pass of
tooth `m - 1`: none yet for `m` = 4. -/
def toothAcc (k m : Nat) : Int := if m = 4 then 0 else combAcc (digit k) m 20

theorem comb_outer_spec (h : Runs) (hsel : AffSelect) (X : p384Curve.Point) (hX : nist.fromM X = p384G) (hord : addOrderOf X = n384)
    (htab : CombTabulated mid.p384.precomp.CURVE_GENERATOR_PRECOMP_COMB)
    (k : Nat) (hk : k < n384) (windows : Std.Array (U8 × U8) 77#usize) (hw : WindowsOk k windows 77)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (hs : iter.iter.start.val = 0)
    (he : iter.iter.end.val ≤ 4) (result : mid.p384.JacobianMontPoint)
    (hres : jrep (gpt X (toothAcc k iter.iter.end.val)) result) :
    mid.p384.JacobianMontPoint.base_multiply_loop0 iter windows result ⦃ r =>
      jrep (gpt X (combAcc (digit k) 0 20)) r ⦄ := by
  unfold mid.p384.JacobianMontPoint.base_multiply_loop0
  apply loop.spec_decr_nat (fun x => x.1.iter.end.val)
    (fun x => x.1.iter.start.val = 0 ∧ x.1.iter.end.val ≤ 4 ∧ jrep (gpt X (toothAcc k x.1.iter.end.val)) x.2)
  · rintro ⟨it, res⟩ ⟨hs, he, hres⟩
    simp only at hs he hres ⊢
    unfold mid.p384.JacobianMontPoint.base_multiply_loop0.body
    step as ⟨o, it1, hst, ho⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, he1⟩ := ho
      simp only
      have hst' : it1.iter.start.val = 0 := by rw [hst]; exact hs
      set t := it1.iter.end.val with htdef
      have ht : t < 4 := by omega
      apply WP.spec_bind (Pₘ := fun r1 => jrep (gpt X (combAcc (digit k) t 0)) r1)
      · split
        · rename_i h3
          have h3' : t ≠ 3 := by
            intro e
            have : it1.iter.end = 3#usize := UScalar.eq_of_val_eq (by simp [← htdef, e])
            simp [this] at h3
          step with double_inplace_n_spec h { start := 0#usize, «end» := 5#usize } res _ hres (by simp) as ⟨r1, hr1⟩
          rw [iterate_double] at hr1
          have hm : it.iter.end.val = t + 1 := by omega
          rw [hm, toothAcc, ite_eq_right (by omega)] at hr1
          rw [combAcc_tooth _ _ (by omega)]
          simpa using hr1
        · rename_i h3
          have h3' : t = 3 := by simpa using h3
          simp only [WP.spec_ok]
          have hm : it.iter.end.val = 4 := by omega
          rw [hm, toothAcc, ite_eq_left rfl] at hres
          rw [h3', combAcc_start]
          exact hres
      · intro r1 hr1
        step with comb_inner_spec h hsel X hX hord htab k hk windows hw it1.iter.end (by omega)
          { start := 0#usize, «end» := 20#usize } (by simp) (by simp) r1 (by simpa using hr1) as ⟨r2, hr2⟩
        refine ⟨by omega, by omega, ?_, by omega⟩
        rw [toothAcc, ite_eq_right (by omega)]
        exact hr2
    · obtain ⟨rfl⟩ := ho
      simp only [WP.spec_ok]
      have h0 : it.iter.end.val = 0 := by omega
      rw [h0, toothAcc, ite_eq_right (by norm_num)] at hres
      exact hres
  · exact ⟨hs, he, hres⟩

@[step]
theorem base_multiply_spec (h : Runs) (hsel : AffSelect) (htab : CombTabulated mid.p384.precomp.CURVE_GENERATOR_PRECOMP_COMB)
    (k : mid.p384.Scalar) (hk : wordsNat k.val < n384) :
    mid.p384.JacobianMontPoint.base_multiply k ⦃ r => jrep (p384Pow p384G (wordsNat k.val)) r ⦄ := by
  obtain ⟨X, hX, hX0, hn⟩ := p384_fromM_G
  have hord : addOrderOf X = n384 := addOrderOf_eq_prime hn hX0
  have hk384 : wordsNat k.val < 2 ^ 384 := lt_trans hk (by simp [n384])
  unfold mid.p384.JacobianMontPoint.base_multiply
  step with booth_w5_spec k as ⟨windows, hw⟩
  step with infinity_spec as ⟨inf, hinf⟩
  step as ⟨iter, hiter⟩
  apply WP.spec_mono (comb_outer_spec h hsel X hX hord htab _ hk windows hw iter (by rw [hiter]; rfl) (by rw [hiter]; decide) inf
    (by rw [hiter]; show jrep (nist.fromM ((if 4 = 4 then 0 else _ : Int) • X)) inf; rw [ite_eq_left rfl, zero_zsmul]; exact hinf))
  intro r hr
  rw [combAcc_end, booth_sum _ hk384] at hr
  rw [← hX, p384Pow, nist.pow_fromM, ← natCast_zsmul]
  exact hr


/-! ## Key generation -/

@[step]
theorem private_eq_spec (a b : mid.p384.Scalar) :
    mid.p384.Scalar.private_eq a b ⦃ r => r = decide (wordsNat a.val = wordsNat b.val) ⦄ := by
  unfold mid.p384.Scalar.private_eq
  step*

@[step]
theorem reduce_mod_n_spec (a : mid.p384.Scalar) :
    mid.p384.Scalar.reduce_mod_n a ⦃ r => wordsNat r.val = wordsNat a.val % n384 ⦄ := by
  unfold mid.p384.Scalar.reduce_mod_n mid.p384.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

theorem into_range_check_spec (sc : mid.p384.Scalar) :
    mid.p384.Scalar.into_range_check sc ⦃ r =>
      if 0 < wordsNat sc.val ∧ wordsNat sc.val < n384 then r = .Ok sc
      else r = .Err (.KeyRejected .ScalarOutOfRange) ⦄ := by
  unfold mid.p384.Scalar.into_range_check mid.p384.Scalar.is_zero
    mid.p384.Scalar.Insts.CoreDefaultDefault.default core.default.DefaultArray.default low.ct.into_public
  simp only [core.convert.IntoFrom.into, error.Error.Insts.CoreConvertFromKeyFormatError.from]
  step as ⟨red, hred⟩
  step as ⟨b, hb⟩
  step as ⟨b1, hb1⟩
  have hn : 0 < n384 := by simp [n384]
  have hbv : b = decide (wordsNat sc.val < n384) := by
    rw [hb, hred]; exact decide_eq_decide.mpr (Nat.mod_eq_iff_lt (by omega))
  have hb1v : b1 = decide (wordsNat sc.val = 0) := by
    rw [hb1]; congr 2
  subst hbv hb1v
  by_cases hr : 0 < wordsNat sc.val ∧ wordsNat sc.val < n384
  · have h0 : wordsNat sc.val ≠ 0 := by omega
    simp [hr, h0]
  · simp only [hr, ↓reduceIte]
    by_cases h0 : wordsNat sc.val = 0
    · simp [h0]
    · have : ¬ wordsNat sc.val < n384 := fun h => hr ⟨by omega, h⟩
      simp [this, h0]

theorem be_any_size_48_spec (s : Slice U8) (h : s.length = 48) :
    mid.util.big_endian_slice_any_size_to_u64x6 s ⦃ o =>
      ∃ w, o = some w ∧ wordsNat w.val = beNat s.val ⦄ := by
  unfold mid.util.big_endian_slice_any_size_to_u64x6
  have hl : s.len = 48#usize := by
    apply UScalar.eq_of_val_eq; simpa [Slice.len, Slice.length] using h
  simp only [core.array.TryFromSharedArraySlice.try_from, hl, ↓reduceDIte]
  step as ⟨w, hw⟩
  simp [hw]

theorem from_bytes_checked_spec (bytes : Slice U8) (hl : bytes.length = 48) :
    mid.p384.Scalar.from_bytes_checked bytes ⦃ r =>
      if 0 < beNat bytes.val ∧ beNat bytes.val < n384 then
        ∃ sc, r = .Ok sc ∧ wordsNat sc.val = beNat bytes.val
      else r = .Err (.KeyRejected .ScalarOutOfRange) ⦄ := by
  unfold mid.p384.Scalar.from_bytes_checked
  apply WP.spec_bind (be_any_size_48_spec bytes hl)
  rintro o ⟨w, rfl, hw⟩
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply WP.spec_mono (into_range_check_spec w)
  intro r hr
  rw [hw] at hr
  split_ifs at hr ⊢
  · exact ⟨w, hr, hw⟩
  · exact hr

theorem from_bytes_spec (bytes : Slice U8) (hl : bytes.length = 48) :
    mid.p384.PrivateKey.from_bytes bytes ⦃ r =>
      if 0 < beNat bytes.val ∧ beNat bytes.val < n384 then
        ∃ k, r = .Ok k ∧ wordsNat k.scalar.val = beNat bytes.val
      else r = .Err (.KeyRejected .ScalarOutOfRange) ⦄ := by
  unfold mid.p384.PrivateKey.from_bytes
  step with from_bytes_checked_spec bytes hl as ⟨r, hr⟩
  split_ifs at hr ⊢
  · obtain ⟨sc, rfl, hsc⟩ := hr
    simp [core.result.Result.map,
      mid.p384.PrivateKey.from_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleScalarPrivateKey.call_once,
      low.ct.into_secret, hsc]
  · subst hr
    simp [core.result.Result.map]

theorem public_point_spec (h : Runs) (hsel : AffSelect) (k : mid.p384.PrivateKey) (x y : Nat) (hk : wordsNat k.scalar.val < n384)
    (hq : p384Pow p384G (wordsNat k.scalar.val) = some (x, y)) (hc : p384OnCurve (some (x, y))) :
    mid.p384.PrivateKey.public_point k ⦃ pt =>
      (pairNat6 pt.xy.val).1 < p384 ∧ (pairNat6 pt.xy.val).2 < p384 ∧
        (p384RInv * (pairNat6 pt.xy.val).1 % p384, p384RInv * (pairNat6 pt.xy.val).2 % p384) = (x, y) ⦄ := by
  unfold mid.p384.PrivateKey.public_point low.ct.into_public
  step with base_multiply_spec h hsel tabulated k.scalar hk as ⟨j, hj⟩
  step with as_affine_spec h j _ hj as ⟨q, hqx, hqy, hq'⟩
  rw [hq] at hq'
  simp only [Option.getD_some] at hq'
  step with on_curve_spec h q hqx hqy as ⟨b, hb⟩
  rw [hq'] at hb
  have hbt : b = true := hb.mpr hc
  subst hbt
  step
  exact ⟨hqx, hqy, Prod.mk.inj hq'⟩


theorem as_bytes_uncompressed_spec (h : Runs) (pt : mid.p384.AffineMontPoint) (hx : (pairNat6 pt.xy.val).1 < p384)
    (hy : (pairNat6 pt.xy.val).2 < p384) :
    mid.p384.AffineMontPoint.as_bytes_uncompressed pt ⦃ b =>
      b.val.head? = some 4#u8 ∧
        p384Coords b.val = (p384RInv * (pairNat6 pt.xy.val).1 % p384, p384RInv * (pairNat6 pt.xy.val).2 % p384) ⦄ := by
  have hl : (pt.xy.val).length = 12 := pt.xy.property
  unfold mid.p384.AffineMontPoint.as_bytes_uncompressed
  simp only [mid.p384.FieldElement.BYTES]
  have h97 : (Array.repeat 97#usize 0#u8).val.length = 97 := by simp [Array.repeat]
  step*
  · have hsl : s.length = 97 := by simp [Slice.length, s_post, Array.repeat]
    rw [indicator_post1, hsl]; simp
  · simp [x_post, s1_post]
  · have hsl : s.length = 97 := by simp [Slice.length, s_post, Array.repeat]
    simp [x_post1, indicator_post1, hsl, s2_post]
  · have hsl : s.length = 97 := by simp [Slice.length, s_post, Array.repeat]
    have hxyl : xy.length = 96 := by rw [indicator_post1, hsl]
    have ha48 : (a.val).length = 48 := a.property
    have ha148 : (a1.val).length = 48 := a1.property
    obtain ⟨hxy, hxyl'⟩ := x_post4 x1 y1 (by simp [x1_post, s1_post])
      (by simp [y1_post, s2_post, hxyl])
    obtain ⟨hall, hall'⟩ := indicator_post4 indicator1 (split_at_mut_back1 (x1, y1))
      (by simp [indicator1_post, indicator_post]) (by rw [hxyl', hxyl, hsl])
    have hind : indicator1.val = [4#u8] := by
      rw [indicator1_post, Slice.set_val_eq, indicator_post2, s_post]
      simp [Array.repeat]
    rw [to_slice_mut_back_post, Array.from_slice_val _ _ (by rw [← Slice.length, hall', hsl]; rfl), hall, hind,
      hxy, x1_post, y1_post, s1_post, s2_post, Array.val_to_slice, Array.val_to_slice]
    refine ⟨rfl, ?_⟩
    simp only [p384Coords]
    have h1 : ([4#u8] ++ (a.val ++ a1.val)).slice 1 49 = a.val := by
      simp [List.slice, List.take_left' ha48]
    have h2 : ([4#u8] ++ (a.val ++ a1.val)).slice 49 97 = a1.val := by
      simp [List.slice, List.drop_left' ha48, List.take_of_length_le, ha148]
    rw [h1, h2, a_post, a1_post]
    simp only [feNat] at fe_post fe1_post fe2_post fe3_post
    rw [fe1_post, fe3_post, fe_post, fe2_post]

theorem public_key_uncompressed_spec (h : Runs) (hsel : AffSelect) (k : mid.p384.PrivateKey) (x y : Nat)
    (hk : wordsNat k.scalar.val < n384)
    (hq : p384Pow p384G (wordsNat k.scalar.val) = some (x, y)) (hc : p384OnCurve (some (x, y))) :
    mid.p384.PrivateKey.public_key_uncompressed k ⦃ b =>
      b.val.head? = some 4#u8 ∧ p384Coords b.val = (x, y) ⦄ := by
  unfold mid.p384.PrivateKey.public_key_uncompressed
  step
  step with public_point_spec h hsel k x y hk hq hc as ⟨pt, hx, hy, hpx, hpy⟩
  step with as_bytes_uncompressed_spec h pt hx hy as ⟨b, hb4, hbc⟩
  exact ⟨hb4, hbc.trans (Prod.ext hpx hpy)⟩

theorem encode_public_spec (h : Runs) (hsel : AffSelect) (k : mid.p384.PrivateKey) (algorithm : high.agreement.Algorithm)
    (x y : Nat) (hk : wordsNat k.scalar.val < n384) (hq : p384Pow p384G (wordsNat k.scalar.val) = some (x, y))
    (hc : p384OnCurve (some (x, y))) :
    high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.encode_public k algorithm ⦃ pk =>
      high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
        b.length = 97 ∧ b.val.head? = some 4#u8 ∧ p384Coords b.val = (x, y) ⦄ ⦄ := by
  unfold high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.encode_public high.agreement.PublicKey.from_encoding
    high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref low.generic.zeroise.ZeroableRef.new
  step with public_key_uncompressed_spec h hsel k x y hk hq hc as ⟨a, ha4, hac⟩
  step as ⟨sl, hsl⟩
  subst hsl
  have hlen : a.to_slice.len.val = 97 := by simp
  step as ⟨s, back, hs, hsl, hback⟩
  step as ⟨x', hx⟩
  step as ⟨b, hb, hbl⟩
  have ha97 : (a.val).length = 97 := a.property
  have hz : (Array.repeat 133#usize 0#u8).val.length = 133 := (Array.repeat 133#usize 0#u8).property
  have hbv : b.val = a.val := by
    have := take_setSlice! (Array.repeat 133#usize 0#u8).val a.val 0 (by omega)
    rw [hb, Array.val_to_slice, hback, hx, Array.val_to_slice, hlen, List.slice]
    simp only [ha97, Nat.zero_add, List.take_zero, List.nil_append] at this
    simp only [List.drop_zero, Nat.sub_zero, this]
  refine ⟨by rw [hbl, hlen], ?_, ?_⟩
  · rw [hbv]; exact ha4
  · rw [hbv]; exact hac

/-- An encoded public key, as `encode_public_spec` states it, is `p384PublicKey`'s. -/
theorem public_key_of_coords (d x y : Nat) (hq : p384Pow p384G d = some (x, y))
    (pk : high.agreement.PublicKey)
    (hpk : high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
      b.length = 97 ∧ b.val.head? = some 4#u8 ∧ p384Coords b.val = (x, y) ⦄) :
    high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
      p384PublicKey d b.val ⦄ :=
  WP.spec_mono hpk fun b ⟨hl, h4, hxy⟩ => ⟨hl, h4, by rw [hq, hxy]⟩

/-- The public key `encode_public` computes for a scalar in [1, n). -/
theorem encode_public_key_spec (h : Runs) (hsel : AffSelect) (k : mid.p384.PrivateKey) (algorithm : high.agreement.Algorithm)
    (hk0 : 0 < wordsNat k.scalar.val) (hk : wordsNat k.scalar.val < n384) :
    high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.encode_public k algorithm ⦃ pk =>
      high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
        p384PublicKey (wordsNat k.scalar.val) b.val ⦄ ⦄ := by
  obtain ⟨x, y, hq, hc⟩ := p384_g_mult _ hk0 hk
  exact WP.spec_mono (encode_public_spec h hsel k algorithm x y hk hq hc)
    fun pk hpk => public_key_of_coords _ x y hq pk hpk

/-- `p384Agree`'s fields, which the theorems below rewrite to, so `step` finds
their specs. -/
theorem p384Agree_random : high.agreement.p384Agree.random = mid.p384.PrivateKey.generate := rfl

theorem p384Agree_load :
    high.agreement.p384Agree.load = high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.load := rfl

theorem p384Agree_encode_public :
    high.agreement.p384Agree.encode_public =
      high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.encode_public := rfl

/-- A key and its public key, as `Keyed::private_key` keeps them, is a `p384Key`. -/
theorem private_key_spec (k : mid.p384.PrivateKey) (pk : high.agreement.PublicKey)
    (hpk : high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b =>
      p384PublicKey (wordsNat k.scalar.val) b.val ⦄) :
    high.agreement.Keyed.private_key high.agreement.p384Agree k pk ⦃ key =>
      p384Key (wordsNat k.scalar.val) key ⦄ := by
  simp only [high.agreement.Keyed.private_key, high.agreement.p384Agree,
    high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.wrap, bind_ok, WP.spec_ok]
  exact ⟨{ key := k, ops := () }, rfl, rfl, hpk⟩

/-- `p384Keygen`, for the scalar `generate_loop` returns. -/
def drawKeygen (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8) (i : Nat) :
    Nat → core.result.Result mid.p384.PrivateKey error.Error → Prop
  | 0, key => key = .Err .RngFailed
  | n + 1, key =>
    match draws i with
    | (.Err _, _) => key = .Err .RngFailed
    | (.Ok _, out) =>
      if 0 < beNat out.val ∧ beNat out.val < n384 then
        ∃ k, key = .Ok k ∧ wordsNat k.scalar.val = beNat out.val
      else drawKeygen draws (i + 1) n key

theorem generate_loop_spec (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8)
    (hdraw : ∀ i, mid.p384.PrivateKey.draw i (Array.repeat 48#usize 0#u8).to_slice = ok (draws i))
    (hlen : ∀ i, (draws i).2.length = 48) (n i : Nat) :
    mid.p384.PrivateKey.generate_loop i n ⦃ key => drawKeygen draws i n key ⦄ := by
  induction n generalizing i with
  | zero => simp [mid.p384.PrivateKey.generate_loop, drawKeygen]
  | succ n ih =>
    unfold mid.p384.PrivateKey.generate_loop
    simp only [Array.to_slice_mut, lift, bind_ok]
    have hf : mid.p384.PrivateKey.draw i (Array.repeat 48#usize 0#u8).to_slice ⦃ p => p = draws i ⦄ := by
      rw [hdraw]; simp [WP.spec_ok]
    step with hf as ⟨r, out, hd⟩
    simp only [drawKeygen, ← hd]
    have hout : out.length = 48 := by simpa [← hd] using hlen i
    have hfrom : ((Array.repeat 48#usize 0#u8).from_slice out).to_slice.val = out.val := by
      simp [Array.from_slice, hout]
    have hl : ((Array.repeat 48#usize 0#u8).from_slice out).to_slice.length = 48 := by
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

/-- A scalar `generate_loop` returns is in [1, n), and is `p384Keygen`'s with
any public key a `p384Key` holds for it. -/
theorem drawKeygen_ok (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8)
    (n i : Nat) (k : mid.p384.PrivateKey) (hr : drawKeygen draws i n (.Ok k)) :
    0 < wordsNat k.scalar.val ∧ wordsNat k.scalar.val < n384 ∧
      ∀ key, p384Key (wordsNat k.scalar.val) key → p384Keygen draws i n (.Ok key) := by
  induction n generalizing i with
  | zero => simp [drawKeygen] at hr
  | succ n ih =>
    simp only [drawKeygen] at hr
    simp only [p384Keygen]
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

/-- A failure `generate_loop` returns is `p384Keygen`'s. -/
theorem drawKeygen_err (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8)
    (n i : Nat) (e : error.Error) (hr : drawKeygen draws i n (.Err e)) :
    p384Keygen draws i n (.Err e) := by
  induction n generalizing i with
  | zero => simpa [drawKeygen, p384Keygen] using hr
  | succ n ih =>
    simp only [drawKeygen] at hr
    simp only [p384Keygen]
    rcases hd : draws i with ⟨res, out⟩
    simp only [hd] at hr ⊢
    rcases res with _ | _
    · simp only at hr ⊢
      split_ifs at hr ⊢
      · obtain ⟨k, hk, -⟩ := hr
        cases hk
      · exact ih (i + 1) hr
    · simpa using hr

theorem load_scalar_spec (h : Runs) (hsel : AffSelect) (algorithm : high.agreement.Algorithm) (b : Slice U8) :
    high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.load algorithm (.Scalar b) ⦃ r =>
      if b.length = 48 then
        if 0 < beNat b.val ∧ beNat b.val < n384 then
          ∃ k pk, r = .Ok (k, pk) ∧ wordsNat k.scalar.val = beNat b.val ∧
            high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk ⦃ b' =>
              p384PublicKey (beNat b.val) b'.val ⦄
        else r = .Err (.KeyRejected .ScalarOutOfRange)
      else r = .Err (.KeyRejected .WrongLength) ⦄ := by
  unfold high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.load
  step as ⟨_⟩
  by_cases hl : b.length = 48
  · have hlen : Slice.len b = mid.p384.Scalar.BYTES := by
      apply UScalar.eq_of_val_eq
      simpa [Slice.len, Slice.length, mid.p384.Scalar.BYTES] using hl
    simp only [hlen, ↓reduceIte, hl]
    step with from_bytes_spec b hl as ⟨r, hr⟩
    split_ifs at hr ⊢ with hrange
    · obtain ⟨k, rfl, hk⟩ := hr
      step with core.result.Result.Insts.CoreOpsTry.branch_Ok.spec as ⟨cf, hcf⟩
      subst hcf
      simp only
      step with encode_public_key_spec h hsel k algorithm (hk ▸ hrange.1) (hk ▸ hrange.2) as ⟨pk, hpk⟩
      exact ⟨k, pk, rfl, hk, hk ▸ hpk⟩
    · subst hr
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · have hlen : ¬ Slice.len b = mid.p384.Scalar.BYTES := by
      intro h'
      exact hl (by simpa [Slice.len, Slice.length, mid.p384.Scalar.BYTES] using congrArg UScalar.val h')
    simp [hlen, hl, error.Error.Insts.CoreConvertFromKeyFormatError.from]

end P384

open P384

/-! ## The agreement API, `high::agreement`, through the modelled dispatch -/

/-- A generated P-384 key's scalar is the first of up to 64 draws from the
system source whose bytes, read big-endian, are in [1, n), and key generation
is refused if a draw fails before one is, or none is. The draws themselves are
outside the functional spec. -/
theorem p384_generate (h : Runs) (hsel : AffSelect) (draws : Nat → core.result.Result Unit getrandom.error.Error × Slice U8)
    (hdraw : ∀ i, mid.p384.PrivateKey.draw i (Array.repeat 48#usize 0#u8).to_slice = ok (draws i))
    (hlen : ∀ i, (draws i).2.length = 48) :
    high.agreement.PrivateKey.generate high.agreement.ECDH_P384 ⦃ key => p384Keygen draws 0 64 key ⦄ := by
  unfold high.agreement.PrivateKey.generate high.agreement.ECDH_P384 high.agreement.Algorithm.generate
    high.agreement.Keyed.generate
  simp only [p384Agree_random]
  unfold mid.p384.PrivateKey.generate
  step as ⟨_⟩
  step with generate_loop_spec draws hdraw hlen 64 0 as ⟨r, hr⟩
  rcases r with k | e
  · obtain ⟨hk0, hk, hkey⟩ := drawKeygen_ok draws 64 0 k hr
    simp only [p384Agree_encode_public]
    step with encode_public_key_spec h hsel k _ hk0 hk as ⟨pk, hpk⟩
    step with private_key_spec k pk hpk as ⟨key, hkey'⟩
    exact hkey key hkey'
  · simp only [WP.spec_ok]
    exact drawKeygen_err draws 64 0 e hr

/-- A P-384 key loaded from its scalar is refused unless it is 48 bytes and,
read big-endian, in [1, n), and otherwise is that scalar, as
`p384_generate`'s is a draw's. -/
theorem p384_from_scalar (h : Runs) (hsel : AffSelect) (b : Slice U8) :
    high.agreement.PrivateKey.from_scalar high.agreement.ECDH_P384 b ⦃ key =>
      if b.length = 48 then
        if 0 < beNat b.val ∧ beNat b.val < n384 then
          ∃ key', key = .Ok key' ∧ p384Key (beNat b.val) key'
        else key = core.result.Result.Err (.KeyRejected .ScalarOutOfRange)
      else key = core.result.Result.Err (.KeyRejected .WrongLength) ⦄ := by
  unfold high.agreement.PrivateKey.from_scalar high.agreement.ECDH_P384 high.agreement.Algorithm.load
    high.agreement.Keyed.load
  simp only [p384Agree_load]
  step with load_scalar_spec h hsel _ b as ⟨r, hr⟩
  split_ifs at hr ⊢
  · obtain ⟨k, pk, rfl, hk, hpk⟩ := hr
    simp only
    step with private_key_spec k pk (hk ▸ hpk) as ⟨key', hkey'⟩
    exact ⟨key', rfl, hk ▸ hkey'⟩
  · subst hr
    simp
  · subst hr
    simp

/-- A P-384 key's public key: X9.62's uncompressed encoding of its scalar
times the generator, which `p384_generate` and `p384_from_scalar` show every
key holds. -/
theorem p384_public_key (key : high.agreement.PrivateKey) (d : Nat) (hkey : p384Key d key) :
    (do
      let pk ← high.agreement.PrivateKey.public_key key
      high.agreement.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk) ⦃ b =>
      p384PublicKey d b.val ⦄ := by
  obtain ⟨_, _, _, hpk⟩ := hkey
  simpa [high.agreement.PrivateKey.public_key] using hpk

end rind.x86_64
