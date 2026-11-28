import Rind.Aarch64.MlKemEncrypt
import Rind.Aarch64.Sha3
import Rind.MlKemSample
open Aeneas Aeneas.Std Result rind.spec Spec Spec.MLKEM rind.spec.mlkem rind.spec.s2n

/-!
# ML-KEM's matrix sampling on aarch64

`sample_ntt` over the four-way SHAKE128 (`shake128x4_squeeze_spec`), the
sponge (`squeezing_squeeze_spec`), and s2n-bignum's rejection sampling
(`mlkem_rej_uniform_vartime_axiom`) writes each polynomial of a `k` by `k`
matrix as SHAKE128's first 256 candidates below `q` on its input (`Sampled`),
which `sampleNTT_sampled` shows is FIPS 203's `SampleNTT`. aarch64 has no
eight-way sampler, so this covers every `k`; `sample_transposed_spec` states
`Coeffs::sample` for ML-KEM-768's transposed matrix, and `decoded_new_spec`
`Decoded::new`, whose result `kpke_encrypt_fips` takes. Each assumes that
`SampleNTT` finishes on the matrix's inputs (`Halts`), which no proof shows
for every input.
-/

namespace rind.aarch64

namespace MlKemSample

open MlKemCoding MlKemRoutines MlKemPoly MlKemPke MlKemEncrypt
open MlKemCbd (try_from_mut_spec unwrap_mut_spec)

/-! ## s2n-bignum's rejection sampling keeps `accepted`'s candidates -/

theorem leNat_cons3 (b0 b1 b2 : U8) (rest : List U8) :
    leNat (b0 :: b1 :: b2 :: rest) = b0.val + 256 * b1.val + 65536 * b2.val + 16777216 * leNat rest := by
  simp only [leNat, List.map_cons, Nat.ofDigits_cons]
  ring

theorem wordsOfNum_add2 (n x : ℕ) :
    wordsOfNum 12 (n + 2) x = x % 4096 :: x / 4096 % 4096 :: wordsOfNum 12 n (x / 16777216) := by
  unfold wordsOfNum
  rw [List.range_succ_eq_map, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Function.comp_def, List.cons.injEq]
  refine ⟨by norm_num, by norm_num, List.map_congr_left fun i _ => ?_⟩
  rw [show 12 * (i + 1 + 1) = 24 + 12 * i by ring, pow_add, ← Nat.div_div_eq_div_mul]
  norm_num

/-- The 12-bit words of whole three-byte groups that are below `q` are
`accepted`'s. -/
theorem filter_words (T : ℕ) : ∀ (l : List U8), l.length = 3 * T →
    (wordsOfNum 12 (2 * T) (leNat l)).filter (· < 3329) = accepted (bv l) := by
  induction T with
  | zero =>
    intro l hl
    have : l = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst this
    simp [wordsOfNum, accepted, bv]
  | succ T ih =>
    intro l hl
    match l, hl with
    | b0 :: b1 :: b2 :: rest, hl =>
      have hr : rest.length = 3 * T := by simp at hl; omega
      have h0 : b0.val < 256 := b0.hBounds
      have h1 : b1.val < 256 := b1.hBounds
      have h2 : b2.val < 256 := b2.hBounds
      rw [show 2 * (T + 1) = 2 * T + 2 by ring, wordsOfNum_add2, leNat_cons3,
        show (b0.val + 256 * b1.val + 65536 * b2.val + 16777216 * leNat rest) % 4096 =
          b0.val + 256 * (b1.val % 16) by omega,
        show (b0.val + 256 * b1.val + 65536 * b2.val + 16777216 * leNat rest) / 4096 % 4096 =
          b1.val / 16 + 16 * b2.val by omega,
        show (b0.val + 256 * b1.val + 65536 * b2.val + 16777216 * leNat rest) / 16777216 = leNat rest by omega,
        List.filter_cons, List.filter_cons, ih rest hr]
      simp only [bv, List.map_cons, accepted, keep, Byte.val, UScalar.bv_toNat, q]
      split_ifs <;> simp_all

/-- What `mlkem_rej_uniform_vartime` keeps of a whole number of three-byte
groups is their first 256 candidates below `q`. -/
theorem rejOut_eq (l : List U8) (hl : l.length % 3 = 0) : rejOut l = (accepted (bv l)).take 256 := by
  unfold rejOut
  rw [show 2 * l.length / 3 = 2 * (l.length / 3) by omega, filter_words _ l (by omega)]

/-! ## Filling an output with candidates -/

/-- `out` holds `done` candidates of `W` from `base`: every one `W` has past
`base`, or as many as `out` holds. -/
def Filled (W : List ℕ) (base : ℕ) (out : List I16) (done : ℕ) : Prop :=
  done ≤ out.length ∧ base + done = min (base + out.length) W.length ∧
    ∀ k < done, (out[k]!).val = ((W[base + k]! : ℕ) : ℤ)

/-- A candidate written where there is room. -/
theorem filled_push (W : List ℕ) (base : ℕ) (out : List I16) (done x : ℕ) (v : I16) (hv : v.val = x)
    (h : Filled W base out done) (hd : done < out.length) :
    Filled (W ++ [x]) base (out.set done v) (done + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hW : W.length = base + done := by omega
  refine ⟨by simp; omega, by simp; omega, fun k hk => ?_⟩
  by_cases hkd : k = done
  · subst hkd
    rw [getElem!_pos _ k (by simp; omega), List.getElem_set_self, hv,
      show base + k = W.length + 0 by omega]
    simp
  · rw [getElem!_pos _ k (by simp; omega), List.getElem_set_ne (Ne.symm hkd), ← getElem!_pos _ k (by omega),
      h3 k (by omega), getElem!_pos _ (base + k) (by omega), getElem!_pos _ (base + k) (by simp; omega),
      List.getElem_append_left]

/-- Candidates past a full `out`. -/
theorem filled_full (W K : List ℕ) (base : ℕ) (out : List I16) (done : ℕ)
    (h : Filled W base out done) (hd : ¬ done < out.length) : Filled (W ++ K) base out done := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, by simp; omega, fun k hk => ?_⟩
  rw [h3 k hk, getElem!_pos _ (base + k) (by omega), getElem!_pos _ (base + k) (by simp; omega),
    List.getElem_append_left]

/-! ## `tail_case` -/

theorem q_eq : mid.mlkem.Q = 3329#i16 := by unfold mid.mlkem.Q; rfl

/-- A `u16` below `2 ^ 15`, as an `i16`, holds its value. -/
theorem hcast16 (x : U16) (h : x.val < 2 ^ 15) : (UScalar.hcast .I16 x).val = x.val := by
  rw [UScalar.hcast_val_eq]
  exact Int.bmod_eq_of_le (by simp) (by simp; omega)

/-- `u16::from_le_bytes` of two bytes. -/
theorem u16_of_bytes (b0 b1 : U8) (y : U16) {h}
    (hy : y.bv = (BitVec.fromLEBytes ((Std.Array.make 2#usize [b0, b1]).val.map U8.bv)).cast h) :
    y.val = b0.val + 256 * b1.val := by
  show y.bv.toNat = _
  rw [hy, BitVec.toNat_cast, toNat_fromLEBytes]
  simp [Std.Array.make, Nat.ofDigits_cons]

/-- Block `c` of SHAKE128's output on `M`. -/
def Block (M : List Byte) (c : ℕ) (bytes : List U8) : Prop :=
  ∀ i < 168, (bytes[i]!).bv = xofByte M (168 * c + i)

/-- `keep` of three bytes, as `tail_case` reads them. -/
theorem keep_bv (b0 b1 b2 : U8) :
    keep b0.bv b1.bv b2.bv =
      (if b0.val + 256 * (b1.val % 16) < q then [b0.val + 256 * (b1.val % 16)] else []) ++
        (if b1.val / 16 + 16 * b2.val < q then [b1.val / 16 + 16 * b2.val] else []) := by
  simp only [keep, Byte.val, UScalar.bv_toNat]

/-- The inner loop of `tail_case` writes the candidates of one block. -/
theorem tail_inner_spec (M : List Byte) (c : ℕ) (bytes : Std.Array U8 168#usize) (hb : Block M c bytes.val)
    (base : ℕ) (iter : core.ops.range.Range Usize) (he : iter.end.val = 56) (hs : iter.start.val ≤ 56)
    (output : Slice I16) (done : Usize)
    (hf : Filled (acc M (3 * (56 * c + iter.start.val))) base output.val done.val) :
    mid.mlkem.sample_ntt.tail_case_loop0_loop0 iter output done bytes ⦃ r =>
      r.1.length = output.length ∧ Filled (acc M (3 * (56 * c + 56))) base r.1.val r.2.val ⦄ := by
  unfold mid.mlkem.sample_ntt.tail_case_loop0_loop0
  apply WP.spec_mono (range_loop 56 (fun i (s : Slice I16 × Usize) =>
    s.1.length = output.length ∧ Filled (acc M (3 * (56 * c + i))) base s.1.val s.2.val) _ ?_
    iter (output, done) he hs ⟨rfl, hf⟩)
  · intro r hr; exact hr
  · rintro it ⟨out, d⟩ he' hs' ⟨hl, hinv⟩
    simp only at hl hinv ⊢
    unfold mid.mlkem.sample_ntt.tail_case_loop0_loop0.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨i, hi⟩
      step as ⟨b0, hb0⟩
      step as ⟨i1, hi1⟩
      step as ⟨b1, hb1⟩
      step as ⟨i2, hi2⟩
      step as ⟨b2, hb2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨d1, hd1⟩
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      step as ⟨d2, hd2⟩
      have ht : it.start.val < 56 := by omega
      have hx (k : ℕ) (hk : k < 3) (b : U8) (hb' : b = bytes.val[3 * it.start.val + k]!) :
          b.bv = xofByte M (3 * (56 * c + it.start.val) + k) := by
        rw [hb', hb _ (by omega)]
        congr 1
        ring
      have hx0 := hx 0 (by omega) b0 (by rw [hb0, getElem!_pos bytes.val _ (by simp; omega)]; simp [hi])
      have hx1 := hx 1 (by omega) b1 (by rw [hb1, getElem!_pos bytes.val _ (by simp; omega)]; simp [hi1, hi])
      have hx2 := hx 2 (by omega) b2 (by rw [hb2, getElem!_pos bytes.val _ (by simp; omega)]; simp [hi2, hi])
      simp only [Nat.add_zero] at hx0
      have hsucc := acc_succ M (56 * c + it.start.val)
      rw [← hx0, ← hx1, ← hx2, keep_bv] at hsucc
      have h0 : b0.val < 256 := b0.hBounds
      have h1 : b1.val < 256 := b1.hBounds
      have h2 : b2.val < 256 := b2.hBounds
      have hi3v := u16_of_bytes b0 b1 i3 hi3
      have hi5v := u16_of_bytes b1 b2 i5 hi5
      have hi4v : i4.val = b0.val + 256 * (b1.val % 16) := by
        rw [hi4, UScalar.val_and, show (4095#u16).val = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, hi3v]
        omega
      have hi6v : i6.val = b1.val / 16 + 16 * b2.val := by
        rw [hi6, hi5v, Nat.shiftRight_eq_div_pow]
        omega
      have hd1v : d1.val = ((b0.val + 256 * (b1.val % 16) : ℕ) : ℤ) := by
        rw [hd1, hcast16 _ (by omega), hi4v]
      have hd2v : d2.val = ((b1.val / 16 + 16 * b2.val : ℕ) : ℤ) := by
        rw [hd2, hcast16 _ (by omega), hi6v]
      generalize hW : acc M (3 * (56 * c + it.start.val)) = W at hinv hsucc
      generalize b0.val + 256 * (b1.val % 16) = x1 at hd1v hsucc
      generalize b1.val / 16 + 16 * b2.val = x2 at hd2v hsucc
      apply WP.spec_bind (Pₘ := fun (r : Slice I16 × Usize × core.ops.range.Range Usize) =>
        r.2.2 = it1 ∧ r.1.length = output.length ∧
          Filled (W ++ if x1 < q then [x1] else []) base r.1.val r.2.1.val)
      · split
        · rename_i hq
          rw [q_eq] at hq
          have hc : x1 < q := by
            have : d1.val < 3329 := by scalar_tac
            show x1 < 3329; omega
          simp only [hc, ite_true]
          split
          · rename_i hdl
            have hdl' : d.val < out.length := by scalar_tac
            step as ⟨s1, hs1⟩
            step as ⟨d3, hd3⟩
            refine ⟨by rw [hs1, Slice.set_length]; exact hl, ?_⟩
            rw [hs1, Slice.set_val_eq, hd3]
            exact filled_push W base out.val d.val x1 d1 hd1v hinv hdl'
          · rename_i hdl
            have hdl' : ¬ d.val < out.length := by scalar_tac
            simp only [bind_ok]
            exact (WP.spec_ok _).2 ⟨rfl, hl, filled_full W [x1] base out.val d.val hinv hdl'⟩
        · rename_i hq
          rw [q_eq] at hq
          have hc : ¬ x1 < q := by
            have : ¬ d1.val < 3329 := by scalar_tac
            show ¬ x1 < 3329; omega
          simp only [hc, ite_false, List.append_nil]
          exact (WP.spec_ok _).2 ⟨rfl, hl, hinv⟩
      · rintro ⟨out1, d', it2⟩ ⟨hit, hl1, hf1⟩
        simp only at hit hl1 hf1 ⊢
        subst it2
        simp only [uncurry_apply_pair]
        have hfin (out2 : Slice I16) (d'' : Usize) (hl2 : out2.length = output.length)
            (hf2 : Filled (W ++ (if x1 < q then [x1] else []) ++ if x2 < q then [x2] else []) base out2.val d''.val) :
            it1.end.val = 56 ∧ it1.start.val = it.start.val + 1 ∧ it.start.val < 56 ∧
              out2.length = output.length ∧
              Filled (acc M (3 * (56 * c + it1.start.val))) base out2.val d''.val := by
          refine ⟨by rw [he1]; exact he', hst, ht, hl2, ?_⟩
          rw [hst, show 56 * c + (it.start.val + 1) = 56 * c + it.start.val + 1 by ring, hsucc, ← List.append_assoc]
          exact hf2
        split
        · rename_i hq
          rw [q_eq] at hq
          have hc : x2 < q := by
            have : d2.val < 3329 := by scalar_tac
            show x2 < 3329; omega
          split
          · rename_i hdl
            have hdl' : d'.val < out1.length := by scalar_tac
            step as ⟨s1, hs1⟩
            step as ⟨d3, hd3⟩
            refine hfin s1 d3 (by rw [hs1, Slice.set_length]; exact hl1) ?_
            rw [hs1, Slice.set_val_eq, hd3]
            simp only [hc, ↓reduceIte]
            exact filled_push _ base out1.val d'.val x2 d2 hd2v hf1 hdl'
          · rename_i hdl
            have hdl' : ¬ d'.val < out1.length := by scalar_tac
            apply (WP.spec_ok _).2
            refine hfin _ _ hl1 ?_
            simp only [hc, ↓reduceIte]
            exact filled_full _ [x2] base out1.val d'.val hf1 hdl'
        · rename_i hq
          rw [q_eq] at hq
          have hc : ¬ x2 < q := by
            have : ¬ d2.val < 3329 := by scalar_tac
            show ¬ x2 < 3329; omega
          apply (WP.spec_ok _).2
          refine hfin _ _ hl1 ?_
          simp only [hc, ↓reduceIte, List.append_nil]
          exact hf1
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      have : it.start.val = 56 := by omega
      rw [this] at hinv
      exact ⟨hl, hinv⟩

/-- The block `SqueezingSponge::squeeze` reads after `c` blocks. -/
theorem block_of_squeeze (M : List Byte) (c : ℕ) (out : List U8)
    (hout : bv out = (sponge 168 shakePad M (168 * c + 168)).drop (168 * c)) : Block M c out := by
  intro i hi
  rw [← getElem!_bv, hout, show sponge 168 shakePad M (168 * c + 168) =
    (List.range (168 * c + 168)).map (xofByte M) from rfl, getElem!_pos _ i (by simp; omega)]
  simp

/-- What a turn of `tail_case`'s loop after block `c` leaves: the next
block's candidates, or `output` filled. -/
def TailStep (M : List Byte) (T base c : ℕ) (output : Slice I16) :
    ControlFlow (mid.sha3.SqueezingSponge 168#usize × Slice I16 × Usize)
      (mid.sha3.SqueezingSponge 168#usize × Slice I16) → Prop
  | .cont x => Squeezing x.1 shakePad M (c + 1) ∧ x.2.1.length = output.length ∧
      Filled (acc M (168 * (c + 1))) base x.2.1.val x.2.2.val ∧ 56 * c < T
  | .done y => y.2.length = output.length ∧
      ∀ k < output.length, (y.2.val[k]!).val = (((acc M (3 * T))[base + k]! : ℕ) : ℤ)

/-- `tail_case`'s loop, from block `c` of SHAKE128 on `M`, fills `output`
with the candidates past `base`, given that the first `3 * T` bytes hold
enough of them. -/
theorem tail_loop_spec (h : RunsSha3) (M : List Byte) (T base : ℕ) (n : ℕ) :
    ∀ c, T - 56 * c = n → ∀ (sponge : mid.sha3.SqueezingSponge 168#usize) (output : Slice I16) (done : Usize),
      Squeezing sponge shakePad M c → Filled (acc M (168 * c)) base output.val done.val →
      base + output.length ≤ (acc M (3 * T)).length →
      mid.mlkem.sample_ntt.tail_case_loop0 sponge output done ⦃ r =>
        r.2.length = output.length ∧
          ∀ k < output.length, (r.2.val[k]!).val = (((acc M (3 * T))[base + k]! : ℕ) : ℤ) ⦄ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hn sponge output done hs hf hT
  unfold mid.mlkem.sample_ntt.tail_case_loop0
  unfold loop
  apply WP.spec_bind (Pₘ := TailStep M T base c output)
  · unfold mid.mlkem.sample_ntt.tail_case_loop0.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : done.val < output.length := by scalar_tac
      step with Std.Array.to_slice_mut_spec as ⟨s, back, hsv, hback⟩
      have hsl : s.length = 168 := by simp [Slice.length, hsv]
      step with squeezing_squeeze_spec h (R := 168#usize) (by decide) sponge shakePad M c hs s
        as ⟨sp1, s1, hl1, hout1, hsq1⟩
      step with shake128_r_bytes as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hbv : (back s1).val = s1.val := by
        rw [hback, Std.Array.from_slice_val _ _ (by rw [← Slice.length, hl1, hsl]; rfl)]
      have hb : Block M c (back s1).val := by
        rw [hbv]
        refine block_of_squeeze M c s1.val ?_
        rw [hout1, hsl]
      have hf0 : Filled (acc M (3 * (56 * c + 0))) base output.val done.val := by
        rw [show 3 * (56 * c + 0) = 168 * c by ring]; exact hf
      step with tail_inner_spec M c (back s1) hb base { start := 0#usize, «end» := i2 }
        (by simp; omega) (by simp) output done hf0 as ⟨out1, d1, hl2, hf2⟩
      refine ⟨?_, hl2, ?_, ?_⟩
      · rw [hsl] at hsq1; exact hsq1
      · rw [show 168 * (c + 1) = 3 * (56 * c + 56) by ring]; exact hf2
      · by_contra hc
        have := acc_length_mono M (show 3 * T ≤ 168 * c by omega)
        have hol : output.length = output.val.length := rfl
        obtain ⟨_, hf2', _⟩ := hf
        omega
    · rename_i hlt
      have hlt' : ¬ done.val < output.length := by scalar_tac
      apply (WP.spec_ok _).2
      obtain ⟨hd, hb, hv⟩ := hf
      have hol : output.length = output.val.length := rfl
      refine ⟨rfl, fun k hk => ?_⟩
      rw [hv k (by omega), acc_agree M (168 * c) (3 * T) (base + k) (by omega) (by omega)]
  · rintro (⟨s', out', d'⟩ | ⟨s', out'⟩) hr
    · obtain ⟨hs', hl', hf', hc⟩ := hr
      have := ih (T - 56 * (c + 1)) (by omega) (c + 1) rfl s' out' d' hs' hf' (by rw [hl']; exact hT)
      unfold mid.mlkem.sample_ntt.tail_case_loop0 at this
      rw [hl'] at this
      exact this
    · exact (WP.spec_ok _).2 hr

/-- `tail_case` fills `output` with the candidates after those of the first
`c` blocks. -/
theorem tail_case_spec (h : RunsSha3) (M : List Byte) (T c : ℕ) (sponge : mid.sha3.SqueezingSponge 168#usize)
    (hs : Squeezing sponge shakePad M c) (output : Slice I16)
    (hT : (acc M (168 * c)).length + output.length ≤ (acc M (3 * T)).length) :
    mid.mlkem.sample_ntt.tail_case sponge output ⦃ r =>
      r.2.length = output.length ∧ ∀ k < output.length,
        (r.2.val[k]!).val = (((acc M (3 * T))[(acc M (168 * c)).length + k]! : ℕ) : ℤ) ⦄ :=
  tail_loop_spec h M T _ _ c rfl sponge output 0#usize hs ⟨by simp, by simp, fun k hk => by simp at hk⟩ hT

/-! ## `sample_from`, `sample_into`, and `sample_poly_ntt_4x` -/

/-- `out` holds SHAKE128's first 256 candidates below `q` on `M`. -/
def Sampled (M : List Byte) (out : List I16) : Prop :=
  ∀ k < 256, (out[k]!).val = (((sampled M)[k]! : ℕ) : ℤ)

/-- `sample_from` writes SHAKE128's first 256 candidates on `M`, from
`samples`, its first three blocks, then from `sponge`, which continues after
them. -/
theorem sample_from_spec (h : RunsSha3) (M : List Byte) (hH : Halts M)
    (samples : Std.Array U8 504#usize) (hsm : bv samples.val = shake128 M 504)
    (sponge : mid.sha3.SqueezingSponge 168#usize) (hs : Squeezing sponge shakePad M 3)
    (output : Std.Array I16 256#usize) :
    mid.mlkem.sample_ntt.sample_from samples sponge output ⦃ r => Sampled M r.2.val ⦄ := by
  obtain ⟨T, hT⟩ := hH
  unfold mid.mlkem.sample_ntt.sample_from
  step as ⟨s, hsv⟩
  have hsl : s.val.length = 504 := by simp [hsv]
  have hrej : rejOut s.val = (acc M 504).take 256 := by
    rw [rejOut_eq _ (by rw [hsl]), hsv, Std.Array.val_to_slice, hsm]
  step with mlkem_rej_uniform_vartime_axiom output s (by simp [Slice.length, hsl]) as ⟨i, out1, hi, hout1⟩
  rw [hrej] at hi hout1
  step as ⟨used, hused⟩
  have hlen : ((acc M 504).take 256).length = min 256 (acc M 504).length := by simp
  have hused' : used.val = i.val := by
    have : i.val ≤ 256 := by omega
    rw [hused, UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  have hfirst (k : ℕ) (hk : k < ((acc M 504).take 256).length) :
      (out1.val[k]!).val = (((acc M (3 * T))[k]! : ℕ) : ℤ) := by
    rw [hout1 k hk, take_getElem! _ _ _ (by omega), acc_agree M 504 (3 * T) k (by omega) (by omega)]
  unfold Sampled
  split
  · rename_i hu
    rw [N_eq] at hu
    have hu' : used.val < 256 := by scalar_tac
    have h504 : (acc M (168 * 3)).length = used.val := by
      rw [show 168 * 3 = 504 from rfl]; omega
    step as ⟨s1, back, hs1, hs1l, hback⟩
    have hs1l' : s1.length = 256 - used.val := by rw [hs1l]
    step with tail_case_spec h M T 3 sponge hs s1 (by rw [h504, hs1l']; omega) as ⟨sp2, s2, hl2, hv2⟩
    intro k hk
    rw [hback, sampled_getElem! M T hT k hk]
    by_cases hku : k < used.val
    · rw [List.getElem!_setSlice!_prefix _ _ _ _ hku]
      exact hfirst k (by omega)
    · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by rw [← Slice.length, hl2, hs1l']; omega,
        by simp; omega⟩, hv2 (k - used.val) (by rw [hs1l']; omega), h504,
        show used.val + (k - used.val) = k by omega]
  · rename_i hu
    rw [N_eq] at hu
    have hu' : ¬ used.val < 256 := by scalar_tac
    apply (WP.spec_ok _).2
    intro k hk
    rw [sampled_getElem! M T hT k hk]
    exact hfirst k (by omega)

/-- `sample_into` writes SHAKE128's first 256 candidates on `M`, from a
sponge that has absorbed it. -/
theorem sample_into_spec (h : RunsSha3) (M : List Byte) (hH : Halts M)
    (sponge : mid.sha3.SqueezingSponge 168#usize) (hs : Squeezing sponge shakePad M 0)
    (output : Std.Array I16 256#usize) :
    mid.mlkem.sample_ntt.sample_into sponge output ⦃ r => Sampled M r.val ⦄ := by
  unfold mid.mlkem.sample_ntt.sample_into
  step with Std.Array.to_slice_mut_spec as ⟨s, back, hsv, hback⟩
  have hsl : s.length = 504 := by
    show s.val.length = 504
    rw [hsv]
    exact (Std.Array.repeat 504#usize 0#u8).property
  step with squeezing_squeeze_spec h (R := 168#usize) (by decide) sponge shakePad M 0 hs s
    as ⟨sp1, s1, hl1, hout1, hsq1⟩
  have hbv : (back s1).val = s1.val := by
    rw [hback, Std.Array.from_slice_val _ _ (by rw [← Slice.length, hl1, hsl]; rfl)]
  rw [hsl] at hsq1
  step with sample_from_spec h M hH (back s1) (by rw [hbv, hout1, hsl]; rfl) sp1 hsq1 output
    as ⟨sp2, out2, hv⟩
  exact hv

/-- `sample_poly_ntt_4x` writes SHAKE128's first 256 candidates on each of
its four inputs. -/
theorem sample_poly_ntt_4x_spec (h : RunsSha3) (M : ℕ → List Byte) (hH : ∀ j < 4, Halts (M j))
    (inputs : Std.Array (Std.Array U8 40#usize) 4#usize) (hin : Shake128Inputs inputs M)
    (outputs : Std.Array (Std.Array I16 256#usize) 4#usize) :
    mid.mlkem.sample_ntt.sample_poly_ntt_4x inputs outputs ⦃ r =>
      ∀ j < 4, Sampled (M j) (r.val[j]!).val ⦄ := by
  unfold mid.mlkem.sample_ntt.sample_poly_ntt_4x
  step with shake128x4_new_spec h M inputs hin as ⟨x, hx⟩
  step with shake128x4_squeeze_spec h x M hx as ⟨sp, smp, hsq⟩
  unfold mid.mlkem.sample_ntt.sample_poly_ntt_4x_loop
  apply WP.spec_mono (range_loop' 4 (fun i (s : Std.Array (Std.Array I16 256#usize) 4#usize ×
      Std.Array (mid.sha3.SqueezingSponge 168#usize) 4#usize) =>
      (∀ j < i, Sampled (M j) (s.1.val[j]!).val) ∧ ∀ j, i ≤ j → j < 4 → Squeezing (s.2.val[j]!) shakePad (M j) 3)
    (fun r => ∀ j < 4, Sampled (M j) (r.val[j]!).val) _ ?_ { start := 0#usize, «end» := 4#usize } (outputs, sp) (by simp) (by simp)
    ⟨fun j hj => absurd hj (by simp), fun j _ hj => (hsq j hj).2⟩)
  · intro r hr; exact hr
  · rintro it ⟨outs, sps⟩ he hs ⟨hdone, hsps⟩
    simp only at hdone hsps ⊢
    unfold mid.mlkem.sample_ntt.sample_poly_ntt_4x_loop.body
    step as ⟨o, it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      have ht : it.start.val < 4 := by omega
      step as ⟨a, ha⟩
      step as ⟨ss, back, hss, hback⟩
      step as ⟨a1, back1, ha1, hback1⟩
      have hsm : bv a.val = shake128 (M it.start.val) 504 := by
        rw [ha, ← getElem!_pos smp.val it.start.val (by simp; omega)]
        exact (hsq _ ht).1
      have hss' : Squeezing ss shakePad (M it.start.val) 3 := by
        rw [hss, ← getElem!_pos sps.val it.start.val (by simp; omega)]
        exact hsps _ le_rfl ht
      step with sample_from_spec h (M it.start.val) (hH _ ht) a hsm ss hss' a1
        as ⟨ss1, a2, hv⟩
      refine ⟨by rw [he1]; exact he, hst, ht, ?_, ?_⟩
      · intro j hj
        rw [hback1, hst] at *
        rw [Std.Array.set_val_eq]
        by_cases hji : j = it.start.val
        · subst hji
          rw [getElem!_set_self _ _ _ (by simp; omega)]
          exact hv
        · rw [getElem!_set_ne _ _ _ _ (Ne.symm hji)]
          exact hdone j (by omega)
      · intro j hj hj4
        rw [hback, Std.Array.set_val_eq, getElem!_set_ne _ _ _ _ (by omega)]
        exact hsps j (by omega) hj4
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      have : it.start.val = 4 := by omega
      rw [this] at hdone
      exact hdone

/-! ## `sample_ntt` -/

/-- `shake_input` lays out `ρ`, the two indices, and SHAKE128's padding. -/
theorem shake_input_spec (rho : Std.Array U8 32#usize) (transposed : Bool) (i j : U8) :
    mid.mlkem.sample_ntt.shake_input rho transposed i j ⦃ input =>
      bv input.val = (bv rho.val ++ if transposed then [i.bv, j.bv] else [j.bv, i.bv]) ++
        shakePad :: List.replicate 5 0 ⦄ := by
  unfold mid.mlkem.sample_ntt.shake_input
  step as ⟨s, back, hs, hsl, hback⟩
  step as ⟨s1, hs1⟩
  step as ⟨s2, hs2⟩
  have hr : rho.val.length = 32 := rho.property
  have hb : (back s2).val = rho.val ++ List.replicate 8 0#u8 := by
    rw [hback, hs2, hs1, Std.Array.val_to_slice]
    simp [List.setSlice!, hr]
  split
  · step as ⟨a, ha⟩
    step as ⟨a1, ha1⟩
    step as ⟨a2, ha2⟩
    rw [ha2, ha1, ha, shake_pad_byte_eq]
    simp only [Std.Array.set_val_eq, hb]
    simp [hr, bv, List.replicate]
    rfl
  · step as ⟨a, ha⟩
    step as ⟨a1, ha1⟩
    step as ⟨a2, ha2⟩
    rw [ha2, ha1, ha, shake_pad_byte_eq]
    simp only [Std.Array.set_val_eq, hb]
    simp [hr, bv, List.replicate]
    rfl

/-- The SHAKE128 input of polynomial `p` of a `k` by `k` matrix, row by row:
`ρ`, then its column and row, or its row and column for the transpose. -/
def matMsg (rho : List Byte) (transposed : Bool) (k p : ℕ) : List Byte :=
  rho ++ if transposed then [((p / k : ℕ) : Byte), ((p % k : ℕ) : Byte)]
    else [((p % k : ℕ) : Byte), ((p / k : ℕ) : Byte)]

theorem matMsg_length (rho : List Byte) (transposed : Bool) (k p : ℕ) :
    (matMsg rho transposed k p).length = rho.length + 2 := by
  unfold matMsg; split <;> simp

theorem u8_bv (x : U8) (n : ℕ) (h : x.val = n) : x.bv = (n : Byte) := by
  apply BitVec.eq_of_toNat_eq
  show x.val = _
  rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, ← h]
  exact (Nat.mod_eq_of_lt (by scalar_tac)).symm

/-- The position after `p`: the next column, or the next row's first. -/
theorem next_pos (k p : ℕ) (hk : 0 < k) :
    (p + 1) / k = (if p % k + 1 = k then p / k + 1 else p / k) ∧
      (p + 1) % k = (if p % k + 1 = k then 0 else p % k + 1) := by
  have hdm := Nat.div_add_mod p k
  split
  · have : p + 1 = k * (p / k + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [this, Nat.mul_div_cancel_left _ hk, Nat.mul_mod_right]
    exact ⟨rfl, rfl⟩
  · have hlt : p % k + 1 < k := by have := Nat.mod_lt p hk; omega
    have : p + 1 = (p % k + 1) + k * (p / k) := by omega
    rw [this, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hlt, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hlt]
    exact ⟨by omega, rfl⟩

/-- `next_index` steps from position `p` of a `k` by `k` matrix to `p + 1`. -/
theorem next_index_spec (k : Usize) (hk : 0 < k.val ∧ k.val ≤ 4) (p : ℕ) (hp : p < k.val * k.val)
    (i j : U8) (hi : i.val = p / k.val) (hj : j.val = p % k.val) :
    mid.mlkem.sample_ntt.next_index k i j ⦃ r =>
      r.1.val = (p + 1) / k.val ∧ r.2.val = (p + 1) % k.val ⦄ := by
  unfold mid.mlkem.sample_ntt.next_index
  have hik : p / k.val < k.val := Nat.div_lt_of_lt_mul hp
  have hjk : p % k.val < k.val := Nat.mod_lt p hk.1
  obtain ⟨hn1, hn2⟩ := next_pos k.val p hk.1
  step as ⟨i1, hi1⟩
  have hi1' : i1.val = j.val := by
    rw [hi1, UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by have := j.hBounds; scalar_tac)
  step as ⟨i2, hi2⟩
  split
  · rename_i he
    have he' : p % k.val + 1 = k.val := by
      have : i2.val = k.val := by rw [he]
      omega
    simp only [he', ↓reduceIte] at hn1 hn2
    step as ⟨i3, hi3⟩
    exact ⟨by rw [hn1]; omega, by rw [hn2]; rfl⟩
  · rename_i he
    have he' : ¬ p % k.val + 1 = k.val := by
      intro h'
      exact he (by scalar_tac)
    simp only [he', ↓reduceIte] at hn1 hn2
    step as ⟨i3, hi3⟩
    exact ⟨by rw [hn1]; omega, by rw [hn2]; omega⟩

/-- `shake_input` of position `p`'s row and column. -/
theorem shake_input_pos (rho : Std.Array U8 32#usize) (transposed : Bool) (k p : ℕ) (i j : U8)
    (hi : i.val = p / k) (hj : j.val = p % k) :
    mid.mlkem.sample_ntt.shake_input rho transposed i j ⦃ input =>
      bv input.val = matMsg (bv rho.val) transposed k p ++ shakePad :: List.replicate 5 0 ⦄ := by
  apply WP.spec_mono (shake_input_spec rho transposed i j)
  intro input h'
  rw [h', u8_bv i _ hi, u8_bv j _ hj]
  rfl

/-- The inputs `sample_ntt` builds for four polynomials from position `p0`. -/
def Inputs4 (rho : List Byte) (transposed : Bool) (k p0 n : ℕ) (inputs : Std.Array (Std.Array U8 40#usize) 4#usize) :
    Prop :=
  ∀ u < n, bv (inputs.val[u]!).val = matMsg rho transposed k (p0 + u) ++ shakePad :: List.replicate 5 0

/-- `sample_ntt`'s inner loop lays out four polynomials' inputs from
position `p0`. -/
theorem inputs_loop_spec (rho : Std.Array U8 32#usize) (transposed : Bool) (k : Usize)
    (hk : 0 < k.val ∧ k.val ≤ 4) (p0 : ℕ) (hp0 : p0 + 4 ≤ k.val * k.val)
    (iter : core.ops.range.Range Usize) (he : iter.end.val = 4) (hs : iter.start.val ≤ 4)
    (i j : U8) (hi : i.val = (p0 + iter.start.val) / k.val) (hj : j.val = (p0 + iter.start.val) % k.val)
    (inputs : Std.Array (Std.Array U8 40#usize) 4#usize)
    (hin : Inputs4 (bv rho.val) transposed k.val p0 iter.start.val inputs) :
    mid.mlkem.sample_ntt.sample_ntt_loop0_loop0 iter rho transposed k i j inputs ⦃ r =>
      r.1.val = (p0 + 4) / k.val ∧ r.2.1.val = (p0 + 4) % k.val ∧
        Inputs4 (bv rho.val) transposed k.val p0 4 r.2.2 ⦄ := by
  unfold mid.mlkem.sample_ntt.sample_ntt_loop0_loop0
  apply WP.spec_mono (range_loop 4 (fun t (s : U8 × U8 × Std.Array (Std.Array U8 40#usize) 4#usize) =>
    s.1.val = (p0 + t) / k.val ∧ s.2.1.val = (p0 + t) % k.val ∧
      Inputs4 (bv rho.val) transposed k.val p0 t s.2.2) _ ?_ iter (i, j, inputs) he hs ⟨hi, hj, hin⟩)
  · intro r hr; exact hr
  · rintro it ⟨i', j', ins⟩ he' hs' ⟨hi', hj', hin'⟩
    simp only at hi' hj' hin' ⊢
    unfold mid.mlkem.sample_ntt.sample_ntt_loop0_loop0.body
    step as ⟨o, it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step with shake_input_pos rho transposed k.val (p0 + it.start.val) i' j' hi' hj' as ⟨a, ha⟩
      step as ⟨a1, ha1⟩
      step with next_index_spec k hk (p0 + it.start.val) (by omega) i' j' hi' hj' as ⟨i2, j2, hi2, hj2⟩
      refine ⟨by rw [he1]; exact he', hst, by omega, ?_, ?_, ?_⟩
      · rw [hi2, hst]; rfl
      · rw [hj2, hst]; rfl
      · intro u hu
        rw [ha1, Std.Array.set_val_eq]
        by_cases hu' : u = it.start.val
        · subst hu'
          rw [getElem!_set_self _ _ _ (by simp; omega)]
          exact ha
        · rw [getElem!_set_ne _ _ _ _ (Ne.symm hu')]
          exact hin' u (by omega)
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      have : it.start.val = 4 := by omega
      rw [this] at hi' hj' hin'
      exact ⟨hi', hj', hin'⟩

/-- `out`'s first `n` polynomials are those `SampleNTT` gives the matrix's. -/
def MatSampled (rho : List Byte) (transposed : Bool) (k n : ℕ) (out : List Poly) : Prop :=
  ∀ p < n, Sampled (matMsg rho transposed k p) (out[p]!).val

/-- `sample_ntt`'s loop state: `done` polynomials sampled, at the row and
column of the next. -/
def MatInv (rho : Std.Array U8 32#usize) (transposed : Bool) (k : Usize)
    (s : Slice Poly × U8 × U8 × Usize) : Prop :=
  s.1.length = k.val * k.val ∧ s.2.2.2.val ≤ k.val * k.val ∧ s.2.1.val = s.2.2.2.val / k.val ∧
    s.2.2.1.val = s.2.2.2.val % k.val ∧ MatSampled (bv rho.val) transposed k.val s.2.2.2.val s.1.val

/-- `sample_ntt`'s first loop samples four polynomials at a time while four
remain. -/
theorem batches_spec (h : RunsSha3) (rho : Std.Array U8 32#usize) (transposed : Bool) (k : Usize)
    (hk : 0 < k.val ∧ k.val ≤ 4)
    (hH : ∀ p < k.val * k.val, Halts (matMsg (bv rho.val) transposed k.val p))
    (out : Slice Poly) (i j : U8) (done : Usize) (hinv : MatInv rho transposed k (out, i, j, done)) :
    mid.mlkem.sample_ntt.sample_ntt_loop0 rho transposed out k i j done ⦃ r =>
      MatInv rho transposed k r ∧ k.val * k.val < r.2.2.2.val + 4 ⦄ := by
  unfold mid.mlkem.sample_ntt.sample_ntt_loop0
  apply loop.spec_decr_nat (fun x => k.val * k.val - x.2.2.2.val) (MatInv rho transposed k) _ _ _ ?_ hinv
  rintro ⟨o, i', j', d⟩ ⟨hl', hd', hi', hj', hs'⟩
  simp only at hl' hd' hi' hj' hs' ⊢
  unfold mid.mlkem.sample_ntt.sample_ntt_loop0.body
  have hK : k.val * k.val ≤ 16 := Nat.mul_le_mul hk.2 hk.2 |>.trans (by norm_num)
  step as ⟨i1, hi1⟩
  split
  · rename_i hle
    have hle' : d.val + 4 ≤ k.val * k.val := by
      have : i1.val ≤ o.length := by scalar_tac
      omega
    step with inputs_loop_spec rho transposed k hk d.val hle' { start := 0#usize, «end» := 4#usize }
      (by simp) (by simp) i' j' (by simpa using hi') (by simpa using hj') _
      (fun u hu => absurd hu (by simp)) as ⟨i3, j1, ins, hi3, hj1, hins⟩
    step as ⟨i4, hi4⟩
    step as ⟨s, back, hsv, hsl, hback⟩
    step with try_from_mut_spec 4#usize s (by rw [hsl]; scalar_tac) as ⟨r1, tback, hr1, htback⟩
    subst hr1
    step with unwrap_mut_spec core.fmt.DebugTryFromSliceError _ as ⟨outs, uback, houts, huback⟩
    subst houts
    have hrl : (bv rho.val).length = 32 := by rw [bv_length]; exact rho.property
    step with sample_poly_ntt_4x_spec h (fun u => matMsg (bv rho.val) transposed k.val (d.val + u))
      (fun u hu => hH _ (by omega)) ins
      (fun u hu => ⟨by rw [matMsg_length, hrl], hins u hu⟩) _ as ⟨outs1, hv⟩
    have hval : (back (tback (uback outs1))).val = o.val.setSlice! d.val outs1.val := by
      rw [hback, Slice.setSlice!_val, huback, htback]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> try dsimp only
    · rw [hback, Slice.setSlice!_length]; exact hl'
    · omega
    · rw [hi3, hi4]
    · rw [hj1, hi4]
    · intro p hp
      rw [hval]
      by_cases hpd : p < d.val
      · rw [List.getElem!_setSlice!_prefix _ _ _ _ hpd]
        exact hs' p hpd
      · have hol : outs1.val.length = 4 := outs1.property
        rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by omega, by
          have : o.val.length = k.val * k.val := hl'
          omega⟩]
        have := hv (p - d.val) (by omega)
        rwa [show d.val + (p - d.val) = p by omega] at this
    · omega
  · rename_i hle
    apply (WP.spec_ok _).2
    exact ⟨⟨hl', hd', hi', hj', hs'⟩, by scalar_tac⟩

/-- `sample_ntt`'s second loop samples the polynomials left one at a time. -/
theorem singles_spec (h : RunsSha3) (rho : Std.Array U8 32#usize) (transposed : Bool) (k : Usize)
    (hk : 0 < k.val ∧ k.val ≤ 4)
    (hH : ∀ p < k.val * k.val, Halts (matMsg (bv rho.val) transposed k.val p))
    (out : Slice Poly) (i j : U8) (done : Usize) (hinv : MatInv rho transposed k (out, i, j, done)) :
    mid.mlkem.sample_ntt.sample_ntt_loop1 rho transposed out k i j done ⦃ r =>
      r.length = k.val * k.val ∧ MatSampled (bv rho.val) transposed k.val (k.val * k.val) r.val ⦄ := by
  unfold mid.mlkem.sample_ntt.sample_ntt_loop1
  apply loop.spec_decr_nat (fun x => k.val * k.val - x.2.2.2.val) (MatInv rho transposed k) _ _ _ ?_ hinv
  rintro ⟨o, i', j', d⟩ ⟨hl', hd', hi', hj', hs'⟩
  simp only at hl' hd' hi' hj' hs' ⊢
  unfold mid.mlkem.sample_ntt.sample_ntt_loop1.body
  have hK : k.val * k.val ≤ 16 := Nat.mul_le_mul hk.2 hk.2 |>.trans (by norm_num)
  dsimp only
  split
  · rename_i hlt
    have hlt' : d.val < k.val * k.val := by
      have : d.val < o.length := by scalar_tac
      omega
    step with shake_input_pos rho transposed k.val d.val i' j' hi' hj' as ⟨input, hin⟩
    step with next_index_spec k hk d.val hlt' i' j' hi' hj' as ⟨i2, j1, hi2, hj1⟩
    step with sponge_new_spec 168#usize (by decide) 31#u8 as ⟨sp, hsp⟩
    step as ⟨s, hsv, hsl⟩
    step with sponge_absorb_spec h (R := 168#usize) (by decide) sp [] hsp s as ⟨sp1, hsp1⟩
    step with sponge_finish_spec (R := 168#usize) (by decide) sp1 _ hsp1 as ⟨ss, hss⟩
    have hrl : (bv rho.val).length = 32 := by rw [bv_length]; exact rho.property
    have hm : [] ++ bv s.val = matMsg (bv rho.val) transposed k.val d.val := by
      rw [List.nil_append, hsv, Std.Array.val_to_slice]
      simp only [List.slice, List.drop_zero, Nat.sub_zero]
      have ht : bv (List.take 34 input.val) = (bv input.val).take 34 := by simp [bv, List.map_take]
      rw [ht, hin, List.take_append_of_le_length (by rw [matMsg_length, hrl]),
        List.take_of_length_le (by rw [matMsg_length, hrl])]
    rw [hm] at hss
    replace hss : Squeezing ss shakePad (matMsg (bv rho.val) transposed k.val d.val) 0 := hss
    step as ⟨a, back, ha, hback⟩
    step with sample_into_spec h _ (hH d.val hlt') ss hss a as ⟨a1, ha1⟩
    step as ⟨d1, hd1⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> try dsimp only
    · rw [hback, Slice.set_length]; exact hl'
    · omega
    · rw [hi2, hd1]
    · rw [hj1, hd1]
    · intro p hp
      rw [hback, Slice.set_val_eq]
      by_cases hpd : p = d.val
      · subst hpd
        rw [getElem!_set_self _ _ _ (by
          have : o.val.length = k.val * k.val := hl'
          omega)]
        exact ha1
      · rw [getElem!_set_ne _ _ _ _ (Ne.symm hpd)]
        exact hs' p (by omega)
    · omega
  · rename_i hlt
    apply (WP.spec_ok _).2
    have : d.val = k.val * k.val := by
      have : ¬ d.val < o.length := by scalar_tac
      have : o.val.length = k.val * k.val := hl'
      simp only [Slice.length] at *
      omega
    rw [this] at hs'
    exact ⟨hl', hs'⟩

/-- `sample_ntt` writes each polynomial of a `k` by `k` matrix, row by row,
or of its transpose: those `SampleNTT` gives, as SHAKE128's first 256
candidates below `q`. -/
theorem sample_ntt_spec (h : RunsSha3) (rho : Std.Array U8 32#usize) (transposed : Bool) (k : ℕ)
    (out : Slice Poly) (hl : out.length = k * k) (hk : k = 2 ∨ k = 3 ∨ k = 4)
    (hH : ∀ p < k * k, Halts (matMsg (bv rho.val) transposed k p)) :
    mid.mlkem.sample_ntt.sample_ntt rho transposed out ⦃ r =>
      r.length = k * k ∧ MatSampled (bv rho.val) transposed k (k * k) r.val ⦄ := by
  unfold mid.mlkem.sample_ntt.sample_ntt
  have hlen : (Slice.len out).val = k * k := by rw [Slice.len_val]; exact hl
  have hrank : ∃ kk : Usize, mid.mlkem.rank (Slice.len out) = ok kk ∧ kk.val = k := by
    unfold mid.mlkem.rank
    rw [hlen]
    rcases hk with rfl | rfl | rfl
    · exact ⟨2#usize, rfl, rfl⟩
    · exact ⟨3#usize, rfl, rfl⟩
    · exact ⟨4#usize, rfl, rfl⟩
  obtain ⟨kk, hrank, hkv⟩ := hrank
  simp only [hrank, bind_ok]
  have hk' : 0 < kk.val ∧ kk.val ≤ 4 := by rw [hkv]; omega
  step with batches_spec h rho transposed kk hk' (by rw [hkv]; exact hH) out 0#u8 0#u8 0#usize
    ⟨by rw [hkv]; exact hl, by simp, by simp, by simp, fun p hp => absurd hp (by simp)⟩
    as ⟨o1, i1, j1, d1, hinv, _⟩
  step with singles_spec h rho transposed kk hk' (by rw [hkv]; exact hH) o1 i1 j1 d1 hinv
    as ⟨r, hr, hs⟩
  rw [hkv] at hr hs
  exact ⟨hr, hs⟩

/-! ## `Coeffs::sample` -/

/-- On aarch64, `Coeffs::sample`'s unpacking leaves each polynomial as it is:
s2n-bignum's routines take rind's layout. -/
theorem unpack_loop_spec (n : ℕ) (polys : Slice Poly) (hl : polys.length = n)
    (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = n) :
    mid.mlkem.CoeffsMNtt.sample_loop it polys ⦃ y =>
      y.length = n ∧ ∀ j < n, y.val[j]! = polys.val[j]! ⦄ := by
  unfold mid.mlkem.CoeffsMNtt.sample_loop
  apply WP.spec_mono (slice_loop n (fun _ _ _ => True) (fun _ a b => b = a) _ ?_ polys hl
    (fun _ _ => trivial) it hs he)
  · intro y hy
    exact hy
  · intro it s he hs hl' _
    simp only
    unfold mid.mlkem.CoeffsMNtt.sample_loop.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨a, back', ha, hb⟩
      subst hb
      simp only [low.generic.mlkem.mlkem_unpack, bind_ok]
      apply (WP.spec_ok _).2
      refine ⟨by rw [he1]; exact he, hst, by omega, by rw [set_length]; exact hl',
        by rw [set_getElem!_self _ _ _ (by omega), ha, getElem!_pos], fun j hj => set_getElem!_ne _ _ _ _ hj⟩
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      exact ⟨by omega, rfl⟩

/-- `Coeffs::sample` of ML-KEM-768's matrix, or its transpose: each
polynomial is SHAKE128's first 256 candidates below `q` on its input. -/
theorem coeffs_sample_spec (h : RunsSha3) (inst : mid.mlkem.FixedArray Mat Poly) (hi : IsArray inst)
    (rho : Std.Array U8 32#usize) (transposed : Bool)
    (hH : ∀ p < 9, Halts (matMsg (bv rho.val) transposed 3 p)) :
    mid.mlkem.CoeffsMNtt.sample inst rho transposed ⦃ r =>
      MatSampled (bv rho.val) transposed 3 9 r.1.val ⦄ := by
  unfold mid.mlkem.CoeffsMNtt.sample
  simp only [hi.filled, hi.as_mut, bind_ok]
  step as ⟨polys, back, hpv, hpl, hback⟩
  step with sample_ntt_spec h rho transposed 3 polys hpl (by decide) hH as ⟨polys1, hl1, hs1⟩
  step with unpack_loop_spec 9 polys1 hl1 { start := 0#usize, «end» := Slice.len polys1 } rfl
    (by rw [Slice.len_val]; exact hl1) as ⟨polys2, hl2, hq2⟩
  apply (WP.spec_ok _).2
  intro p hp
  rw [hback _ hl2, hq2 p hp]
  exact hs1 p hp

/-- Polynomial `3i + j` of ML-KEM-768's transposed matrix is SHAKE128's on
`ρ ‖ i ‖ j`. -/
theorem matMsg_transposed (rho : List Byte) (i j : ℕ) (hj : j < 3) :
    matMsg rho true 3 (3 * i + j) = rho ++ [(i : Byte), (j : Byte)] := by
  unfold matMsg
  rw [show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega]
  rfl

theorem vappend_toList {α : Type} {m n : ℕ} (a : Vector α m) (b : Vector α n) :
    (Vector.append a b).toList = a.toList ++ b.toList :=
  Vector.toList_append

open scoped Spec.Notations in
/-- `Coeffs::sample` of ML-KEM-768's transposed matrix: polynomial `3i + j`
is FIPS 203's `SampleNTT(ρ ‖ i ‖ j)`, the matrix's entry in row `j` and column
`i`, given that `SampleNTT` finishes on each. -/
theorem sample_transposed_spec (h : RunsSha3) (inst : mid.mlkem.FixedArray Mat Poly) (hi : IsArray inst)
    (rho : Std.Array U8 32#usize) (ρ : 𝔹 32) (hρ : bv rho.val = ρ.toList)
    (hH : ∀ i : ℕ, i < 3 → ∀ j : ℕ, j < 3 → Halts (ρ ‖ #v[(i : Byte)] ‖ #v[(j : Byte)]).toList) :
    mid.mlkem.CoeffsMNtt.sample inst rho true ⦃ r =>
      ∀ i : ℕ, i < 3 → ∀ j : ℕ, j < 3 → Holds 0 3328 256 (r.1.val[3 * i + j]!).val (SampleNTT (ρ ‖ #v[(i : Byte)] ‖ #v[(j : Byte)])) ⦄ := by
  have hmsg (i j : ℕ) (hj : j < 3) :
      matMsg (bv rho.val) true 3 (3 * i + j) = (ρ ‖ #v[(i : Byte)] ‖ #v[(j : Byte)]).toList := by
    rw [matMsg_transposed _ _ _ hj, hρ, vappend_toList, vappend_toList, List.append_assoc]
    rfl
  apply WP.spec_mono (coeffs_sample_spec h inst hi rho true (fun p hp => by
    have := hH (p / 3) (by omega) (p % 3) (by omega)
    rwa [← hmsg _ _ (by omega), show 3 * (p / 3) + p % 3 = p by omega] at this))
  intro r hr i hi3 j hj3 c hc
  have hs := hr (3 * i + j) (by omega) c hc
  rw [hmsg _ _ hj3] at hs
  have hlt := sampled_lt _ c hc (hH i hi3 j hj3)
  refine ⟨by rw [hs]; omega, by rw [hs]; omega, ?_⟩
  rw [hs, getElem!_pos (SampleNTT _) c hc, sampleNTT_sampled _ (hH i hi3 j hj3) c hc]
  simp

/-! ## `Decoded::new` -/

theorem try_from32 (s : Slice U8) (h : s.length = 32) :
    ∃ a : Std.Array U8 32#usize, core.array.TryFromSharedArraySlice.try_from 32#usize s = ok (.Ok a) ∧
      a.val = s.val := by
  have hs : s.len = 32#usize := by scalar_tac
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dite_eq_left hs]
  exact ⟨_, rfl, by simp [Std.Array.from_val]⟩

/-- `as_flattened_mut` views arrays as their bytes in order, and writes back
array `j` from bytes `N j` to `N (j + 1)`. -/
theorem as_flattened_mut_back_spec {N : Usize} (s : Slice (Std.Array U8 N))
    (h : (s.val.flatMap (·.val)).length ≤ Usize.max) :
    core.slice.SliceArray.as_flattened_mut s ⦃ f back => f.val = s.val.flatMap (·.val) ∧
      ∀ t : Slice U8, t.length = s.length * N.val → (back t).length = s.length ∧
        ∀ j < s.length, ((back t).val[j]!).val = sub t.val (N.val * j) N.val ⦄ := by
  unfold core.slice.SliceArray.as_flattened_mut
  simp only
  rw [dite_eq_left_of_eq_true (eq_true h)]
  simp only [WP.spec_ok, WP.uncurry'_pair]
  refine ⟨by simp, fun t ht => ⟨by simp [Slice.length], fun j hj => ?_⟩⟩
  have hj' : j < s.val.length := hj
  simp only [Slice.from_val, List.getElem!_eq_getElem?_getD, List.getElem?_mapIdx,
    List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some]
  rw [Std.Array.from_slice_val _ _ (by
    simp only [Slice.from_val, List.length_take, List.length_drop]
    have : t.val.length = s.val.length * N.val := ht
    have : (j + 1) * N.val ≤ s.val.length * N.val := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this
    omega)]
  simp only [Slice.from_val, sub, Nat.mul_comm j]

theorem toVec_congr (n : ℕ) (l l' : List U8) (h : l.length = n) (h' : l'.length = n) (e : l = l') :
    toVec n l h = toVec n l' h' := by
  subst e; rfl

/-- `t̂`'s polynomial `j`, as `K-PKE.Encrypt` decodes it from `ek`, is the
12-bit decoding of `ek`'s 384 bytes from `384 j`. -/
theorem decode_t_hat (ek : EkBytes) (b : Std.Array U8 384#usize) (j : ℕ) (hj : j < 3)
    (hb : b.val = sub ek.val (384 * j) 384) :
    decode12 b =
      (PolyVector.ByteDecode (k := k .ML_KEM_768) 12 (slice (toVec 1184 ek.val ek.property) 0 1152))[j]! := by
  have hek : ek.val.length = 1184 := ek.property
  interval_cases j <;>
  · unfold decode12 PolyVector.ByteDecode
    simp (disch := decide) only [vget!, Vector.getElem_ofFn, slice_toVec]
    congr 1
    apply toVec_congr
    rw [hb, sub_sub0 _ _ _ _ (by decide)]

open scoped Spec.Notations in
/-- `Decoded::new` of an ML-KEM-768 encapsulation key decodes `t̂` and samples
the transposed matrix, as `K-PKE.Encrypt` reads them from `ek`, given that
`SampleNTT` finishes on each of the matrix's inputs. -/
theorem decoded_new_spec (h : RunsSha3) {X : Type}
    (P : mid.mlkem.Params X Vec Mat EkBytes CtBytes DkBytes Cache Enc) (hP : Is768 P) (ek : EkBytes)
    (hH : ∀ i : ℕ, i < 3 → ∀ j : ℕ, j < 3 →
      Halts (slice (toVec 1184 ek.val ek.property) 1152 32 ‖ #v[(i : Byte)] ‖ #v[(j : Byte)]).toList) :
    mid.mlkem.Decoded.new P ek ⦃ d => DecodedHolds d
      (fun j => (PolyVector.ByteDecode (k := k .ML_KEM_768) 12 (slice (toVec 1184 ek.val ek.property) 0 1152))[j]!)
      (fun i j => SampleNTT (slice (toVec 1184 ek.val ek.property) 1152 32 ‖ #v[(i : Byte)] ‖ #v[(j : Byte)])) ⦄ := by
  have hek : ek.val.length = 1184 := ek.property
  unfold mid.mlkem.Decoded.new
  simp only [hP.ek.as_ref, hP.K, hP.enc.filled, hP.enc.as_mut, bind_ok]
  step as ⟨s, hs⟩
  step as ⟨i1, hi1⟩
  step as ⟨t_hat, rho, htl, hrl, htv, hrv⟩
  step as ⟨s1, back, hs1v, hs1l, hback⟩
  have hfl : (s1.val.flatMap (·.val)).length = 1152 := by
    rw [flat_length]; simp [hs1l]
  step with as_flattened_mut_back_spec s1 (by rw [hfl]; scalar_tac) as ⟨s2, fback, hs2v, hfback⟩
  step as ⟨s3, hs3⟩
  obtain ⟨hl4, hc4⟩ := hfback s3 (by rw [hs3, htl, hi1, hs1l])
  step with from_bytes_spec P.VectorInst hP.vec hP.enc (back (fback s3)) as ⟨c, hc⟩
  obtain ⟨a1, ha1, ha1v⟩ := try_from32 rho (by rw [hrl, hi1]; simp [Slice.length, hs, hek])
  rw [ha1]
  simp only [core.result.Result.unwrap, bind_ok]
  have hρ : bv a1.val = (slice (toVec 1184 ek.val ek.property) 1152 32).toList := by
    rw [ha1v, hrv, hs, hi1, slice_toVec, MlKemCbd.toVec_toList, sub,
      List.take_of_length_le (by simp [hek])]
  step with sample_transposed_spec h P.FixedArraySelf_MatrixArrayI16256Inst hP.mat a1 _ hρ hH as ⟨c1, hc1⟩
  refine ⟨fun j hj => ?_, hc1⟩
  have hbj : ((back (fback s3)).val[j]!).val = sub ek.val (384 * j) 384 := by
    rw [hback _ (by rw [hl4, hs1l]), hc4 j (by rw [hs1l]; exact hj), hs3, htv, hi1, hs,
      show List.take (3 * 384) ek.val = sub ek.val 0 (3 * 384) by simp [sub],
      sub_sub0 _ _ _ _ (by omega)]
  rw [← decode_t_hat ek _ j hj hbj]
  exact hc j hj

end MlKemSample

end rind.aarch64
