import Rind.X86_64.Ghash
import Rind.GhashSpec
open Aeneas Aeneas.Std Result rind.vale rind.simd Polynomial

/-!
# rind's PCLMULQDQ GHASH

`Rind.X86_64.AesGcmModel`'s `ClmulTable::add`, `_mul8`, and `mul_h` hash
blocks as Vale's `ghash_LE` does, for a table of the key's powers: each sums
the Karatsuba products of several blocks with descending powers and reduces
once, which `Rind.Gf128`'s `reduce_sum` and `mul_data` prove is Horner's rule
on the blocks, the state being the polynomial of the hash's bytes reversed.
-/

local notation "P" => Polynomial (ZMod 2)

-- Unfolding the recursions below over polynomials, whose zero and sum are
-- deep terms, needs more than the project's depth.
set_option maxRecDepth 20000

namespace rind.x86_64

/-! ## The PCLMULQDQ steps -/

/-- A table for the GHASH key `H`: H to H^8, each shifted as Vale's
`shift_key_1` does, and beside each its halves XORed. -/
def TableFor (H : P) (t : low.x86_64.ghash.ClmulTable) : Prop :=
  ∀ i < 8, toPoly t.powers.val[i]! = shiftKey1 128 gf128ModulusLowTerms (gPower H (i + 1)) ∧
    t.powers_xor.val[i]! = swap t.powers.val[i]! ^^^ t.powers.val[i]!

theorem mul_model_eq (lo mi hi x h : BitVec 128) :
    low.x86_64.ghash.mul lo mi hi x h (swap h ^^^ h) =
      ok ((karaTerms x h).1 ^^^ lo, (karaTerms x h).2.1 ^^^ mi, (karaTerms x h).2.2 ^^^ hi) := by
  have e0 : (I32.bv 0#i32).getLsbD 0 = false := by decide
  have e4 : (I32.bv 0#i32).getLsbD 4 = false := by decide
  have f0 : (I32.bv 17#i32).getLsbD 0 = true := by decide
  have f4 : (I32.bv 17#i32).getLsbD 4 = true := by decide
  simp only [low.x86_64.ghash.mul, core.core_arch.x86.sse2._mm_shuffle_epi32,
    core.core_arch.x86.sse2._mm_xor_si128, core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128,
    swap_lanes, bind_ok, e0, e4, f0, f4, Bool.false_eq_true, ite_false, ite_true, lane64_0, lane64_1,
    karaTerms]

/-- The model's `reduce!` constant is the translation's `u128_to_m128i(GF128_POLY_HI)`. -/
theorem polyHi_eq :
    low.x86_64.ghash.u128_to_m128i low.x86_64.ghash.GF128_POLY_HI = ok low.x86_64.ghash.polyHi := by
  rw [u128_to_m128i_eq, poly_hi_bv]; rfl

theorem reduce_model_eq (lo mi hi : BitVec 128) :
    low.x86_64.ghash.reduce lo mi hi = ok (reduceModel lo mi hi) := by
  have e0 : (I32.bv 0#i32).getLsbD 0 = false := by decide
  have e4 : (I32.bv 0#i32).getLsbD 4 = false := by decide
  simp only [low.x86_64.ghash.reduce, low.x86_64.ghash.polyHi,
    core.core_arch.x86.sse2._mm_shuffle_epi32, core.core_arch.x86.sse2._mm_xor_si128,
    core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128, swap_lanes, bind_ok, e0, e4,
    Bool.false_eq_true, ite_false, lane64_0, poly_hi_lo, reduceModel]

/-! ## Loads -/

/-- `PSHUFB` by `BYTESWAP` reverses the bytes. -/
theorem shuffle_byteswap (v : BitVec 128) :
    core.core_arch.x86.ssse3._mm_shuffle_epi8 v 0x00010203_04050607_08090a0b_0c0d0e0f#128 =
      ok (reverseBytesQuad32 v) := by
  simp only [core.core_arch.x86.ssse3._mm_shuffle_epi8]
  congr 1

theorem load_be_eq (b : List U8) : low.x86_64.ghash.load_be b = ok (blockBE b) := by
  simp only [low.x86_64.ghash.load_be, low.x86_64.ghash.BYTESWAP, bind_ok, shuffle_byteswap, blockBE]

/-! ## Karatsuba terms summed -/

/-- The powers H^n down to H, as the table holds them. -/
def powersDesc (t : low.x86_64.ghash.ClmulTable) (n : Nat) : List (BitVec 128) :=
  (List.range n).reverse.map fun i => t.powers.val[i]!

theorem powersDesc_succ (t : low.x86_64.ghash.ClmulTable) (n : Nat) :
    powersDesc t (n + 1) = t.powers.val[n]! :: powersDesc t n := by
  simp [powersDesc, List.range_succ]

/-- Data times the table's powers, H^n for the first of `n` down to H for
the last, summed, is `sumPow`. -/
theorem sum_powersDesc (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t) :
    ∀ xs : List (BitVec 128), xs.length ≤ 8 →
      ((xs.zip (powersDesc t xs.length)).map fun p => toPoly (mulModel p.1 p.2)).sum =
        sumPow H (xs.map toPoly)
  | [], _ => by simp [powersDesc, sumPow_nil]
  | x :: xs, hl => by
    rw [List.length_cons, powersDesc_succ, List.zip_cons_cons, List.map_cons, List.sum_cons,
      sum_powersDesc H hH t ht xs (by simp at hl; omega), List.map_cons, sumPow_cons, List.length_map,
      mul_data _ _ _ (small_gPower H hH _) ((ht xs.length (by simp at hl; omega)).1)]

theorem toPoly_reduceAll_powers (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable)
    (ht : TableFor H t) (xs : List (BitVec 128)) (hl : xs.length ≤ 8) :
    toPoly (reduceAll (xs.zip (powersDesc t xs.length))) = sumPow H (xs.map toPoly) := by
  rw [toPoly_reduceAll, sum_powersDesc H hH t ht xs hl]

/-! ## `_mul8` and `mul_h` -/

theorem powersDesc_eight (t : low.x86_64.ghash.ClmulTable) :
    powersDesc t 8 = [t.powers.val[7]!, t.powers.val[6]!, t.powers.val[5]!, t.powers.val[4]!,
      t.powers.val[3]!, t.powers.val[2]!, t.powers.val[1]!, t.powers.val[0]!] := rfl

theorem mul8_eq (H : P) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t)
    (x1 x2 x3 x4 x5 x6 x7 x8 : BitVec 128) :
    low.x86_64.ghash._mul8 t x1 x2 x3 x4 x5 x6 x7 x8 =
      ok (reduceAll ([x1, x2, x3, x4, x5, x6, x7, x8].zip (powersDesc t 8))) := by
  simp only [low.x86_64.ghash._mul8, core.core_arch.x86.sse2._mm_setzero_si128, bind_ok,
    (ht 0 (by omega)).2, (ht 1 (by omega)).2, (ht 2 (by omega)).2, (ht 3 (by omega)).2,
    (ht 4 (by omega)).2, (ht 5 (by omega)).2, (ht 6 (by omega)).2, (ht 7 (by omega)).2,
    mul_model_eq, reduce_model_eq, powersDesc_eight, reduceAll, accum, List.zip_cons_cons,
    List.zip_nil_left]
  rfl

theorem mul_h_eq (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t)
    (x : BitVec 128) :
    ∃ y, low.x86_64.ghash.ClmulTable.mul_h t x = ok y ∧ toPoly y = gf128MulRev (toPoly x) H := by
  refine ⟨reduceAll ([x].zip (powersDesc t 1)), ?_, ?_⟩
  · simp only [low.x86_64.ghash.ClmulTable.mul_h, core.core_arch.x86.sse2._mm_setzero_si128, bind_ok,
      (ht 0 (by omega)).2, mul_model_eq, reduce_model_eq, reduceAll, accum, powersDesc,
      List.range_one, List.reverse_singleton, List.map_cons, List.map_nil, List.zip_cons_cons,
      List.zip_nil_left]
    rfl
  · have h1 := toPoly_reduceAll_powers H hH t ht [x] (by simp)
    rw [List.length_singleton] at h1
    rw [h1, List.map_cons, List.map_nil, sumPow_cons,
      sumPow_nil, List.length_nil, gPower_one, add_zero]

/-! ## `add_tail` -/

theorem add_tail_loop_eq (x lo mi hi : BitVec 128) :
    ∀ (blocks : List (List U8)) (ps : List (BitVec 128 × BitVec 128)),
      blocks.length ≤ ps.length → (∀ p ∈ ps, p.2 = swap p.1 ^^^ p.1) →
      low.x86_64.ghash.ClmulTable.add_tail_loop blocks ps x lo mi hi =
        let a := accum (lo, mi, hi) ((tailInputs x (blocks.map blockBE)).zip (ps.map Prod.fst))
        ok (if blocks = [] then x else 0, a.1, a.2.1, a.2.2, ps.drop blocks.length)
  | [], ps, _, _ => by simp [low.x86_64.ghash.ClmulTable.add_tail_loop, tailInputs, accum]
  | _ :: _, [], hl, _ => by simp at hl
  | b :: bs, (h, hx) :: ps, hl, hp => by
    have hhx : hx = swap h ^^^ h := hp (h, hx) (by simp)
    subst hhx
    rw [low.x86_64.ghash.ClmulTable.add_tail_loop]
    simp only [load_be_eq, core.core_arch.x86.sse2._mm_xor_si128, bind_ok, mul_model_eq,
      core.core_arch.x86.sse2._mm_setzero_si128]
    simp only [add_tail_loop_eq 0 _ _ _ bs ps (by simp at hl; omega) (fun p hp' => hp p (by simp [hp']))]
    simp only [tailInputs_zero]
    simp only [List.map_cons, tailInputs_cons, List.zip_cons_cons, accum, List.length_cons,
      List.drop_succ_cons, List.cons_ne_nil, ite_false, ite_self]
    rfl

/-- The table's first `n` powers, each beside its halves XORed, from H^n down. -/
theorem zip_take_reverse (t : low.x86_64.ghash.ClmulTable) (n : Nat) (hn : n ≤ 8) :
    ((t.powers.val.take n).zip (t.powers_xor.val.take n)).reverse =
      (List.range n).reverse.map fun i => (t.powers.val[i]!, t.powers_xor.val[i]!) := by
  rw [List.map_reverse]
  congr 1
  have h1 : t.powers.val.length = 8 := by simp
  have h2 : t.powers_xor.val.length = 8 := by simp
  apply List.ext_getElem
  · simp only [List.length_zip, List.length_take, List.length_map, List.length_range]
    omega
  · intro i hi _
    simp only [List.length_zip, List.length_take] at hi
    have i1 : i < t.powers.val.length := by omega
    have i2 : i < t.powers_xor.val.length := by omega
    simp [List.getElem_zip, List.getElem_take, List.getElem?_eq_getElem i1, List.getElem?_eq_getElem i2]

theorem powersDesc_split (t : low.x86_64.ghash.ClmulTable) (m : Nat) :
    powersDesc t (m + 1) =
      ((List.range m).map Nat.succ).reverse.map (fun i => t.powers.val[i]!) ++ [t.powers.val[0]!] :=
  range_succ_reverse _ m

theorem add_tail_eq (t : low.x86_64.ghash.ClmulTable) (H : P) (ht : TableFor H t) (bytes : List U8)
    (x : BitVec 128) (hb : bytes ≠ []) (hl : bytes.length ≤ 128) :
    low.x86_64.ghash.ClmulTable.add_tail t bytes x =
      ok (reduceAll ((tailInputs x (padBlocks bytes)).zip (powersDesc t ((bytes.length + 15) / 16)))) := by
  have hr := chunksRest_length 16 bytes
  have hm := chunksOf_length 16 bytes
  have hn8 : ¬ (bytes.length + 15) / 16 > 8 := by omega
  have hne : bytes.isEmpty = false := by simpa using hb
  have hps : ∀ p ∈ (List.range ((bytes.length + 15) / 16)).reverse.map
      (fun i => (t.powers.val[i]!, t.powers_xor.val[i]!)), p.2 = swap p.1 ^^^ p.1 := by
    intro p hp
    simp only [List.mem_map, List.mem_reverse, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact (ht i (by omega)).2
  simp only [low.x86_64.ghash.ClmulTable.add_tail, hne, hn8,
    zip_take_reverse t _ (by omega : (bytes.length + 15) / 16 ≤ 8),
    Bool.false_eq_true, ite_false, core.core_arch.x86.sse2._mm_setzero_si128, bind_ok,
    add_tail_loop_eq x 0 0 0 (chunksOf 16 bytes) _ (by simp; omega) hps]
  have hfst : ∀ n, List.map Prod.fst (List.map (fun i => (t.powers.val[i]!, t.powers_xor.val[i]!))
      (List.range n).reverse) = powersDesc t n := fun n => by rw [List.map_map]; rfl
  simp only [hfst]
  by_cases h0 : bytes.length % 16 = 0
  · have hn : (bytes.length + 15) / 16 = (chunksOf 16 bytes).length := by omega
    have hrest : chunksRest 16 bytes = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hd : List.drop (chunksOf 16 bytes).length (List.map (fun i => (t.powers.val[i]!, t.powers_xor.val[i]!))
        (List.range (chunksOf 16 bytes).length).reverse) = [] := by simp
    simp only [hn, hd, padBlocks, hrest, ite_true, List.append_nil, uncurry_apply_pair, bind_ok,
      reduce_model_eq, reduceAll]
  · have hn : (bytes.length + 15) / 16 = (chunksOf 16 bytes).length + 1 := by omega
    rw [hn] at hps ⊢
    have h00 := (ht 0 (by omega)).2
    simp only [range_succ_reverse, uncurry_apply_pair, bind_ok, low.x86_64.ghash.BYTESWAP, shuffle_byteswap,
      core.core_arch.x86.sse2._mm_xor_si128, h00]
    rw [List.drop_left' (by simp)]
    simp only [mul_model_eq, uncurry_apply_pair, bind_ok, reduce_model_eq]
    have hrest : chunksRest 16 bytes ≠ [] := fun h => h0 (by rw [← hr, h]; rfl)
    have hA : (List.map blockBE (chunksOf 16 bytes)).length =
        (((List.range (chunksOf 16 bytes).length).map Nat.succ).reverse.map (fun i => t.powers.val[i]!)).length := by
      simp
    simp only [padBlocks, hrest, ite_false, powersDesc_split, reduceAll]
    simp only [accum_tail _ _ _ _ _ hA, List.map_eq_nil_iff]
    rfl

/-- `add_tail` hashes the padded blocks of up to 128 bytes. -/
theorem add_tail_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t)
    (bytes : List U8) (x : BitVec 128) (hl : bytes.length ≤ 128) :
    ∃ y, low.x86_64.ghash.ClmulTable.add_tail t bytes x = ok y ∧
      toPoly y = ghashPoly H (toPoly x) ((padBlocks bytes).map toPoly) := by
  by_cases hb : bytes = []
  · subst hb
    exact ⟨x, by simp [low.x86_64.ghash.ClmulTable.add_tail], by rw [padBlocks_nil, List.map_nil, ghashPoly_nil]⟩
  · refine ⟨_, add_tail_eq t H ht bytes x hb hl, ?_⟩
    have hlen := length_padBlocks bytes
    have hne : padBlocks bytes ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen
      exact hb (List.eq_nil_of_length_eq_zero (by omega))
    have h := toPoly_reduceAll_powers H hH t ht (tailInputs x (padBlocks bytes))
      (by rw [length_tailInputs]; omega)
    rw [length_tailInputs, hlen] at h
    rw [h, sumPow_tailInputs H x _ hne]

/-! ## `add` -/

theorem add_loop_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t) :
    ∀ (chunks : List (List U8)) (x : BitVec 128), (∀ c ∈ chunks, c.length = 128) →
      ∃ y, low.x86_64.ghash.ClmulTable.add_loop t chunks x = ok y ∧
        toPoly y = ghashPoly H (toPoly x) ((chunks.flatMap padBlocks).map toPoly)
  | [], x, _ => ⟨x, rfl, by simp [ghashPoly_nil]⟩
  | c :: chunks, x, hc => by
    have hc0 : c.length = 128 := hc c (by simp)
    have h8 : (chunksOf 16 c).length = 8 := by rw [chunksOf_length, hc0]
    let y := reduceAll ((tailInputs x (padBlocks c)).zip (powersDesc t 8))
    have hy : low.x86_64.ghash.ClmulTable.add_loop t (c :: chunks) x =
        low.x86_64.ghash.ClmulTable.add_loop t chunks y := by
      rw [low.x86_64.ghash.ClmulTable.add_loop]
      simp only [load_be_eq, core.core_arch.x86.sse2._mm_xor_si128, bind_ok, mul8_eq H t ht]
      congr 2
      rw [padBlocks_128 c hc0, eight _ h8]
      rfl
    have hyp : toPoly y = ghashPoly H (toPoly x) ((padBlocks c).map toPoly) := by
      have hl : (padBlocks c).length = 8 := by rw [padBlocks_128 c hc0, List.length_map, h8]
      have hne : padBlocks c ≠ [] := fun h => by rw [h] at hl; simp at hl
      have h := toPoly_reduceAll_powers H hH t ht (tailInputs x (padBlocks c)) (by rw [length_tailInputs]; omega)
      rw [length_tailInputs, hl] at h
      rw [h, sumPow_tailInputs H x _ hne]
    obtain ⟨z, hz, hzp⟩ := add_loop_spec H hH t ht chunks y (fun c h => hc c (by simp [h]))
    exact ⟨z, hy ▸ hz, by rw [hzp, hyp, List.flatMap_cons, List.map_append, ghashPoly_append]⟩

/-- `ClmulTable::add` hashes the padded blocks of the bytes from the state
`x`, for a table of `H`'s powers. -/
theorem clmul_add_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t)
    (bytes : List U8) (x : BitVec 128) :
    ∃ y, low.x86_64.ghash.ClmulTable.add t bytes x = ok y ∧
      toPoly y = ghashPoly H (toPoly x) ((padBlocks bytes).map toPoly) := by
  obtain ⟨y, hy, hyp⟩ := add_loop_spec H hH t ht (chunksOf 128 bytes) x (fun c h => chunksOf_length_mem h)
  have hr : (chunksRest 128 bytes).length ≤ 128 := by rw [chunksRest_length]; omega
  obtain ⟨z, hz, hzp⟩ := add_tail_spec H hH t ht (chunksRest 128 bytes) y hr
  refine ⟨z, by rw [low.x86_64.ghash.ClmulTable.add, hy, bind_ok, hz], ?_⟩
  rw [hzp, hyp, padBlocks_split bytes, List.map_append, ghashPoly_append]

/-! ## The table `ClmulTable::new` builds -/

/-- `<[T; N]>::map`, for a closure that returns `g` of its argument. -/
theorem map_eq {T F U : Type} {N : Std.Usize} (inst : core.ops.function.FnMut F T U) (g : T → U)
    (hf : ∀ f x, inst.call_mut f x = ok (g x, f)) (a : Std.Array T N) (f : F) :
    ∃ h, core.array.Array.map inst a f = ok (Std.Array.from (a.val.map g) h) := by
  have key : ∀ (l : List T) (acc : List U), l.foldlM (fun (p : List U × F) x => do
      let (y, f) ← inst.call_mut p.2 x
      ok (p.1 ++ [y], f)) (acc, f) = ok (acc ++ l.map g, f) := by
    intro l
    induction l with
    | nil => intro acc; simp only [List.foldlM_nil, List.map_nil, List.append_nil]; rfl
    | cons x l ih =>
      intro acc
      have hy := hf f x
      simp only [List.foldlM_cons, hy, bind_ok, bind_tc_ok, uncurry_apply_pair]
      rw [ih]
      simp
  have hl : (a.val.map g).length = N.val := by rw [List.length_map, Std.Array.property]
  refine ⟨hl, ?_⟩
  unfold core.array.Array.map
  simp only [key, List.nil_append, bind_ok, uncurry_apply_pair]
  rw [dite_eq_left hl]

theorem clmul_new_spec (h : Std.U128) (hw : low.x86_64.cpu.HaveAesHardware) :
    ∃ t, low.x86_64.ghash.ClmulTable.new h hw = ok t ∧ TableFor (toPoly h.bv) t := by
  obtain ⟨hl, hm⟩ := map_eq
    low.x86_64.ghash.ClmulTable.with_powers.closure.Insts.CoreOpsFunctionFnMutTuple__m128i__m128i
    (fun p => swap p ^^^ p)
    (fun f x => by simp only [
      low.x86_64.ghash.ClmulTable.with_powers.closure.Insts.CoreOpsFunctionFnMutTuple__m128i__m128i.call_mut,
      low.x86_64.ghash.xor_halves, core.core_arch.x86.sse2._mm_shuffle_epi32,
      core.core_arch.x86.sse2._mm_xor_si128, bind_ok, swap_lanes])
    (Std.Array.make 8#usize (ghashPowers h.bv) (by simp [ghashPowers])) ()
  refine ⟨_, by simp only [low.x86_64.ghash.ClmulTable.new, powers_eq, bind_ok,
    low.x86_64.ghash.ClmulTable.with_powers, hm]; rfl, ?_⟩
  intro i hi
  refine ⟨ghashPowers_spec h.bv i hi, ?_⟩
  have hlen : i < (ghashPowers h.bv).length := by simp [ghashPowers]; omega
  rw [Std.Array.from_val, Std.Array.make_val, getElem!_pos _ i (by simpa using hlen),
    getElem!_pos _ i hlen, List.getElem_map]

end rind.x86_64

