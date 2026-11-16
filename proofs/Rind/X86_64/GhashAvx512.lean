import Rind.X86_64.Lanes512
open Aeneas Aeneas.Std Result rind.vale rind.simd Polynomial

/-!
# rind's AVX-512 GHASH

`Rind.X86_64.AesGcmModel`'s `_mul16`, `_mul_tail`, and `GhashTableAvx512::add`
hash blocks as `ClmulTable::add` does, for a table of the key's 16 powers:
each lane sums schoolbook products of blocks with descending powers and folds
the sum once by the reflected modulus, which is `Rind.Gf128`'s `reduce_sum`
of the lane's products, and the lanes' folds are XORed.
-/

local notation "P" => Polynomial (ZMod 2)

set_option maxRecDepth 20000

namespace rind.x86_64

/-- The 512-bit GHASH's powers for the key `H`: H^16 down to H, each shifted
as Vale's `shift_key_1` does. -/
def Avx512Powers (H : P) (t : low.x86_64.ghash.GhashTableAvx512) : Prop :=
  ∃ s, low.x86_64.aes_gcm_vaes.VaesKernel.powers t.vaes = ok s ∧ s.val.length = 16 ∧
    ∀ i < 16, toPoly s.val[i]! = shiftKey1 128 gf128ModulusLowTerms (gPower H (16 - i))

/-! ## Folding a lane -/

theorem fold_eq (L M Hh : BitVec 128) :
    clmul c64 (lo (clmul c64 (lo L) ^^^ swap L ^^^ M)) ^^^ swap (clmul c64 (lo L) ^^^ swap L ^^^ M) ^^^ Hh =
      reduceModel L (M ^^^ L ^^^ Hh) Hh := by
  simp only [reduceModel]
  generalize clmul c64 (lo L) = a
  have e : M ^^^ L ^^^ Hh ^^^ L ^^^ Hh ^^^ swap L ^^^ a = a ^^^ swap L ^^^ M := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_xor]
    cases M.getLsbD k <;> cases L.getLsbD k <;> cases Hh.getLsbD k <;> cases (swap L).getLsbD k <;>
      cases a.getLsbD k <;> rfl
  rw [e]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_xor]
  cases Hh.getLsbD k <;> cases (swap (a ^^^ swap L ^^^ M)).getLsbD k <;>
    cases (clmul c64 (lo (a ^^^ swap L ^^^ M))).getLsbD k <;> rfl

/-- A lane's schoolbook sum, folded, is the sum of its products' own
reductions. -/
theorem fold_sum (L M Hh : BitVec 128) (ps : List (BitVec 128 × BitVec 128))
    (hk : toPoly L + X ^ 64 * toPoly M + X ^ 128 * toPoly Hh = (ps.map fun p => toPoly p.1 * toPoly p.2).sum) :
    toPoly (reduceModel L (M ^^^ L ^^^ Hh) Hh) = (ps.map fun p => toPoly (mulModel p.1 p.2)).sum := by
  refine reduce_sum _ _ _ ps ?_
  rw [← hk, kara, toPoly_xor, toPoly_xor]
  linear_combination (X ^ 64 * (toPoly L + toPoly Hh)) * two_eq_zero_P

theorem imm_facts :
    (I32.bv 0#i32).toNat % 4 = 0 ∧ (I32.bv 1#i32).toNat % 4 = 1 ∧ (I32.bv 2#i32).toNat % 4 = 2 ∧
    (I32.bv 3#i32).toNat % 4 = 3 ∧ (I32.bv 0#i32).getLsbD 0 = false ∧ (I32.bv 0#i32).getLsbD 4 = false ∧
    (I32.bv 1#i32).getLsbD 0 = true ∧ (I32.bv 1#i32).getLsbD 4 = false ∧
    (I32.bv 16#i32).getLsbD 0 = false ∧ (I32.bv 16#i32).getLsbD 4 = true ∧
    (I32.bv 17#i32).getLsbD 0 = true ∧ (I32.bv 17#i32).getLsbD 4 = true := by decide

theorem polyLo_hi : hi low.x86_64.ghash.polyLo = c64 := by decide

/-! ## `_mul16` -/

/-- `_mul16` of 16 blocks, four to a vector, the first in lane 0, is the sum
of the blocks times H^16 down to H. -/
theorem mul16_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.GhashTableAvx512) (ht : Avx512Powers H t)
    (x : Nat → BitVec 128) :
    ∃ y, low.x86_64.ghash._mul16 t (ofLanes128 fun j => x j) (ofLanes128 fun j => x (4 + j))
      (ofLanes128 fun j => x (8 + j)) (ofLanes128 fun j => x (12 + j)) = ok y ∧
      toPoly y = sumPow H ((List.range 16).map (toPoly ∘ x)) := by
  obtain ⟨s, hs, hl, hp⟩ := ht
  obtain ⟨i0, i1, i2, i3, a0, a4, b0, b4, c0, c4, d0, d4⟩ := imm_facts
  simp only [low.x86_64.ghash._mul16, low.x86_64.ghash.GhashTableAvx512.powers, hs, hl, ite_true, bind_ok]
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.getElem!_cons_zero, List.getElem!_cons_succ, Nat.mul_zero, Nat.zero_add]
  simp only [broadcast512_eq, clmul512_eq, xor512_eq, ternary512_eq, ternary512q_eq, shuffle512_eq,
    low.x86_64.ghash.sumLanes, extract512_eq, ternary128_eq, core.core_arch.x86.sse2._mm_xor_si128, bind_ok,
    i0, i1, i2, i3, a0, a4, b0, b4, c0, c4, d0, d4, ite_true, ite_false, Bool.false_eq_true, polyLo_hi,
    lane64_0, lane64_1, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd]
  simp only [fold_eq]
  refine ⟨_, rfl, ?_⟩
  have hx : ∀ (a b : BitVec 128), toPoly a * toPoly b = (toPoly (lo a) + X ^ 64 * toPoly (hi a)) *
      (toPoly (lo b) + X ^ 64 * toPoly (hi b)) := fun a b => by rw [← toPoly_halves, ← toPoly_halves]
  rw [toPoly_xor, toPoly_xor, toPoly_xor]
  rw [fold_sum _ _ _ [(x 0, s.val[0]!), (x 4, s.val[4]!), (x 8, s.val[8]!), (x 12, s.val[12]!)] (by
      simp only [toPoly_xor, toPoly_clmul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx]; ring),
    fold_sum _ _ _ [(x 1, s.val[1]!), (x 5, s.val[5]!), (x 9, s.val[9]!), (x 13, s.val[13]!)] (by
      simp only [toPoly_xor, toPoly_clmul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx]; ring),
    fold_sum _ _ _ [(x 2, s.val[2]!), (x 6, s.val[6]!), (x 10, s.val[10]!), (x 14, s.val[14]!)] (by
      simp only [toPoly_xor, toPoly_clmul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx]; ring),
    fold_sum _ _ _ [(x 3, s.val[3]!), (x 7, s.val[7]!), (x 11, s.val[11]!), (x 15, s.val[15]!)] (by
      simp only [toPoly_xor, toPoly_clmul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx]; ring)]
  have hm : ∀ (a : BitVec 128) (i : Nat), i < 16 →
      toPoly (mulModel a s.val[i]!) = gf128MulRev (toPoly a) (gPower H (16 - i)) :=
    fun a i hi => mul_data _ _ _ (small_gPower H hH _) (hp i hi)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hm _ _ (by omega : (0:Nat) < 16),
    hm _ _ (by omega : (1:Nat) < 16), hm _ _ (by omega : (2:Nat) < 16), hm _ _ (by omega : (3:Nat) < 16),
    hm _ _ (by omega : (4:Nat) < 16), hm _ _ (by omega : (5:Nat) < 16), hm _ _ (by omega : (6:Nat) < 16),
    hm _ _ (by omega : (7:Nat) < 16), hm _ _ (by omega : (8:Nat) < 16), hm _ _ (by omega : (9:Nat) < 16),
    hm _ _ (by omega : (10:Nat) < 16), hm _ _ (by omega : (11:Nat) < 16), hm _ _ (by omega : (12:Nat) < 16),
    hm _ _ (by omega : (13:Nat) < 16), hm _ _ (by omega : (14:Nat) < 16), hm _ _ (by omega : (15:Nat) < 16),
    sumPow_cons, sumPow_nil, List.length_cons, List.length_nil, Function.comp]
  ring

/-! ## `GhashTableAvx512::add` -/

theorem pshufb_byteswap (v : BitVec 128) : pshufb v 0x00010203_04050607_08090a0b_0c0d0e0f#128 = reverseBytesQuad32 v := by
  have h := shuffle_byteswap v
  simp only [shuffle_epi8_eq, Result.ok.injEq] at h
  exact h

theorem drop_take_drop {α : Type} (l : List α) (a j : Nat) (hj : 16 * j + 16 ≤ 64) :
    (((l.drop a).take 64).drop (16 * j)).take 16 = (l.drop (a + 16 * j)).take 16 := by
  rw [List.drop_take, List.take_take, List.drop_drop, show min 16 (64 - 16 * j) = 16 by omega]

/-- A 64-byte load's lanes are the 16-byte loads of its blocks. -/
theorem loadBytes512_chunk (c : List U8) (v : Nat) :
    loadBytes512 ((c.drop (64 * v)).take 64) = ofLanes128 fun j => loadBytes ((c.drop (16 * (4 * v + j))).take 16) := by
  unfold loadBytes512
  apply ofLanes128_ext
  intro j hj
  rw [drop_take_drop _ _ _ (by omega), show 64 * v + 16 * j = 16 * (4 * v + j) by ring]

theorem getElem!_chunksOf {α : Type} [Inhabited α] (k : Nat) (l : List α) (i : Nat) (hi : i < l.length / k) :
    (chunksOf k l)[i]! = (l.drop (k * i)).take k := by
  simp [chunksOf, hi]

/-- `hash16` of a 256-byte chunk: GHASH of its blocks from `current`. -/
theorem hash16_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.GhashTableAvx512) (ht : Avx512Powers H t)
    (c : List U8) (hc : c.length = 256) (current : BitVec 128) :
    ∃ y, low.x86_64.ghash.hash16 t (ofLanes128 fun _ => 0x00010203_04050607_08090a0b_0c0d0e0f#128)
      ((chunksOf 64 c).map loadBytes512) current = ok y ∧
      toPoly y = ghashPoly H (toPoly current) ((padBlocks c).map toPoly) := by
  let X : Nat → BitVec 128 := fun b => if b = 0 then current ^^^ blockBE ((c.drop 0).take 16)
    else blockBE ((c.drop (16 * b)).take 16)
  obtain ⟨y, hy, hyp⟩ := mul16_spec H hH t ht X
  refine ⟨y, ?_, ?_⟩
  · rw [← hy]
    have hl : c.length / 64 = 4 := by omega
    simp only [low.x86_64.ghash.hash16, chunksOf, hl, List.range_succ, List.range_zero, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, List.getElem!_cons_zero, List.getElem!_cons_succ,
      ]
    simp only [loadBytes512_chunk, pshufb512_eq, setzero512_eq, insert512_eq, xor512q_eq, bind_ok, pshufb_byteswap]
    have i0 : (I32.bv 0#i32).toNat % 4 = 0 := by decide
    have e0 : (ofLanes128 fun j => reverseBytesQuad32 (loadBytes (List.take 16 (List.drop (16 * (4 * 0 + j)) c))) ^^^
        if j = (I32.bv 0#i32).toNat % 4 then current else 0) = ofLanes128 fun j => X j := by
      apply ofLanes128_ext; intro j hj
      rw [i0]; simp only [X, blockBE]
      by_cases h : j = 0
      · subst h; simp [BitVec.xor_comm]
      · simp [h]
    have ev : ∀ v, 0 < v → (ofLanes128 fun j => reverseBytesQuad32 (loadBytes (List.take 16 (List.drop (16 * (4 * v + j)) c)))) =
        ofLanes128 fun j => X (4 * v + j) := fun v hv => by
      apply ofLanes128_ext; intro j hj
      simp only [X, blockBE]
      have h : ¬(4 * v + j = 0) := by omega
      simp only [h, ite_false]
    rw [e0, ev 1 (by decide), ev 2 (by decide), ev 3 (by decide)]
  · have hpad : padBlocks c = (List.range 16).map fun b => blockBE ((c.drop (16 * b)).take 16) := by
      rw [padBlocks, show chunksRest 16 c = [] from List.eq_nil_of_length_eq_zero (by rw [chunksRest_length, hc])]
      simp [chunksOf, hc]
    have hti : (List.range 16).map X = tailInputs current (padBlocks c) := by
      rw [hpad]; simp [List.range_succ, X, tailInputs]
    rw [hyp, ← sumPow_tailInputs H current _ (by rw [hpad]; simp), ← hti, List.map_map]


/-! ## `GhashTableAvx512::add` -/

/-- A 256-byte chunk's blocks are its sixteen 16-byte ones. -/
theorem chunks_256 (bytes : List U8) :
    chunksOf 16 bytes = (chunksOf 256 bytes).flatMap (chunksOf 16) ++ chunksOf 16 (chunksRest 256 bytes) ∧
      chunksRest 16 bytes = chunksRest 16 (chunksRest 256 bytes) := by
  induction h : bytes.length using Nat.strong_induction_on generalizing bytes with
  | _ n ih =>
    by_cases hl : bytes.length < 256
    · simp [chunksOf_of_lt hl, chunksRest_of_lt hl]
    · have hl' : 256 ≤ bytes.length := by omega
      have h256 : (bytes.take 256).length = 16 * 16 := by simp; omega
      obtain ⟨ih1, ih2⟩ := ih (bytes.drop 256).length (by simp; omega) (bytes.drop 256) rfl
      have e := List.take_append_drop 256 bytes
      constructor
      · rw [chunksOf_cons (by omega) hl', chunksRest_cons (by omega) hl', List.flatMap_cons, List.append_assoc,
          ← ih1, ← chunksOf_append (by omega) 16 _ _ h256, e]
      · rw [chunksRest_cons (by omega) hl', ← ih2]
        conv_lhs => rw [← e]
        rw [chunksRest_append (by omega) 16 _ _ h256]

theorem padBlocks_256 (c : List U8) (hc : c.length = 256) : padBlocks c = (chunksOf 16 c).map blockBE := by
  have : chunksRest 16 c = [] := List.eq_nil_of_length_eq_zero (by rw [chunksRest_length, hc])
  simp [padBlocks, this]

theorem padBlocks_split256 (bytes : List U8) :
    padBlocks bytes = (chunksOf 256 bytes).flatMap padBlocks ++ padBlocks (chunksRest 256 bytes) := by
  obtain ⟨h1, h2⟩ := chunks_256 bytes
  have hflat : (chunksOf 256 bytes).flatMap padBlocks = ((chunksOf 256 bytes).flatMap (chunksOf 16)).map blockBE := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro c hc
    exact padBlocks_256 c (chunksOf_length_mem hc)
  rw [hflat, padBlocks, padBlocks, h1, h2, List.map_append, List.append_assoc]

theorem add_loop512_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.GhashTableAvx512)
    (ht : Avx512Powers H t) :
    ∀ (chunks : List (List U8)) (x : BitVec 128), (∀ c ∈ chunks, c.length = 256) →
      ∃ y, low.x86_64.ghash.GhashTableAvx512.add_loop t
          (ofLanes128 fun _ => 0x00010203_04050607_08090a0b_0c0d0e0f#128) chunks x = ok y ∧
        toPoly y = ghashPoly H (toPoly x) ((chunks.flatMap padBlocks).map toPoly)
  | [], x, _ => ⟨x, rfl, by simp [ghashPoly_nil]⟩
  | c :: chunks, x, hc => by
    obtain ⟨y, hy, hyp⟩ := hash16_spec H hH t ht c (hc c (by simp)) x
    obtain ⟨z, hz, hzp⟩ := add_loop512_spec H hH t ht chunks y (fun c h => hc c (by simp [h]))
    refine ⟨z, by rw [low.x86_64.ghash.GhashTableAvx512.add_loop, hy, bind_ok, hz], ?_⟩
    rw [hzp, hyp, padBlocks_256 c (hc c (by simp)), List.flatMap_cons, List.map_append, ghashPoly_append,
      padBlocks_256 c (hc c (by simp))]

/-- `GhashTableAvx512::add` hashes the padded blocks of the bytes from the
state `x`, for tables of `H`'s powers. -/
theorem avx512_add_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.GhashTableAvx512)
    (ht : Avx512Powers H t) (htc : TableFor H t.clmul) (bytes : List U8) (x : BitVec 128) :
    ∃ y, low.x86_64.ghash.GhashTableAvx512.add t bytes x = ok y ∧
      toPoly y = ghashPoly H (toPoly x) ((padBlocks bytes).map toPoly) := by
  obtain ⟨y, hy, hyp⟩ := add_loop512_spec H hH t ht (chunksOf 256 bytes) x (fun c h => chunksOf_length_mem h)
  obtain ⟨z, hz, hzp⟩ := clmul_add_spec H hH t.clmul htc (chunksRest 256 bytes) y
  refine ⟨z, ?_, ?_⟩
  · rw [low.x86_64.ghash.GhashTableAvx512.add, low.x86_64.ghash.BYTESWAP, bind_ok, broadcast512_eq, bind_ok, hy,
      bind_ok, hz]
  · rw [hzp, hyp, padBlocks_split256 bytes, List.map_append, ghashPoly_append]

/-! ## `_mul_tail` -/

theorem clmul_zero_right (x : BitVec 64) : clmul x 0 = 0 :=
  toPoly_inj (by rw [toPoly_clmul, toPoly_zero, mul_zero, toPoly_zero])

theorem mulModel_zero (a : BitVec 128) : mulModel a 0 = 0 := by
  have h0 : lo (0 : BitVec 128) = 0 := rfl
  have hs : swap (0 : BitVec 128) = 0 := by decide
  have h1 : hi (0 : BitVec 128) = 0 := rfl
  have h00 : (0 : BitVec 128) ^^^ 0 = 0 := rfl
  simp only [mulModel, h0, h1, h00, hs, clmul_zero_right]

theorem ofLanes128_lane128 (x : BitVec 512) : ofLanes128 (lane128 x) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [getLsbD_ofLanes128, lane128, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
    Nat.mod_lt k (show 128 > 0 by omega)]
  congr 1; omega

/-- A lane's schoolbook terms, as one product. -/
noncomputable def tri (L M Hh : BitVec 128) : P := toPoly L + X ^ 64 * toPoly M + X ^ 128 * toPoly Hh

theorem tri_step (L M Hh a b : BitVec 128) :
    tri (L ^^^ clmul (lo a) (lo b)) (M ^^^ clmul (hi a) (lo b) ^^^ clmul (lo a) (hi b)) (Hh ^^^ clmul (hi a) (hi b)) =
      tri L M Hh + toPoly a * toPoly b := by
  simp only [tri, toPoly_xor, toPoly_clmul]
  rw [toPoly_halves a, toPoly_halves b]
  ring

/-- `_mul_tail`'s power for lane `i` of vector `j`: the block `4j + i`'s, H^(n - 4j - i),
or zero past the `n` blocks. -/
def tailKey (pw : List (BitVec 128)) (n j i : Nat) : BitVec 128 :=
  if 4 * j + i < n then pw[16 - n + 4 * j + i]! else 0

/-- `_mul_tail`'s block for lane `i` of the vector `x`, the `j`th, `current` XORed into the first. -/
def tailX (current : BitVec 128) (x : BitVec 512) (j i : Nat) : BitVec 128 :=
  lane128 x i ^^^ if j = 0 ∧ i = 0 then current else 0

/-- The products lane `i` sums over the vectors `xs`, the first the `j`th. -/
def tailPairs (pw : List (BitVec 128)) (n : Nat) (current : BitVec 128) (i : Nat) :
    Nat → List (BitVec 512) → List (BitVec 128 × BitVec 128)
  | _, [] => []
  | j, x :: xs => (tailX current x j i, tailKey pw n j i) :: tailPairs pw n current i (j + 1) xs

theorem mul_tail_loop_spec (pw : List (BitVec 128)) (hpw : pw.length = 16) (n : Nat) (hn : n ≤ 16)
    (current : BitVec 128) :
    ∀ (xs : List (BitVec 512)) (j : Nat) (L M Hh : Nat → BitVec 128), 4 * (j + xs.length) ≤ n + 3 →
      ∃ L' M' Hh', low.x86_64.ghash.mul_tail_loop pw n current j xs (ofLanes128 L, ofLanes128 M, ofLanes128 Hh) =
        ok (ofLanes128 L', ofLanes128 M', ofLanes128 Hh') ∧
        ∀ i < 4, tri (L' i) (M' i) (Hh' i) = tri (L i) (M i) (Hh i) +
          ((tailPairs pw n current i j xs).map fun p => toPoly p.1 * toPoly p.2).sum
  | [], j, L, M, Hh, _ => ⟨L, M, Hh, rfl, fun i _ => by simp [tailPairs]⟩
  | x :: xs, j, L, M, Hh, hj => by
    obtain ⟨i0, -, -, -, a0, a4, b0, b4, c0, c4, d0, d4⟩ := imm_facts
    obtain ⟨f, rfl⟩ : ∃ f, x = ofLanes128 f := ⟨lane128 x, (ofLanes128_lane128 x).symm⟩
    have hx' : (if j = 0 then do
          let z ← core.core_arch.x86.avx512f._mm512_setzero_si512
          let c ← core.core_arch.x86.avx512f._mm512_inserti32x4 0#i32 z current
          core.core_arch.x86.avx512f._mm512_xor_epi64 (ofLanes128 f) c
        else ok (ofLanes128 f)) = ok (ofLanes128 fun i => tailX current (ofLanes128 f) j i) := by
      by_cases h : j = 0
      · rw [ite_eq_left h, setzero512_eq, bind_ok, insert512_eq, bind_ok, xor512q_eq]
        refine congrArg ok (ofLanes128_ext _ _ fun i hi => ?_)
        rw [tailX, lane128_ofLanes128 f i hi, i0]
        by_cases hi0 : i = 0 <;> simp [hi0, h]
      · rw [ite_eq_right h]
        refine congrArg ok (ofLanes128_ext _ _ fun i hi => ?_)
        rw [tailX, lane128_ofLanes128 f i hi]
        simp [h]
    have hs : ¬ 16 - n + 4 * j > pw.length := by simp only [List.length_cons] at hj; omega
    have hk : ¬ min (n - 4 * j) 4 > (pw.drop (16 - n + 4 * j)).length := by
      simp only [List.length_cons, List.length_drop] at hj ⊢; omega
    have hh : (ofLanes128 fun i => if i < min (n - 4 * j) 4 then (pw.drop (16 - n + 4 * j))[i]! else 0) =
        ofLanes128 fun i => tailKey pw n j i := by
      apply ofLanes128_ext; intro i hi
      simp only [tailKey]
      by_cases h : 4 * j + i < n
      · rw [ite_eq_left (by omega), ite_eq_left h, List.getElem!_drop]
      · rw [ite_eq_right (by omega), ite_eq_right h]
    simp only [low.x86_64.ghash.mul_tail_loop, hx', bind_ok, hs, hk, ite_false, hh, clmul512_eq, xor512_eq,
      ternary512_eq, a0, a4, b0, b4, c0, c4, d0, d4, ite_true, ite_false, Bool.false_eq_true, lane64_0, lane64_1]
    obtain ⟨L', M', Hh', he, hp⟩ := mul_tail_loop_spec pw hpw n hn current xs (j + 1) _ _ _
      (by simp only [List.length_cons] at hj; omega)
    refine ⟨L', M', Hh', he, fun i hi => ?_⟩
    rw [hp i hi, tri_step, tailPairs, List.map_cons, List.sum_cons]
    ring

theorem tailPairs_sum (pw : List (BitVec 128)) (n : Nat) (current : BitVec 128) (i : Nat) :
    ∀ (xs : List (BitVec 512)) (j : Nat),
      ((tailPairs pw n current i j xs).map fun p => toPoly (mulModel p.1 p.2)).sum =
        ((List.range xs.length).map fun m =>
          toPoly (mulModel (tailX current xs[m]! (j + m) i) (tailKey pw n (j + m) i))).sum
  | [], j => by simp [tailPairs]
  | x :: xs, j => by
    rw [tailPairs, List.map_cons, List.sum_cons, tailPairs_sum pw n current i xs (j + 1), List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [Function.comp_def, List.getElem!_cons_zero, List.getElem!_cons_succ, Nat.add_zero]
    exact congrArg (_ + ·) (congrArg List.sum (List.map_congr_left fun m _ => by
      rw [show j + 1 + m = j + (m + 1) by omega]))

theorem sumPow_range (H : P) : ∀ (n : Nat) (f : Nat → P),
    sumPow H ((List.range n).map f) = ((List.range n).map fun k => gf128MulRev (f k) (gPower H (n - k))).sum
  | 0, f => by simp [sumPow_nil]
  | n + 1, f => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, sumPow_cons, sumPow_range H n, List.length_map,
      List.length_range, List.map_cons, List.sum_cons, List.map_map]
    simp only [Function.comp_def, Nat.sub_zero]
    exact congrArg (_ + ·) (congrArg List.sum (List.map_congr_left fun m _ => by
      rw [show n + 1 - m.succ = n - m by omega]))

/-- The four lanes' sums over the vectors are the sum over the blocks. -/
theorem grid (n : Nat) (hn : 1 ≤ n) (hn' : n ≤ 16) (g : Nat → P) :
    ((List.range 4).map fun i =>
      ((List.range ((n + 3) / 4)).map fun m => if 4 * m + i < n then g (4 * m + i) else 0).sum).sum =
      ((List.range n).map g).sum := by
  interval_cases n <;> simp [List.range_succ] <;> ring

/-- The tail's block `b`: lane `b % 4` of the vector `b / 4`, `current` XORed into the first. -/
def tailBlock512 (current : BitVec 128) (x : List (BitVec 512)) (b : Nat) : BitVec 128 :=
  lane128 x[b / 4]! (b % 4) ^^^ if b = 0 then current else 0

theorem mul_tail_sum (H : P) (hH : Small H) (t : low.x86_64.ghash.GhashTableAvx512) (ht : Avx512Powers H t)
    (current : BitVec 128) (x : List (BitVec 512)) (len : Nat) (hlen : len ≤ 256) (h0 : 0 < len)
    (hx : (len + 15) / 16 ≤ 4 * x.length) :
    ∃ y, low.x86_64.ghash._mul_tail t current x len = ok y ∧
      toPoly y = sumPow H ((List.range ((len + 15) / 16)).map fun b => toPoly (tailBlock512 current x b)) := by
  obtain ⟨s, hs, hl, hp⟩ := ht
  obtain ⟨-, -, -, -, -, -, b0, b4, -, -, -, -⟩ := imm_facts
  have hn0 : (len + 15) / 16 ≠ 0 := by omega
  have hn16 : (len + 15) / 16 ≤ 16 := by omega
  generalize hJ : ((len + 15) / 16 + 3) / 4 = J
  obtain ⟨L', M', Hh', he, hpoly⟩ := mul_tail_loop_spec s.val hl ((len + 15) / 16) hn16 current (x.take J) 0
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (by simp only [List.length_take]; omega)
  obtain ⟨i0, i1, i2, i3, -, -, b0, b4, -, -, -, -⟩ := imm_facts
  simp only [low.x86_64.ghash._mul_tail, show ¬ len > 256 by omega, ite_false, hn0, hs, bind_ok, setzero512_eq,
    hJ, he, broadcast512_eq, low.x86_64.ghash.sumLanes, uncurry_apply_pair]
  simp only [clmul512_eq, shuffle512_eq, ternary512_eq, b0, b4, ite_true, ite_false, Bool.false_eq_true, polyLo_hi,
    lane64_0, lane64_1, extract512_eq, bind_ok, i0, i1, i2, i3]
  simp only [fold_eq, core.core_arch.x86.sse2._mm_xor_si128, ternary128_eq, bind_ok]
  refine ⟨_, rfl, ?_⟩
  generalize hn : (len + 15) / 16 = n at *
  let g : Nat → P := fun b => gf128MulRev (toPoly (tailBlock512 current x b)) (gPower H (n - b))
  have hJx : J ≤ x.length := by omega
  have hlane : ∀ i < 4, toPoly (reduceModel (L' i) (M' i ^^^ L' i ^^^ Hh' i) (Hh' i)) =
      ((List.range J).map fun m => if 4 * m + i < n then g (4 * m + i) else 0).sum := fun i hi => by
    rw [fold_sum _ _ _ (tailPairs s.val n current i 0 (x.take J)) (by
        have h := hpoly i hi
        simp only [tri, toPoly_zero, mul_zero, add_zero, zero_add] at h
        exact h),
      tailPairs_sum, List.length_take, Nat.min_eq_left hJx]
    refine congrArg List.sum (List.map_congr_left fun m hm => ?_)
    have hm' : m < J := List.mem_range.1 hm
    have hxm : (x.take J)[m]! = x[m]! := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_take, hm']
    have hb : tailX current x[m]! (0 + m) i = tailBlock512 current x (4 * m + i) := by
      simp only [tailX, tailBlock512, show (4 * m + i) / 4 = m by omega, show (4 * m + i) % 4 = i by omega,
        Nat.zero_add]
      congr 1
      by_cases h : 4 * m + i = 0
      · rw [ite_eq_left (by omega), ite_eq_left h]
      · rw [ite_eq_right (by omega), ite_eq_right h]
    rw [hxm, hb, tailKey, Nat.zero_add]
    by_cases h : 4 * m + i < n
    · rw [ite_eq_left h, ite_eq_left h,
        mul_data _ _ _ (small_gPower H hH _) (hp (16 - n + 4 * m + i) (by omega)),
        show 16 - (16 - n + 4 * m + i) = n - (4 * m + i) by omega]
    · rw [ite_eq_right h, ite_eq_right h, mulModel_zero, toPoly_zero]
  rw [toPoly_xor, toPoly_xor, toPoly_xor, hlane 0 (by omega), hlane 1 (by omega), hlane 2 (by omega),
    hlane 3 (by omega), sumPow_range, ← grid n (by omega) hn16 g, ← hJ]
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.map_append, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
  ring

end rind.x86_64
