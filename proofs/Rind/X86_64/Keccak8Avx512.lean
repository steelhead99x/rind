import Rind.X86_64.Funs
import Rind.KeccakStates
open Aeneas Aeneas.Std Result rind.simd rind.spec

/-!
# The eight-way AVX-512 Keccak-f, proven to compute Keccak-f

`low::x86_64::sha3_keccak8_f1600::permute` runs Keccak-f[1600] on eight
states at once: it transposes them into 25 `__m512i` vectors, element `i` of
vector `k` lane `k` of state `i`, runs 24 rounds on the vectors, and
transposes them back. `permute_spec` proves it computes s2n-bignum's
`keccak 24` on each state, over `Rind.X86_64.Simd`'s models of the AVX-512
intrinsics and `Rind.X86_64.FunsExternal`'s of `set_row`, the one store
through a pointer. `round_eq` proves a round of the vectors is
`keccakRound` on each state's lanes, by unfolding both; `transpose_eq`
proves `transpose` transposes eight vectors of eight elements.
-/

namespace rind.x86_64.keccak8

/-- A vector from its eight 64-bit elements, element 0 lowest. -/
local notation "Q" => ofLanes64x8

theorem getLsbD_Q (f : Nat → BitVec 64) (k : Nat) :
    (Q f).getLsbD k = (decide (k < 512) && (f (k / 64)).getLsbD (k % 64)) := by
  by_cases hk : k < 512
  · simp only [ofLanes64x8, BitVec.getLsbD_append]
    split_ifs <;>
    first
    | rw [show k / 64 = 0 by omega, show k % 64 = k by omega]; simp [show k < 512 by omega]
    | rw [show k / 64 = 1 by omega, show k % 64 = k - 64 by omega]; simp [show k < 512 by omega]
    | rw [show k / 64 = 2 by omega, show k % 64 = k - 64 - 64 by omega]; simp [show k < 512 by omega]
    | rw [show k / 64 = 3 by omega, show k % 64 = k - 64 - 64 - 64 by omega]; simp [show k < 512 by omega]
    | rw [show k / 64 = 4 by omega, show k % 64 = k - 64 - 64 - 64 - 64 by omega]; simp [show k < 512 by omega]
    | rw [show k / 64 = 5 by omega, show k % 64 = k - 64 - 64 - 64 - 64 - 64 by omega]; simp [show k < 512 by omega]
    | rw [show k / 64 = 6 by omega, show k % 64 = k - 64 - 64 - 64 - 64 - 64 - 64 by omega]; simp [show k < 512 by omega]
    | rw [show k / 64 = 7 by omega, show k % 64 = k - 64 - 64 - 64 - 64 - 64 - 64 - 64 by omega]; simp [show k < 512 by omega]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [hk]

theorem lane_Q (f : Nat → BitVec 64) (i : Nat) (h : i < 8) : lane64x8 (Q f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [lane64x8, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, getLsbD_Q]
  simp [show 64 * i + k < 512 by omega, show (64 * i + k) / 64 = i by omega,
    show (64 * i + k) % 64 = k by omega]

theorem Q_lane (x : BitVec 512) : Q (lane64x8 x) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [getLsbD_Q, hk, decide_true, Bool.true_and, lane64x8, BitVec.getLsbD_extractLsb']
  simp [show k % 64 < 64 by omega, show 64 * (k / 64) + k % 64 = k by omega]

theorem Q_congr {f g : Nat → BitVec 64} (h : ∀ i < 8, f i = g i) : Q f = Q g := by
  simp only [ofLanes64x8, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem ternary150 {w : Nat} (a b c : BitVec w) : ternary 150#8 a b c = a ^^^ b ^^^ c := by
  have h0 : (150#8).getLsbD 0 = false := by decide
  have h1 : (150#8).getLsbD 1 = true := by decide
  have h2 : (150#8).getLsbD 2 = true := by decide
  have h3 : (150#8).getLsbD 3 = false := by decide
  have h4 : (150#8).getLsbD 4 = true := by decide
  have h5 : (150#8).getLsbD 5 = false := by decide
  have h6 : (150#8).getLsbD 6 = false := by decide
  have h7 : (150#8).getLsbD 7 = true := by decide
  simp only [ternary, h0, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, ite_false, ite_true]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor, hk,
    decide_true, Bool.true_and, BitVec.getLsbD_zero, Bool.false_or, Bool.or_false]
  have hz : ∀ n i, (0 : BitVec n).getLsbD i = false := fun _ _ => BitVec.getLsbD_zero
  simp only [hz]
  cases a.getLsbD k <;> cases b.getLsbD k <;> cases c.getLsbD k <;> rfl

theorem ternary210 {w : Nat} (a b c : BitVec w) : ternary 210#8 a b c = a ^^^ (~~~b &&& c) := by
  have h0 : (210#8).getLsbD 0 = false := by decide
  have h1 : (210#8).getLsbD 1 = true := by decide
  have h2 : (210#8).getLsbD 2 = false := by decide
  have h3 : (210#8).getLsbD 3 = false := by decide
  have h4 : (210#8).getLsbD 4 = true := by decide
  have h5 : (210#8).getLsbD 5 = false := by decide
  have h6 : (210#8).getLsbD 6 = true := by decide
  have h7 : (210#8).getLsbD 7 = true := by decide
  simp only [ternary, h0, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, ite_false, ite_true]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor, hk,
    decide_true, Bool.true_and, BitVec.getLsbD_zero, Bool.false_or, Bool.or_false]
  have hz : ∀ n i, (0 : BitVec n).getLsbD i = false := fun _ _ => BitVec.getLsbD_zero
  simp only [hz]
  cases a.getLsbD k <;> cases b.getLsbD k <;> cases c.getLsbD k <;> rfl

theorem xor_Q (f g : Nat → BitVec 64) : Q f ^^^ Q g = Q fun i => f i ^^^ g i := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_xor, getLsbD_Q, hk, decide_true, Bool.true_and]

theorem and_Q (f g : Nat → BitVec 64) : Q f &&& Q g = Q fun i => f i &&& g i := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_and, getLsbD_Q, hk, decide_true, Bool.true_and]

theorem not_Q (f : Nat → BitVec 64) : ~~~Q f = Q fun i => ~~~f i := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_not, getLsbD_Q, hk, decide_true, Bool.true_and, show k % 64 < 64 by omega]

theorem getLsbD_ofLanes128 (f : Nat → BitVec 128) (k : Nat) :
    (ofLanes128 f).getLsbD k = (decide (k < 512) && (f (k / 128)).getLsbD (k % 128)) := by
  by_cases hk : k < 512
  · simp only [ofLanes128, BitVec.getLsbD_append]
    split_ifs <;>
    first
    | rw [show k / 128 = 0 by omega, show k % 128 = k by omega]; simp [show k < 512 by omega]
    | rw [show k / 128 = 1 by omega, show k % 128 = k - 128 by omega]; simp [show k < 512 by omega]
    | rw [show k / 128 = 2 by omega, show k % 128 = k - 128 - 128 by omega]; simp [show k < 512 by omega]
    | rw [show k / 128 = 3 by omega, show k % 128 = k - 128 - 128 - 128 by omega]; simp [show k < 512 by omega]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [hk]

/-- Element `i` of a vector of 128-bit lanes: half `i % 2` of lane `i / 2`. -/
theorem lane_ofLanes128 (F : Nat → BitVec 128) (i : Nat) (hi : i < 8) :
    lane64x8 (ofLanes128 F) i = (F (i / 2)).extractLsb' (64 * (i % 2)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [lane64x8, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, getLsbD_ofLanes128]
  simp [show 64 * i + k < 512 by omega, show (64 * i + k) / 128 = i / 2 by omega,
    show (64 * i + k) % 128 = 64 * (i % 2) + k by omega]

/-- Lane `j` of a vector of 64-bit elements: elements `2j + 1` and `2j`. -/
theorem lane128_Q (f : Nat → BitVec 64) (j : Nat) (hj : j < 4) :
    lane128 (Q f) j = f (2 * j + 1) ++ f (2 * j) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [lane128, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, getLsbD_Q,
    BitVec.getLsbD_append]
  by_cases h : k < 64
  · simp [h, show 128 * j + k < 512 by omega, show (128 * j + k) / 64 = 2 * j by omega,
      show (128 * j + k) % 64 = k by omega]
  · simp [h, show 128 * j + k < 512 by omega, show (128 * j + k) / 64 = 2 * j + 1 by omega,
      show (128 * j + k) % 64 = k - 64 by omega]

theorem extract_append_lo (x y : BitVec 64) : (x ++ y).extractLsb' 0 64 = y := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hk, decide_true, Bool.true_and,
    Nat.zero_add, ite_true]

theorem extract_append_hi (x y : BitVec 64) : (x ++ y).extractLsb' 64 64 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hk, decide_true, Bool.true_and,
    show ¬(64 + k < 64) by omega, ite_false, Nat.add_sub_cancel_left]

theorem lane64_append_lo (x y : BitVec 64) : lane64 (x ++ y) 0 = y := extract_append_lo x y
theorem lane64_append_hi (x y : BitVec 64) : lane64 (x ++ y) 1 = x := extract_append_hi x y

theorem unpacklo_Q (f g : Nat → BitVec 64) :
    core.core_arch.x86.avx512f._mm512_unpacklo_epi64 (Q f) (Q g) =
      ok (Q fun i => if i % 2 = 0 then f i else g (i - 1)) := by
  simp only [core.core_arch.x86.avx512f._mm512_unpacklo_epi64, ok.injEq]
  rw [← Q_lane (ofLanes128 _)]
  apply Q_congr; intro i hi
  rw [lane_ofLanes128 _ _ hi, lane128_Q _ _ (by omega), lane128_Q _ _ (by omega)]
  interval_cases i <;> simp [lane64_append_lo, extract_append_lo, extract_append_hi]

theorem unpackhi_Q (f g : Nat → BitVec 64) :
    core.core_arch.x86.avx512f._mm512_unpackhi_epi64 (Q f) (Q g) =
      ok (Q fun i => if i % 2 = 0 then f (i + 1) else g i) := by
  simp only [core.core_arch.x86.avx512f._mm512_unpackhi_epi64, ok.injEq]
  rw [← Q_lane (ofLanes128 _)]
  apply Q_congr; intro i hi
  rw [lane_ofLanes128 _ _ hi, lane128_Q _ _ (by omega), lane128_Q _ _ (by omega)]
  interval_cases i <;> simp [lane64_append_hi, extract_append_lo, extract_append_hi]

theorem shuffle_Q (m : Std.I32) (f g : Nat → BitVec 64) :
    core.core_arch.x86.avx512f._mm512_shuffle_i64x2 m (Q f) (Q g) =
      ok (Q fun i => (if i / 2 < 2 then f else g) (2 * (m.bv.toNat / 4 ^ (i / 2) % 4) + i % 2)) := by
  simp only [core.core_arch.x86.avx512f._mm512_shuffle_i64x2, ok.injEq]
  rw [← Q_lane (ofLanes128 _)]
  apply Q_congr; intro i hi
  rw [lane_ofLanes128 _ _ hi]
  have hs : m.bv.toNat / 4 ^ (i / 2) % 4 < 4 := Nat.mod_lt _ (by omega)
  generalize m.bv.toNat / 4 ^ (i / 2) % 4 = s at hs ⊢
  interval_cases i <;> simp [lane128_Q _ _ hs, extract_append_lo, extract_append_hi]

theorem rol_Q (k : Std.I32) (f : Nat → BitVec 64) :
    core.core_arch.x86.avx512f._mm512_rol_epi64 k (Q f) =
      ok (Q fun i => (f i).rotateLeft (k.bv.toNat % 64)) := by
  simp only [core.core_arch.x86.avx512f._mm512_rol_epi64, ok.injEq]
  exact Q_congr fun i hi => by rw [lane_Q _ _ hi]

theorem ternarylogic150_Q (f g h : Nat → BitVec 64) :
    core.core_arch.x86.avx512f._mm512_ternarylogic_epi64 150#i32 (Q f) (Q g) (Q h) =
      ok (Q fun i => f i ^^^ g i ^^^ h i) := by
  simp only [core.core_arch.x86.avx512f._mm512_ternarylogic_epi64, ok.injEq,
    show (150#i32).bv.setWidth 8 = 150#8 from rfl, ternary150, xor_Q]

theorem ternarylogic210_Q (f g h : Nat → BitVec 64) :
    core.core_arch.x86.avx512f._mm512_ternarylogic_epi64 210#i32 (Q f) (Q g) (Q h) =
      ok (Q fun i => f i ^^^ (~~~g i &&& h i)) := by
  simp only [core.core_arch.x86.avx512f._mm512_ternarylogic_epi64, ok.injEq,
    show (210#i32).bv.setWidth 8 = 210#8 from rfl, ternary210, xor_Q, and_Q, not_Q]

theorem xor512_Q (f g : Nat → BitVec 64) :
    core.core_arch.x86.avx512f._mm512_xor_si512 (Q f) (Q g) = ok (Q fun i => f i ^^^ g i) := by
  simp only [core.core_arch.x86.avx512f._mm512_xor_si512, xor_Q]

theorem set1_Q (a : Std.I64) :
    core.core_arch.x86.avx512f._mm512_set1_epi64 a = ok (Q fun _ => a.bv) := rfl

theorem setr_Q (e0 e1 e2 e3 e4 e5 e6 e7 : Std.I64) :
    core.core_arch.x86.avx512f._mm512_setr_epi64 e0 e1 e2 e3 e4 e5 e6 e7 =
      ok (Q fun i => [e0.bv, e1.bv, e2.bv, e3.bv, e4.bv, e5.bv, e6.bv, e7.bv][i]!) := rfl

/-- Eight states as 25 vectors: element `i` of vector `k` is lane `k` of state `i`. -/
def vecs (S : Nat → List (BitVec 64)) : Std.Array core.core_arch.x86.__m512i 25#usize :=
  Array.make 25#usize ((List.range 25).map fun k => Q fun i => (S i)[k]!) (by simp)

theorem vecs_eq (S : Nat → List (BitVec 64)) :
    vecs S = Array.make 25#usize [Q fun i => (S i)[0]!, Q fun i => (S i)[1]!, Q fun i => (S i)[2]!, Q fun i => (S i)[3]!, Q fun i => (S i)[4]!, Q fun i => (S i)[5]!, Q fun i => (S i)[6]!, Q fun i => (S i)[7]!, Q fun i => (S i)[8]!, Q fun i => (S i)[9]!, Q fun i => (S i)[10]!, Q fun i => (S i)[11]!, Q fun i => (S i)[12]!, Q fun i => (S i)[13]!, Q fun i => (S i)[14]!, Q fun i => (S i)[15]!, Q fun i => (S i)[16]!, Q fun i => (S i)[17]!, Q fun i => (S i)[18]!, Q fun i => (S i)[19]!, Q fun i => (S i)[20]!, Q fun i => (S i)[21]!, Q fun i => (S i)[22]!, Q fun i => (S i)[23]!, Q fun i => (S i)[24]!] := rfl

theorem hcast_I64_bv (x : U64) : (UScalar.hcast .I64 x).bv = x.bv := by
  rw [UScalar.hcast_bv_eq]; exact BitVec.setWidth_eq x.bv

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem round_eq (S : Nat → List (BitVec 64)) (rc : U64) :
    low.x86_64.sha3_keccak8_f1600.round (vecs S) rc = ok (vecs fun i => keccakRound rc.bv (S i)) := by
  unfold low.x86_64.sha3_keccak8_f1600.round low.x86_64.sha3_keccak8_f1600.xor3
    low.x86_64.sha3_keccak8_f1600.xor_andnot
  rw [vecs_eq]
  simp only [Array.index_usize, Array.getElem?_Usize_eq, Array.make_val,
    show (0#usize : Usize).val = 0 from rfl, show (1#usize : Usize).val = 1 from rfl,
    show (2#usize : Usize).val = 2 from rfl, show (3#usize : Usize).val = 3 from rfl,
    show (4#usize : Usize).val = 4 from rfl, show (5#usize : Usize).val = 5 from rfl,
    show (6#usize : Usize).val = 6 from rfl, show (7#usize : Usize).val = 7 from rfl,
    show (8#usize : Usize).val = 8 from rfl, show (9#usize : Usize).val = 9 from rfl,
    show (10#usize : Usize).val = 10 from rfl, show (11#usize : Usize).val = 11 from rfl,
    show (12#usize : Usize).val = 12 from rfl, show (13#usize : Usize).val = 13 from rfl,
    show (14#usize : Usize).val = 14 from rfl, show (15#usize : Usize).val = 15 from rfl,
    show (16#usize : Usize).val = 16 from rfl, show (17#usize : Usize).val = 17 from rfl,
    show (18#usize : Usize).val = 18 from rfl, show (19#usize : Usize).val = 19 from rfl,
    show (20#usize : Usize).val = 20 from rfl, show (21#usize : Usize).val = 21 from rfl,
    show (22#usize : Usize).val = 22 from rfl, show (23#usize : Usize).val = 23 from rfl,
    show (24#usize : Usize).val = 24 from rfl,
    List.getElem?_cons_succ, List.getElem?_cons_zero, bind_ok]
  simp only [ternarylogic150_Q, ternarylogic210_Q, rol_Q, xor512_Q, set1_Q, bind_ok, lift]
  simp only [Array.update, Array.getElem?_Usize_eq, Array.make_val,
    show (0#usize : Usize).val = 0 from rfl, show (1#usize : Usize).val = 1 from rfl,
    show (2#usize : Usize).val = 2 from rfl, show (3#usize : Usize).val = 3 from rfl,
    show (4#usize : Usize).val = 4 from rfl, show (5#usize : Usize).val = 5 from rfl,
    show (6#usize : Usize).val = 6 from rfl, show (7#usize : Usize).val = 7 from rfl,
    show (8#usize : Usize).val = 8 from rfl, show (9#usize : Usize).val = 9 from rfl,
    show (10#usize : Usize).val = 10 from rfl, show (11#usize : Usize).val = 11 from rfl,
    show (12#usize : Usize).val = 12 from rfl, show (13#usize : Usize).val = 13 from rfl,
    show (14#usize : Usize).val = 14 from rfl, show (15#usize : Usize).val = 15 from rfl,
    show (16#usize : Usize).val = 16 from rfl, show (17#usize : Usize).val = 17 from rfl,
    show (18#usize : Usize).val = 18 from rfl, show (19#usize : Usize).val = 19 from rfl,
    show (20#usize : Usize).val = 20 from rfl, show (21#usize : Usize).val = 21 from rfl,
    show (22#usize : Usize).val = 22 from rfl, show (23#usize : Usize).val = 23 from rfl,
    show (24#usize : Usize).val = 24 from rfl,
    List.getElem?_cons_zero, ok.injEq]
  apply Aeneas.Std.Array.ext
  simp only [Array.from_val, vecs_eq, Array.make_val, List.set_cons_zero, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;>
  · apply Q_congr; intro i _
    simp only [keccakRound, List.getElem!_cons_succ, List.getElem!_cons_zero,
      show (I32.bv 0#i32).toNat % 64 = 0 from rfl, show (I32.bv 1#i32).toNat % 64 = 1 from rfl,
      show (I32.bv 2#i32).toNat % 64 = 2 from rfl, show (I32.bv 3#i32).toNat % 64 = 3 from rfl,
      show (I32.bv 6#i32).toNat % 64 = 6 from rfl, show (I32.bv 8#i32).toNat % 64 = 8 from rfl,
      show (I32.bv 10#i32).toNat % 64 = 10 from rfl, show (I32.bv 14#i32).toNat % 64 = 14 from rfl,
      show (I32.bv 15#i32).toNat % 64 = 15 from rfl, show (I32.bv 18#i32).toNat % 64 = 18 from rfl,
      show (I32.bv 20#i32).toNat % 64 = 20 from rfl, show (I32.bv 21#i32).toNat % 64 = 21 from rfl,
      show (I32.bv 25#i32).toNat % 64 = 25 from rfl, show (I32.bv 27#i32).toNat % 64 = 27 from rfl,
      show (I32.bv 28#i32).toNat % 64 = 28 from rfl, show (I32.bv 36#i32).toNat % 64 = 36 from rfl,
      show (I32.bv 39#i32).toNat % 64 = 39 from rfl, show (I32.bv 41#i32).toNat % 64 = 41 from rfl,
      show (I32.bv 43#i32).toNat % 64 = 43 from rfl, show (I32.bv 44#i32).toNat % 64 = 44 from rfl,
      show (I32.bv 45#i32).toNat % 64 = 45 from rfl, show (I32.bv 55#i32).toNat % 64 = 55 from rfl,
      show (I32.bv 56#i32).toNat % 64 = 56 from rfl, show (I32.bv 61#i32).toNat % 64 = 61 from rfl,
      show (I32.bv 62#i32).toNat % 64 = 62 from rfl,
      hcast_I64_bv]
    ac_rfl

/-- Rounds `iter.start` to 23 of eight states, whose first `iter.start` are done. -/
theorem rounds_spec (S : Nat → List (BitVec 64)) (rc : Std.Array U64 24#usize)
    (hrc : rc.val.map (·.bv) = keccakRoundConstants)
    (iter : core.ops.range.Range Usize) (v : Std.Array core.core_arch.x86.__m512i 25#usize)
    (hs : iter.start.val ≤ 24) (he : iter.end.val = 24)
    (hv : v = vecs fun i => keccak iter.start.val (S i)) :
    low.x86_64.sha3_keccak8_f1600.keccak8_f1600_loop iter v rc ⦃ r =>
      r = vecs fun i => keccak 24 (S i) ⦄ := by
  unfold low.x86_64.sha3_keccak8_f1600.keccak8_f1600_loop
  apply loop.spec_decr_nat (fun x => 24 - x.1.start.val)
    (fun x => x.1.start.val ≤ 24 ∧ x.1.end.val = 24 ∧ x.2 = vecs fun i => keccak x.1.start.val (S i))
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold low.x86_64.sha3_keccak8_f1600.keccak8_f1600_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step with Array.index_usize_spec rc it.start (by simp; omega) as ⟨c, hc⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      have hcv : c.bv = keccakRoundConstants[it.start.val]! := by
        rw [← hrc, hc, getElem!_pos _ it.start.val (by simp; omega)]; simp
      rw [hst, round_eq]
      simp only [bind_ok, WP.spec_ok]
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hst', hcv]
      rfl
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      have h24 : it.start.val = 24 := by omega
      simpa [h24] using hst
  · exact ⟨hs, he, hv⟩

/-- Eight vectors from a matrix: element `i` of vector `j` is `m j i`. -/
def mat (m : Nat → Nat → BitVec 64) : Std.Array core.core_arch.x86.__m512i 8#usize :=
  Array.make 8#usize [Q (m 0), Q (m 1), Q (m 2), Q (m 3), Q (m 4), Q (m 5), Q (m 6), Q (m 7)]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `transpose` transposes. -/
theorem transpose_eq (m : Nat → Nat → BitVec 64) :
    low.x86_64.sha3_keccak8_f1600.transpose (mat m) = ok (mat fun j i => m i j) := by
  unfold low.x86_64.sha3_keccak8_f1600.transpose
  simp only [mat, Array.index_usize, Array.getElem?_Usize_eq, Array.make_val,
    show (0#usize : Usize).val = 0 from rfl, show (1#usize : Usize).val = 1 from rfl,
    show (2#usize : Usize).val = 2 from rfl, show (3#usize : Usize).val = 3 from rfl,
    show (4#usize : Usize).val = 4 from rfl, show (5#usize : Usize).val = 5 from rfl,
    show (6#usize : Usize).val = 6 from rfl, show (7#usize : Usize).val = 7 from rfl,
    List.getElem?_cons_succ, List.getElem?_cons_zero, bind_ok, unpacklo_Q, unpackhi_Q, shuffle_Q,
    ok.injEq]
  apply Aeneas.Std.Array.ext
  simp only [Array.make_val, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply Q_congr; intro i hi
    interval_cases i <;> simp [show (I32.bv 68#i32).toNat = 68 from rfl,
      show (I32.bv 238#i32).toNat = 238 from rfl, show (I32.bv 136#i32).toNat = 136 from rfl,
      show (I32.bv 221#i32).toNat = 221 from rfl]

@[step]
theorem row_spec (s : Std.Array U64 25#usize) (i : Usize) (hi : i.val + 8 ≤ 25) :
    low.x86_64.sha3_keccak8_f1600.row s i ⦃ r => r = Q fun k => (s.val[i.val + k]!).bv ⦄ := by
  unfold low.x86_64.sha3_keccak8_f1600.row
  step*
  rw [setr_Q]
  simp only [WP.spec_ok]
  apply Q_congr; intro k hk
  rw [getElem!_pos s.val (i.val + k) (by simp; omega)]
  interval_cases k <;> simp_all [hcast_I64_bv]

@[step]
theorem rows_spec (a : Std.Array (Std.Array U64 25#usize) 8#usize) (i : Usize) (hi : i.val + 8 ≤ 25) :
    low.x86_64.sha3_keccak8_f1600.rows a i ⦃ r =>
      r = mat fun j k => (a.val[j]!.val[i.val + k]!).bv ⦄ := by
  unfold low.x86_64.sha3_keccak8_f1600.rows
  step*
  simp only [mat]
  subst_vars
  congr <;> simp [getElem!_pos]

/-- `set_row`: lane `k` of the result is element `k - i` of `v` from lane `i`
to `i + 7`, and lane `k` of `s` elsewhere. -/
@[step]
theorem set_row_spec (s : Std.Array U64 25#usize) (i : Usize) (hi : i.val + 8 ≤ 25) (f : Nat → BitVec 64) :
    low.x86_64.sha3_keccak8_f1600.set_row s i (Q f) ⦃ r =>
      ∀ k < 25, (r.val[k]!).bv = if i.val ≤ k ∧ k < i.val + 8 then f (k - i.val) else (s.val[k]!).bv ⦄ := by
  rw [low.x86_64.sha3_keccak8_f1600.set_row, dite_eq_left hi, WP.spec_ok]
  intro k hk
  have hl : s.val.length = 25 := by simp
  have ht : (s.val.take i.val).length = i.val := by simp; omega
  have hm : ((List.range 8).map fun k => (⟨lane64x8 (Q f) k⟩ : U64)).length = 8 := by simp
  simp only [Array.make_val, List.getElem!_eq_getElem?_getD, List.append_assoc]
  by_cases h1 : k < i.val
  · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt h1,
      ite_eq_right (by omega)]
  · rw [List.getElem?_append_right (by omega), ht]
    by_cases h2 : k < i.val + 8
    · rw [List.getElem?_append_left (by omega), ite_eq_left ⟨by omega, h2⟩, List.getElem?_map,
        List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      exact lane_Q _ _ (by omega)
    · rw [List.getElem?_append_right (by omega), hm, List.getElem?_drop, ite_eq_right (by omega),
        show i.val + 8 + (k - i.val - 8) = k by omega]

theorem set_rows_mat_spec (a : Std.Array (Std.Array U64 25#usize) 8#usize) (i : Usize) (hi : i.val + 8 ≤ 25)
    (m : Nat → Nat → BitVec 64) :
    low.x86_64.sha3_keccak8_f1600.set_rows a i (mat m) ⦃ r =>
      ∀ j < 8, ∀ k < 25, (r.val[j]!.val[k]!).bv =
        if i.val ≤ k ∧ k < i.val + 8 then m j (k - i.val) else (a.val[j]!.val[k]!).bv ⦄ := by
  unfold low.x86_64.sha3_keccak8_f1600.set_rows
  simp only [mat, Array.index_usize, Array.getElem?_Usize_eq, Array.make_val,
    show (0#usize : Usize).val = 0 from rfl, show (1#usize : Usize).val = 1 from rfl,
    show (2#usize : Usize).val = 2 from rfl, show (3#usize : Usize).val = 3 from rfl,
    show (4#usize : Usize).val = 4 from rfl, show (5#usize : Usize).val = 5 from rfl,
    show (6#usize : Usize).val = 6 from rfl, show (7#usize : Usize).val = 7 from rfl,
    List.getElem?_cons_succ, List.getElem?_cons_zero, bind_ok]
  step*
  intro j hj k hk
  interval_cases j <;> simp_all [getElem!_pos]

theorem mat_lane (r : Std.Array core.core_arch.x86.__m512i 8#usize) :
    r = mat fun j => lane64x8 (r.val[j]!) := by
  apply Aeneas.Std.Array.ext
  have hl : r.val.length = 8 := by simp
  simp only [mat, Array.make_val, Q_lane]
  apply List.ext_getElem (by simp [hl]); intro k h1 h2
  rw [← getElem!_pos r.val k h1]
  have hk : k < 8 := by omega
  interval_cases k <;> rfl

theorem lane_mat (m : Nat → Nat → BitVec 64) (j i : Nat) (hj : j < 8) (hi : i < 8) :
    lane64x8 ((mat m).val[j]!) i = m j i := by
  simp only [mat, Array.make_val]
  interval_cases j <;> simp [lane_Q _ _ hi]

/-- `transpose`, element by element. -/
@[step]
theorem transpose_spec (r : Std.Array core.core_arch.x86.__m512i 8#usize) :
    low.x86_64.sha3_keccak8_f1600.transpose r ⦃ t =>
      ∀ j < 8, ∀ i < 8, lane64x8 (t.val[j]!) i = lane64x8 (r.val[i]!) j ⦄ := by
  rw [mat_lane r, transpose_eq, WP.spec_ok]
  intro j hj i hi
  rw [lane_mat _ _ _ hj hi, lane_mat _ _ _ hi hj]

theorem lane_vecs (S : Nat → List (BitVec 64)) (k i : Nat) (hk : k < 25) (hi : i < 8) :
    lane64x8 ((vecs S).val[k]!) i = (S i)[k]! := by
  simp only [vecs, Array.make_val]
  rw [getElem!_pos _ k (by simp; omega)]
  simp [lane_Q _ _ hi]

theorem make_eq_vecs (l : List core.core_arch.x86.__m512i) (hl : l.length = 25)
    (S : Nat → List (BitVec 64)) (h : ∀ k < 25, ∀ i < 8, lane64x8 l[k]! i = (S i)[k]!) :
    Array.make 25#usize l (by simp [hl]) = vecs S := by
  apply Aeneas.Std.Array.ext
  simp only [Array.make_val, vecs]
  apply List.ext_getElem (by simp [hl]); intro k h1 h2
  rw [List.getElem_map, List.getElem_range, ← Q_lane l[k], ← getElem!_pos l k h1]
  exact Q_congr fun i hi => h k (by omega) i hi

@[step]
theorem set_rows_spec (a : Std.Array (Std.Array U64 25#usize) 8#usize) (i : Usize) (hi : i.val + 8 ≤ 25)
    (r : Std.Array core.core_arch.x86.__m512i 8#usize) :
    low.x86_64.sha3_keccak8_f1600.set_rows a i r ⦃ a' =>
      ∀ j < 8, ∀ k < 25, (a'.val[j]!.val[k]!).bv =
        if i.val ≤ k ∧ k < i.val + 8 then lane64x8 (r.val[j]!) (k - i.val) else (a.val[j]!.val[k]!).bv ⦄ := by
  rw [mat_lane r]
  apply WP.spec_mono (set_rows_mat_spec a i hi _)
  intro a' h j hj k hk
  rw [h j hj k hk, ← mat_lane r]

@[step]
theorem extract64x4_spec (k : Std.I32) (v : core.core_arch.x86.__m512i) :
    core.core_arch.x86.avx512f._mm512_extracti64x4_epi64 k v ⦃ r =>
      r = v.extractLsb' (256 * (k.bv.toNat % 2)) 256 ⦄ := by
  simp [core.core_arch.x86.avx512f._mm512_extracti64x4_epi64]

@[step]
theorem extract_epi64_spec (k : Std.I32) (v : core.core_arch.x86.__m256i) :
    core.core_arch.x86_64.avx._mm256_extract_epi64 k v ⦃ r => r.bv = lane64x4 v (k.bv.toNat % 4) ⦄ := by
  simp [core.core_arch.x86_64.avx._mm256_extract_epi64]

theorem length_keccak24 (L : List (BitVec 64)) : (keccak 24 L).length = 25 := by
  show (keccakRound _ (keccak 23 L)).length = 25
  simp only [keccakRound, List.length_cons, List.length_nil]

/-- Eight states whose every lane is that state's permuted lane are the permuted states. -/
theorem states8_ext (r : Std.Array (Std.Array U64 25#usize) 8#usize)
    (a : Std.Array (Std.Array U64 25#usize) 8#usize)
    (h : ∀ j < 8, ∀ k < 25, (r.val[j]!.val[k]!).bv = (keccak 24 (states8 a)[j]!)[k]!) :
    states8 r = (states8 a).map (keccak 24) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  have hj : j < 8 := by simpa using h1
  apply List.ext_getElem (by simp [length_keccak24])
  intro k h3 h4
  have hk : k < 25 := by simpa using h3
  have := h j hj k hk
  rw [states8_getElem! a j hj] at this
  rw [getElem!_pos r.val j (by simp; omega), getElem!_pos _ k (by simp; omega),
    getElem!_pos a.val j (by simp; omega), getElem!_pos _ k (by simp [length_keccak24]; omega)] at this
  simpa using this

/-- Setting lane 24 of row `j` of `A` changes only that lane. -/
theorem get_set_lane (A : Std.Array (Std.Array U64 25#usize) 8#usize) (j : Usize)
    (row : Std.Array U64 25#usize) (hrow : row = A.val[j.val]!) (x : U64) (j' k : Nat)
    (hj' : j' < 8) (hk : k < 25) :
    (A.set j (row.set 24#usize x)).val[j']!.val[k]! =
      if j' = j.val ∧ k = 24 then x else A.val[j']!.val[k]! := by
  rw [Std.Array.set_val_eq, getElem!_set' _ _ _ _ (by simp; omega)]
  by_cases hj : j.val = j'
  · subst hj hrow
    rw [ite_eq_left rfl, Std.Array.set_val_eq, getElem!_set' _ _ _ _ (by simp; omega)]
    by_cases h24 : k = 24
    · simp [h24]
    · rw [ite_eq_right (by simp; omega), ite_eq_right (by omega)]
  · rw [ite_eq_right hj, ite_eq_right (by omega)]

theorem lane_extract (x : BitVec 512) (h n : Nat) (_hh : h < 2) (hn : n < 4) :
    lane64x4 (x.extractLsb' (256 * h) 256) n = lane64x8 x (4 * h + n) := by
  simp only [lane64x4, lane64x8]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, show 64 * n + i < 256 by omega]
  congr 1; omega

theorem hcast_U64_bv (x : I64) : (IScalar.hcast .U64 x).bv = x.bv := by
  rw [IScalar.hcast_bv_eq]; exact BitVec.signExtend_eq x.bv

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `permute_transposing`: Keccak-f on each of the eight states. -/
theorem permute_transposing_spec (a : Std.Array (Std.Array U64 25#usize) 8#usize)
    (rc : Std.Array U64 24#usize) (hrc : rc.val.map (·.bv) = keccakRoundConstants) :
    low.x86_64.sha3_keccak8_f1600.permute_transposing a rc ⦃ r =>
      states8 r = (states8 a).map (keccak 24) ⦄ := by
  unfold low.x86_64.sha3_keccak8_f1600.permute_transposing
  step with rows_spec a 0#usize (by simp) as ⟨a1, ha1⟩
  step with transpose_spec a1 as ⟨b0, hb0⟩
  step with rows_spec a 8#usize (by simp) as ⟨a2, ha2⟩
  step with transpose_spec a2 as ⟨b1, hb1⟩
  step with rows_spec a 16#usize (by simp) as ⟨a3, ha3⟩
  step with transpose_spec a3 as ⟨b2, hb2⟩
  step*
  rw [setr_Q, bind_ok]
  have hv : Array.make 25#usize [mi, mi1, mi2, mi3, mi4, mi5, mi6, mi7, mi8, mi9, mi10, mi11, mi12,
      mi13, mi14, mi15, mi16, mi17, mi18, mi19, mi20, mi21, mi22, mi23,
      Q fun i => [i1.bv, i3.bv, i5.bv, i7.bv, i9.bv, i11.bv, i13.bv, i15.bv][i]!] (by simp) =
      vecs fun i => keccak 0 (lanes a.val[i]!) := by
    have hb0' : ∀ k (hk : k < b0.val.length), ∀ i < 8,
        lane64x8 b0.val[k] i = (a.val[i]!.val[0 + k]!).bv := by
      intro k hk i hi
      have hk' : k < 8 := by simpa using hk
      rw [← getElem!_pos, hb0 k hk' i hi, ha1, lane_mat _ _ _ hi hk']
    have hb1' : ∀ k (hk : k < b1.val.length), ∀ i < 8,
        lane64x8 b1.val[k] i = (a.val[i]!.val[8 + k]!).bv := by
      intro k hk i hi
      have hk' : k < 8 := by simpa using hk
      rw [← getElem!_pos, hb1 k hk' i hi, ha2, lane_mat _ _ _ hi hk']
    have hb2' : ∀ k (hk : k < b2.val.length), ∀ i < 8,
        lane64x8 b2.val[k] i = (a.val[i]!.val[16 + k]!).bv := by
      intro k hk i hi
      have hk' : k < 8 := by simpa using hk
      rw [← getElem!_pos, hb2 k hk' i hi, ha3, lane_mat _ _ _ hi hk']
    apply make_eq_vecs _ (by simp)
    intro k hk i hi
    simp only [keccak, lanes]
    rw [List.getElem!_map_eq _ _ _ (by simp; omega)]
    subst_vars
    interval_cases k <;> simp only [List.getElem!_cons_succ, List.getElem!_cons_zero] <;>
      first
      | exact hb0' _ _ i hi
      | exact hb1' _ _ i hi
      | exact hb2' _ _ i hi
      | (rw [lane_Q _ _ hi]; interval_cases i <;> simp [hcast_I64_bv, getElem!_pos])
  rw [hv]
  unfold low.x86_64.sha3_keccak8_f1600.keccak8_f1600
  have hr := rounds_spec (fun i => lanes a.val[i]!) rc hrc { start := 0#usize, «end» := 24#usize }
    (vecs fun i => keccak 0 (lanes a.val[i]!)) (by decide) (by decide) rfl
  step with hr as ⟨v, hv'⟩
  step*
  have hL : ∀ j < 8, ∀ k (hk : k < v.val.length), lane64x8 v.val[k] j = (keccak 24 (lanes a.val[j]!))[k]! := by
    intro j hj k hk
    have hk' : k < 25 := by simpa using hk
    rw [← getElem!_pos, hv', lane_vecs _ _ _ hk' hj]
  have h12 : ∀ j < 8, ∀ k < 8, lane64x8 (a12.val[j]!) k = (keccak 24 (lanes a.val[j]!))[k]! := by
    intro j hj k hk
    rw [a12_post j hj k hk]
    interval_cases k <;> simp only [Array.make_val, List.getElem!_cons_succ, List.getElem!_cons_zero,
      mi25_post, mi26_post, mi27_post, mi28_post, mi29_post, mi30_post, mi31_post, mi32_post] <;> exact hL j hj _ _
  have h14 : ∀ j < 8, ∀ k < 8, lane64x8 (a14.val[j]!) k = (keccak 24 (lanes a.val[j]!))[8 + k]! := by
    intro j hj k hk
    rw [a14_post j hj k hk]
    interval_cases k <;> simp only [Array.make_val, List.getElem!_cons_succ, List.getElem!_cons_zero,
      mi33_post, mi34_post, mi35_post, mi36_post, mi37_post, mi38_post, mi39_post, mi40_post] <;> exact hL j hj _ _
  have h16 : ∀ j < 8, ∀ k < 8, lane64x8 (a16.val[j]!) k = (keccak 24 (lanes a.val[j]!))[16 + k]! := by
    intro j hj k hk
    rw [a16_post j hj k hk]
    interval_cases k <;> simp only [Array.make_val, List.getElem!_cons_succ, List.getElem!_cons_zero,
      mi41_post, mi42_post, mi43_post, mi44_post, mi45_post, mi46_post, mi47_post, mi48_post] <;> exact hL j hj _ _
  have h17 : ∀ j < 8, ∀ k < 24, (a17.val[j]!.val[k]!).bv = (keccak 24 (lanes a.val[j]!))[k]! := by
    intro j hj k hk
    rw [a17_post j hj k (by omega)]
    by_cases c16 : 16 ≤ k
    · rw [ite_eq_left ⟨c16, by omega⟩, h16 j hj _ (by omega), show 16 + (k - 16) = k by omega]
    rw [ite_eq_right (by omega), a15_post j hj k (by omega)]
    by_cases c8 : 8 ≤ k
    · rw [ite_eq_left ⟨c8, by omega⟩, h14 j hj _ (by omega), show 8 + (k - 8) = k by omega]
    rw [ite_eq_right (by omega), a13_post j hj k (by omega), ite_eq_left ⟨by omega, by omega⟩,
      h12 j hj _ (by omega), Nat.sub_zero]
  have h24 : ∀ j < 8, lane64x8 mi49 j = (keccak 24 (lanes a.val[j]!))[24]! := by
    intro j hj; rw [mi49_post]; exact hL j hj _ _
  apply states8_ext
  intro j hj k hk
  rw [states8_getElem! a j hj]
  rw [index_mut_back7_post, a40_post, get_set_lane _ _ _ (by rw [a39_post, getElem!_pos _ _ (by simp)]; rfl) _ _ _ hj hk]
  rw [index_mut_back6_post, a37_post, get_set_lane _ _ _ (by rw [a36_post, getElem!_pos _ _ (by simp)]; rfl) _ _ _ hj hk]
  rw [index_mut_back5_post, a34_post, get_set_lane _ _ _ (by rw [a33_post, getElem!_pos _ _ (by simp)]; rfl) _ _ _ hj hk]
  rw [index_mut_back4_post, a31_post, get_set_lane _ _ _ (by rw [a30_post, getElem!_pos _ _ (by simp)]; rfl) _ _ _ hj hk]
  rw [index_mut_back3_post, a28_post, get_set_lane _ _ _ (by rw [a27_post, getElem!_pos _ _ (by simp)]; rfl) _ _ _ hj hk]
  rw [index_mut_back2_post, a25_post, get_set_lane _ _ _ (by rw [a24_post, getElem!_pos _ _ (by simp)]; rfl) _ _ _ hj hk]
  rw [index_mut_back1_post, a22_post, get_set_lane _ _ _ (by rw [a21_post, getElem!_pos _ _ (by simp)]; rfl) _ _ _ hj hk]
  rw [index_mut_back_post, a19_post, get_set_lane _ _ _ (by rw [a18_post, getElem!_pos _ _ (by simp)]; rfl) _ _ _ hj hk]
  by_cases hk24 : k = 24
  · subst hk24
    have hl : ∀ h n, h < 2 → n < 4 →
        lane64x8 mi49 (4 * h + n) = (keccak 24 (lanes a.val[4 * h + n]!))[24]! :=
      fun h n hh hn => h24 _ (by omega)
    have hx : ∀ (x : I64) (y : U64) (h n : Nat), h < 2 → n < 4 → y = IScalar.hcast .U64 x →
        x.bv = lane64x4 (mi49.extractLsb' (256 * h) 256) n →
        y.bv = (keccak 24 (lanes a.val[4 * h + n]!))[24]! := by
      intro x y h n hh hn hy hxv
      rw [hy]
      exact (hcast_U64_bv x).trans (by rw [hxv, lane_extract _ _ _ hh hn]; exact hl h n hh hn)
    simp only [and_true, show (0#usize).val = 0 from rfl, show (1#usize).val = 1 from rfl,
      show (2#usize).val = 2 from rfl, show (3#usize).val = 3 from rfl,
        show (4#usize).val = 4 from rfl,
      show (5#usize).val = 5 from rfl, show (6#usize).val = 6 from rfl,
        show (7#usize).val = 7 from rfl]
    interval_cases j <;> simp only [ite_true, ite_false, Nat.reduceEqDiff]
    · exact hx i16 i17 0 0 (by decide) (by decide) i17_post (by rw [i16_post, lo_post]; rfl)
    · exact hx i18 i19 0 1 (by decide) (by decide) i19_post (by rw [i18_post, lo_post]; rfl)
    · exact hx i20 i21 0 2 (by decide) (by decide) i21_post (by rw [i20_post, lo_post]; rfl)
    · exact hx i22 i23 0 3 (by decide) (by decide) i23_post (by rw [i22_post, lo_post]; rfl)
    · exact hx i24 i25 1 0 (by decide) (by decide) i25_post (by rw [i24_post, hi_post]; rfl)
    · exact hx i26 i27 1 1 (by decide) (by decide) i27_post (by rw [i26_post, hi_post]; rfl)
    · exact hx i28 i29 1 2 (by decide) (by decide) i29_post (by rw [i28_post, hi_post]; rfl)
    · exact hx i30 i31 1 3 (by decide) (by decide) i31_post (by rw [i30_post, hi_post]; rfl)
  · simp only [hk24, and_false, ite_false]
    exact h17 j hj k (by omega)

/-- `permute`: Keccak-f on each of the eight states, given FIPS 202's round
constants. -/
theorem permute_spec (a : Std.Array (Std.Array U64 25#usize) 8#usize)
    (rc : Std.Array U64 24#usize) (hrc : rc.val.map (·.bv) = keccakRoundConstants)
    (t : low.x86_64.cpu.HaveAvx512Vl) :
    low.x86_64.sha3_keccak8_f1600.permute a rc t ⦃ r =>
      states8 r = (states8 a).map (keccak 24) ⦄ := by
  unfold low.x86_64.sha3_keccak8_f1600.permute
  exact permute_transposing_spec a rc hrc

end rind.x86_64.keccak8
