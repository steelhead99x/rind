import Rind.X86_64.PointSelect
import Rind.X86_64.S2nBignum
import Rind.RsaLemmas
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# RSA's table gather on x86_64, proven

`mont_exp`'s `gather` copies power `i` of the 32 rows it tabulates, `w` words
each: by `Rind.X86_64.GatherModel`'s model of its AVX2 gather, which
`gather_avx2_spec` proves, or by s2n-bignum's `bignum_copy_row_from_table`,
whichever `HaveAvx2::check` picks.
-/

namespace rind.x86_64

open rind.simd rind.select

/-! ## Lanes -/

theorem lane64x4_ofLanes64x4 (f : Nat → BitVec 64) {i : Nat} (hi : i < 4) :
    lane64x4 (ofLanes64x4 f) i = f i := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    simp only [lane64x4, ofLanes64x4] <;>
    (repeat (rw [BitVec.extractLsb'_append_eq_of_le (by omega)])) <;>
    first | exact BitVec.extractLsb'_append_eq_right | exact BitVec.extractLsb'_eq_self

theorem ofLanes64x4_congr {f g : Nat → BitVec 64} (h : ∀ i < 4, f i = g i) :
    ofLanes64x4 f = ofLanes64x4 g := by
  simp only [ofLanes64x4, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem ofLanes64x4_allOnes : ofLanes64x4 (fun _ => BitVec.allOnes 64) = BitVec.allOnes 256 := by
  decide

theorem ofLanes64x4_zero : ofLanes64x4 (fun _ => 0#64) = 0#256 := by
  decide

/-- `_mm256_cmpeq_epi64` of two broadcasts. -/
theorem mm256_cmpeq64_bcast (a b : BitVec 64) :
    core.core_arch.x86.avx2._mm256_cmpeq_epi64 (ofLanes64x4 fun _ => a) (ofLanes64x4 fun _ => b) =
      ok (if a = b then BitVec.allOnes 256 else 0) := by
  unfold core.core_arch.x86.avx2._mm256_cmpeq_epi64
  rw [ofLanes64x4_congr (g := fun _ => if a = b then BitVec.allOnes 64 else 0)
    (fun i hi => by rw [lane64x4_ofLanes64x4 _ hi, lane64x4_ofLanes64x4 _ hi])]
  split
  · exact congrArg ok ofLanes64x4_allOnes
  · exact congrArg ok ofLanes64x4_zero

/-- `_mm256_add_epi64` of two broadcasts. -/
theorem mm256_add64_bcast (a b : BitVec 64) :
    core.core_arch.x86.avx2._mm256_add_epi64 (ofLanes64x4 fun _ => a) (ofLanes64x4 fun _ => b) =
      ok (ofLanes64x4 fun _ => a + b) := by
  unfold core.core_arch.x86.avx2._mm256_add_epi64
  rw [ofLanes64x4_congr (g := fun _ => a + b)
    (fun i hi => by rw [lane64x4_ofLanes64x4 _ hi, lane64x4_ofLanes64x4 _ hi])]

/-- The counter after `r` rows matches `i` exactly at row `i`. -/
theorem counter64_eq (r : Nat) (i : U64) (hr : r < 2 ^ 64) :
    BitVec.ofNat 64 r = i.bv ↔ r = i.val := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  exact Iff.rfl

theorem counter64_succ (r : Nat) : BitVec.ofNat 64 r + 1#64 = BitVec.ofNat 64 (r + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem i64_mk_bv (x : BitVec 64) : (⟨x⟩ : Std.I64).bv = x := rfl

theorem one_i64_bv : (1#i64 : Std.I64).bv = 1#64 := rfl

/-! ## `gather_columns` -/

/-- The four words of `l` from `l[b + k]` are those of `l.drop b` from `k`. -/
theorem load256_drop (l : List U64) (b k : Nat) : load256 l (b + k) = load256 (l.drop b) k := by
  simp only [load256, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_assoc]

section
variable (V w col : Nat) (powers : List U64) (i : U64)

/-- `gather_columns`'s state after `r` rows: the counter, and each
accumulator's words from row `i`, once the loop has passed it. -/
def gatherAfter (r : Nat) : core.core_arch.x86.__m256i × List core.core_arch.x86.__m256i :=
  (ofLanes64x4 fun _ => BitVec.ofNat 64 r,
    (List.range V).map fun j => if i.val < r then load256 powers (i.val * w + col + 4 * j) else 0)

theorem gather_row_step (r : Nat) (hr : r + 1 < 2 ^ 64) :
    low.x86_64.mont_exp.gather_row V w col powers (ofLanes64x4 fun _ => i.bv)
      (ofLanes64x4 fun _ => 1#64) (gatherAfter V w col powers i r) r =
      ok (gatherAfter V w col powers i (r + 1)) := by
  simp only [low.x86_64.mont_exp.gather_row, gatherAfter, mm256_cmpeq64_bcast, mm256_add64_bcast,
    core.core_arch.x86.avx2._mm256_and_si256, core.core_arch.x86.avx2._mm256_or_si256, bind_ok,
    and_mask, counter64_eq r i (by omega), counter64_succ, mapM_ok]
  refine congrArg ok (Prod.ext rfl ?_)
  apply List.map_congr_left
  intro j hj
  rw [getD_map_range _ _ (List.mem_range.mp hj)]
  by_cases h : r = i.val
  · subst h
    simp
  · have h' : i.val < r + 1 ↔ i.val < r := by omega
    simp [h, h']

theorem gather_loop : ∀ k, k < 2 ^ 64 →
    (List.range k).foldlM (low.x86_64.mont_exp.gather_row V w col powers (ofLanes64x4 fun _ => i.bv)
      (ofLanes64x4 fun _ => 1#64)) (gatherAfter V w col powers i 0) =
      ok (gatherAfter V w col powers i k)
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [List.range_succ, List.foldlM_append, gather_loop k (by omega), bind_tc_ok,
      List.foldlM_cons, gather_row_step V w col powers i k hk, List.foldlM_nil, pure_tc_eq]

theorem gatherAfter_zero :
    gatherAfter V w col powers i 0 = (0, List.replicate V 0) := by
  simp only [gatherAfter, Nat.not_lt_zero, ite_false, List.map_const', List.length_range]
  exact Prod.ext ofLanes64x4_zero rfl

end

/-- `gather_columns::<V>` copies the `4V` words of row `i` of the 32 rows of
`w` words from column `col`. -/
theorem gather_columns_eq (V : Nat) (z powers : List U64) (col : Nat) (i : U64) (w : Nat)
    (hw : powers.length = 32 * w) (hz : z.length = 4 * V) (hcol : col + 4 * V ≤ w)
    (hi : i.val < 32) :
    low.x86_64.mont_exp.gather_columns V z powers col i =
      ok ((powers.drop (i.val * w + col)).take (4 * V)) := by
  have hw' : powers.length / 32 = w := by omega
  have hloop := gather_loop V w col powers i 32 (by norm_num)
  rw [gatherAfter_zero] at hloop
  have hst : (ofLanes64x4 fun _ => (⟨i.bv⟩ : Std.I64).bv) = ofLanes64x4 fun _ => i.bv := rfl
  have hone : (ofLanes64x4 fun _ => (1#i64 : Std.I64).bv) = ofLanes64x4 fun _ => 1#64 := rfl
  unfold low.x86_64.mont_exp.gather_columns
  rw [hw', ite_eq_left ⟨hz, hcol⟩]
  simp only [core.core_arch.x86.avx._mm256_setzero_si256, core.core_arch.x86.avx._mm256_set1_epi64x,
    bind_ok]
  rw [hst, hone, hloop, bind_ok]
  simp only [gatherAfter, hi, ite_true, List.flatMap_map]
  have hl : 4 * V ≤ (powers.drop (i.val * w + col)).length := by
    rw [List.length_drop]
    have : i.val * w ≤ 31 * w := Nat.mul_le_mul_right _ (by omega)
    omega
  rw [← flatMap_store256 _ V hl]
  simp only [load256_drop]

/-! ## `gather_avx2` -/

theorem mapM_eq_ok {α β : Type} (f : α → Result β) (g : α → β) :
    ∀ (l : List α), (∀ a ∈ l, f a = ok (g a)) → l.mapM f = ok (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons, h a List.mem_cons_self,
      mapM_eq_ok f g l (fun b hb => h b (List.mem_cons_of_mem a hb)), bind_tc_ok, pure_tc_eq,
      List.map_cons]

theorem gather_vectors_eq (len : Nat) (h : len = 4 ∨ len = 8 ∨ len = 12 ∨ len = 16) :
    4 * low.x86_64.mont_exp.gather_vectors len = len := by
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- Blocks of `c` elements from `l`, `n` of them, joined: the first `c·n`
elements. -/
theorem flatten_blocks {α : Type} (l : List α) (c : Nat) : ∀ n,
    ((List.range n).map fun b => (l.drop (c * b)).take c).flatten = l.take (c * n)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, flatten_blocks l c n]
    simp [Nat.mul_succ, List.take_add]

/-- `gather_avx2` copies row `i` of the 32 rows of `powers`, each as long as
`z`, a multiple of four words. -/
theorem gather_avx2_spec (z powers : Slice U64) (i : U64) (t : low.x86_64.cpu.HaveAvx2)
    (hw4 : z.length % 4 = 0) (hp : powers.length = 32 * z.length) (hi : i.val < 32) :
    low.x86_64.mont_exp.gather_avx2 z powers i t ⦃ r =>
      r.val = (powers.val.drop (i.val * z.length)).take z.length ⦄ := by
  unfold low.x86_64.mont_exp.gather_avx2
  rw [ite_eq_left ⟨hw4, hp⟩]
  have hp' : powers.val.length = 32 * z.length := hp
  have hiw : i.val * z.length ≤ 31 * z.length := Nat.mul_le_mul_right _ (by omega)
  -- Each block of up to 16 words copies those words of row `i`.
  have hblock : ∀ b ∈ List.range ((z.length + 15) / 16),
      low.x86_64.mont_exp.gather_columns
        (low.x86_64.mont_exp.gather_vectors ((z.val.drop (16 * b)).take 16).length)
        ((z.val.drop (16 * b)).take 16) powers.val (16 * b) i =
      ok ((((powers.val.drop (i.val * z.length)).take z.length).drop (16 * b)).take 16) := by
    intro b hb
    have hb' := List.mem_range.mp hb
    have hlen : ((z.val.drop (16 * b)).take 16).length = min 16 (z.length - 16 * b) := by
      simp [Nat.min_comm]
    have hV := gather_vectors_eq ((z.val.drop (16 * b)).take 16).length (by rw [hlen]; omega)
    rw [gather_columns_eq _ _ _ _ _ z.length hp' hV.symm (by rw [hV, hlen]; omega) hi, hV, hlen,
      List.drop_take, List.take_take, List.drop_drop]
  have hrow : ((powers.val.drop (i.val * z.length)).take z.length).length = z.length := by
    simp only [List.length_take, List.length_drop]; omega
  have hflat : ((List.range ((z.length + 15) / 16)).map fun b =>
      (((powers.val.drop (i.val * z.length)).take z.length).drop (16 * b)).take 16).flatten =
      (powers.val.drop (i.val * z.length)).take z.length := by
    rw [flatten_blocks, List.take_of_length_le (by rw [hrow]; omega)]
  rw [mapM_eq_ok _ _ _ hblock, bind_ok]
  simp only [hflat, hrow, _root_.dite_true, WP.spec_ok, Slice.from_val]

/-! ## `gather` -/

/-- `gather` copies row `i` of the 32 rows of `powers`, each as long as `z`,
a multiple of four words, whichever path `HaveAvx2::check` picks. -/
theorem gather_spec (havx : ∃ t, low.x86_64.cpu.HaveAvx2.check = ok t) (z powers : Slice U64)
    (i : U64) (hw4 : z.length % 4 = 0) (hp : powers.length = 32 * z.length) (hi : i.val < 32)
    (hw : z.length < 2 ^ 60) :
    low.x86_64.mont_exp.gather z powers i ⦃ r =>
      r.val = (powers.val.drop (i.val * z.length)).take z.length ⦄ := by
  obtain ⟨t, ht⟩ := havx
  unfold low.x86_64.mont_exp.gather
  simp only [ht, bind_ok]
  cases t with
  | some token => exact gather_avx2_spec z powers i token hw4 hp hi
  | none =>
    dsimp only
    step*
    have hrow : ((powers.val.drop (i.val * z.length)).take z.length).length = z.length := by
      have : i.val * z.length ≤ 31 * z.length := Nat.mul_le_mul_right _ (by omega)
      simp only [List.length_take, List.length_drop]
      have hp' : powers.val.length = 32 * z.length := hp
      omega
    have hi2 : i2.val = z.length := by
      simp only [i2_post, UScalar.cast_val_eq, Slice.len_val, UScalarTy.numBits] <;> omega
    rw [hi2] at r_post1
    exact wordsNat_inj _ _ (by rw [hrow]; exact r_post) r_post1

end rind.x86_64
