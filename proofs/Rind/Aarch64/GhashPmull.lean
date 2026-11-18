import Rind.Aarch64.Funs
import Rind.GhashSpec
import Rind.RowSelect
open Aeneas Aeneas.Std Result rind.vale rind.simd Polynomial
open core.core_arch.arm_shared.neon.generated core.core_arch.aarch64.neon.generated

/-!
# rind's PMULL GHASH

`Rind.Aarch64.AesGcmModel`'s `Ghash::add` hashes blocks as Vale's
`ghash_LE` does, for the table `PmullTable::new` builds: its `mul!` is the
x86 one's Karatsuba step with the key's halves stored swapped, so the
argument of `Rind.X86_64.GhashClmul` carries over, each step's terms
`Rind.Gf128`'s `karaTerms` and its `reduce!` `reduceModel`.
-/

local notation "P" => Polynomial (ZMod 2)
local notation "V" => core.core_arch.arm_shared.neon.uint64x2_t

set_option maxRecDepth 20000

namespace rind.aarch64.pmull

/-! ## The PMULL steps -/

theorem lane64_0 (x : BitVec 128) : lane64 x 0 = lo x := rfl
theorem lane64_1 (x : BitVec 128) : lane64 x 1 = hi x := rfl

theorem xor_zero' {n : Nat} (x : BitVec n) : x ^^^ (0 : BitVec n) = x := BitVec.xor_zero

/-- `vextq_u64::<1>(x, x)` swaps the halves. -/
theorem ext1_eq (x : V) : vextq_u64 1#i32 x x = ok (swap x) := by
  have : (I32.bv 1#i32).toNat = 1 := by decide
  simp only [vextq_u64, this]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro i hk
  simp only [swap, lo, rind.vale.hi, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', Nat.one_mod, mul_one, hk, decide_true, Bool.true_and]
  by_cases h : i < 64
  · simp [h, Nat.add_comm]
  · simp [h, show ¬ 64 + i < 128 by omega, show i - 64 < 64 by omega, show 64 + i - 128 = i - 64 by omega]

theorem p64_eq (a b : V) : low.aarch64.ghash.vmull_p64_fix a b = ok (clmul (lo a) (lo b)) := by
  simp [low.aarch64.ghash.vmull_p64_fix, vgetq_lane_u64, vmull_p64, lane64_0]

theorem high_p64_eq (a b : V) : low.aarch64.ghash.vmull_high_p64_fix a b = ok (clmul (hi a) (hi b)) := by
  simp [low.aarch64.ghash.vmull_high_p64_fix, vgetq_lane_u64, vmull_p64, lane64_1]

theorem lo_swap (x : BitVec 128) : lo (swap x) = hi x := by simp [swap, lo_append]
theorem hi_swap (x : BitVec 128) : hi (swap x) = lo x := by simp [swap, hi_append]

theorem hi_swap_xor (x : BitVec 128) : hi (swap x ^^^ x) = lo (swap x ^^^ x) := by
  rw [hi_xor, lo_xor, hi_swap, lo_swap, BitVec.xor_comm]

/-- `mul!` adds the Karatsuba terms of `x` times `h`, given `h` swapped and
the lane `mul_m` reads holding `h`'s halves XORed. -/
theorem mulStep_eq (lo' mi hi' x h m : V) (high : Bool)
    (hm : lane64 m (if high then 1 else 0) = lo (swap h ^^^ h)) :
    low.aarch64.ghash.mulStep lo' mi hi' x (swap h) m high =
      ok ((karaTerms x h).1 ^^^ lo', (karaTerms x h).2.1 ^^^ mi, (karaTerms x h).2.2 ^^^ hi') := by
  cases high
  · simp only [Bool.false_eq_true, ite_false, lane64_0] at hm
    simp only [low.aarch64.ghash.mulStep, ext1_eq, high_p64_eq, p64_eq, veorq_u64, bind_ok,
      Bool.false_eq_true, ite_false, hi_swap, lo_swap, karaTerms, hm]
  · simp only [ite_true, lane64_1] at hm
    simp only [low.aarch64.ghash.mulStep, ext1_eq, high_p64_eq, p64_eq, veorq_u64, bind_ok,
      ite_true, hi_swap_xor, hi_swap, lo_swap, karaTerms, hm]

theorem poly_hi_lo : lo 0xc2000000_00000000_c2000000_00000000#128 = c64 := by decide

theorem reduce_eq (lo' mi hi' : V) : low.aarch64.ghash.reduce lo' mi hi' = ok (reduceModel lo' mi hi') := by
  simp only [low.aarch64.ghash.reduce, low.aarch64.ghash.GF128_POLY_HI, ext1_eq, p64_eq, veorq_u64,
    bind_ok, poly_hi_lo, reduceModel]

theorem zero_eq : low.aarch64.ghash.zero = ok 0 := rfl

theorem mul_eq (a b : V) : low.aarch64.ghash._mul a b = ok (mulModel a b) := by
  simp only [low.aarch64.ghash._mul, low.aarch64.ghash.zero, low.aarch64.ghash.xor_halves,
    low.aarch64.ghash.GF128_POLY_HI, ext1_eq, p64_eq, high_p64_eq, veorq_u64, bind_ok, poly_hi_lo,
    xor_zero', hi_swap, lo_swap, mulModel]

theorem add_self_eq {w : Nat} (x : BitVec w) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, pow_one]
  congr 1; omega

theorem carry_mask_bit (k : Nat) : (257870231182273679361785313768096399361#128).getLsbD k =
    (k == 0 || k == 64 || k == 121 || k == 126 || k == 127) := by
  by_cases hk : k < 128
  · interval_cases k <;> decide
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    simp only [eq_comm (a := false), Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    omega

/-- `SSHR` by 31: the sign bit in every bit. -/
theorem sshr31 (x : BitVec 32) : x.sshiftRight 31 = if x.getLsbD 31 then 0xffffffff#32 else 0#32 := by
  by_cases hb : x.getLsbD 31 <;> simp only [hb, ite_true, Bool.false_eq_true, ite_false] <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> interval_cases i <;>
    simp only [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last] <;>
    simp (config := { decide := true }) [hb, ← BitVec.getLsbD_eq_getElem]

/-- The two lanes doubled, as one shift of the whole: lane 0's top bit carries
into lane 1's bottom. -/
theorem shift_halves (h : BitVec 128) :
    (h.extractLsb' 64 64 <<< 1 ++ h.extractLsb' 0 64 <<< 1) =
      (h <<< 1) ^^^ (if h.getLsbD 63 then 0x10000000000000000#128 else 0#128) := by
  by_cases hb : h.getLsbD 63 <;> simp only [hb, ite_true, Bool.false_eq_true, ite_false] <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> interval_cases i <;>
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_extractLsb'] <;>
    simp (config := { decide := true }) [hb, ← BitVec.getLsbD_eq_getElem]

theorem lane32_app0 (a b c d : BitVec 32) : lane32 (a ++ b ++ c ++ d) 0 = d :=
  rind.select.lane32_ofLanes32 (fun i => if i = 0 then d else if i = 1 then c else if i = 2 then b else a)
    (by decide : 0 < 4)
theorem lane32_app1 (a b c d : BitVec 32) : lane32 (a ++ b ++ c ++ d) 1 = c :=
  rind.select.lane32_ofLanes32 (fun i => if i = 0 then d else if i = 1 then c else if i = 2 then b else a)
    (by decide : 1 < 4)
theorem lane32_app2 (a b c d : BitVec 32) : lane32 (a ++ b ++ c ++ d) 2 = b :=
  rind.select.lane32_ofLanes32 (fun i => if i = 0 then d else if i = 1 then c else if i = 2 then b else a)
    (by decide : 2 < 4)
theorem lane32_app3 (a b c d : BitVec 32) : lane32 (a ++ b ++ c ++ d) 3 = a :=
  rind.select.lane32_ofLanes32 (fun i => if i = 0 then d else if i = 1 then c else if i = 2 then b else a)
    (by decide : 3 < 4)

theorem big_endian_eq (h : V) : low.aarch64.ghash.gf128_big_endian h = ok (skBV h) := by
  have e0 : (I32.bv 0#i32).toNat = 0 := by decide
  have e1 : (I32.bv 1#i32).toNat = 1 := by decide
  have e2 : (I32.bv 2#i32).toNat = 2 := by decide
  have e3 : (I32.bv 3#i32).toNat = 3 := by decide
  have e31 : (I32.bv 31#i32).toNat = 31 := by decide
  simp only [low.aarch64.ghash.gf128_big_endian, low.aarch64.ghash.GF128_POLY_CARRY_MASK,
    vreinterpretq_s32_u64, vreinterpretq_u64_s32, vgetq_lane_s32, vsetq_lane_s32, vshrq_n_s32,
    vaddq_u64, vandq_u64, veorq_u64, bind_ok, e0, e1, e2, e3, e31]
  congr 1
  simp only [ofLanes32, lane32_app0, lane32_app1, lane32_app2, lane32_app3, Nat.reduceMod,
    Nat.reduceEqDiff, ite_true, ite_false]
  have bv : ∀ x : BitVec 32, I32.bv (x#iscalar) = x := fun _ => rfl
  have l1 : lane64 h 1 = h.extractLsb' 64 64 := rfl
  have l0 : lane64 h 0 = h.extractLsb' 0 64 := rfl
  have b3 : (lane32 h 3).getLsbD 31 = h.getLsbD 127 := by simp [lane32]
  have b1 : (lane32 h 1).getLsbD 31 = h.getLsbD 63 := by simp [lane32]
  have b0 : (lane32 h 0).getLsbD 31 = h.getLsbD 31 := by simp [lane32]
  simp only [bv, min_self, sshr31, b3, b1, b0, l1, l0, add_self_eq, shift_halves, skBV]
  cases h.getLsbD 127 <;> cases h.getLsbD 63 <;> cases h.getLsbD 31 <;>
    simp only [ite_true, ite_false, Bool.false_eq_true] <;>
    rw [BitVec.xor_assoc] <;> congr 1

/-! ## The table `PmullTable::new` builds -/

/-- `vzip1q_u64(xor_halves(a), xor_halves(b))`: `a`'s halves XORed in the low
lane, `b`'s in the high. -/
def zipm (a b : BitVec 128) : BitVec 128 := lo (swap b ^^^ b) ++ lo (swap a ^^^ a)

/-- `htable` for the key powers `p`, H to H^8: each pair of powers swapped,
their halves XORed zipped between them. -/
def htableOf (p : List (BitVec 128)) : List (BitVec 128) :=
  [swap p[0]!, zipm p[0]! p[1]!, swap p[1]!, swap p[2]!, zipm p[2]! p[3]!, swap p[3]!,
    swap p[4]!, zipm p[4]! p[5]!, swap p[5]!, swap p[6]!, zipm p[6]! p[7]!, swap p[7]!]

/-- A table for the GHASH key `H`: `htableOf` H to H^8, each shifted as
Vale's `shift_key_1` does. -/
def TableFor (H : P) (t : low.aarch64.ghash.PmullTable) : Prop :=
  ∃ p : List (BitVec 128), (∀ i < 8, toPoly p[i]! = shiftKey1 128 gf128ModulusLowTerms (gPower H (i + 1))) ∧
    t.htable.val = htableOf p

theorem xor_halves_eq (h : V) : low.aarch64.ghash.xor_halves h = ok (swap h ^^^ h) := by
  simp [low.aarch64.ghash.xor_halves, ext1_eq, veorq_u64]

/-- The table `PmullTable::new` builds for the key `h`. -/
def pmullTableOf (h : BitVec 128) (o : Option low.aarch64.cpu.HaveSha3) : low.aarch64.ghash.PmullTable where
  htable := Std.Array.make 12#usize (htableOf (ghashPowers h)) (by simp [htableOf])
  eight_way := o

theorem closure_eq (a b : V) :
    low.aarch64.ghash.PmullTable.new.closure.Insts.CoreOpsFunctionFnPairuint64x2_tuint64x2_tuint64x2_t.call
      () (a, b) = ok (zipm a b) := by
  simp [low.aarch64.ghash.PmullTable.new.closure.Insts.CoreOpsFunctionFnPairuint64x2_tuint64x2_tuint64x2_t.call,
    xor_halves_eq, vzip1q_u64, zipm, lane64_0]

theorem pmull_new_spec (h : Std.U128) (tok : low.aarch64.cpu.HaveCryptoExt)
    (o : Option low.aarch64.cpu.HaveSha3) (ho : low.aarch64.cpu.HaveSha3.check = ok o) :
    ∃ t, low.aarch64.ghash.PmullTable.new h tok = ok t ∧ TableFor (toPoly h.bv) t := by
  refine ⟨pmullTableOf h.bv o, ?_, ghashPowers h.bv, ghashPowers_spec h.bv, rfl⟩
  simp only [low.aarch64.ghash.PmullTable.new, low.aarch64.ghash.from_u128, big_endian_eq,
    low.aarch64.ghash.mul, mul_eq, ext1_eq, closure_eq, bind_ok, ho]
  rfl

/-! ## `mul!` against the table -/

theorem mulStep_lo (lo' mi hi' x a b : V) :
    low.aarch64.ghash.mulStep lo' mi hi' x (swap a) (zipm a b) false =
      ok ((karaTerms x a).1 ^^^ lo', (karaTerms x a).2.1 ^^^ mi, (karaTerms x a).2.2 ^^^ hi') :=
  mulStep_eq _ _ _ _ _ _ _ (by simp [zipm, lane64_0, lo_append])

theorem mulStep_hi (lo' mi hi' x a b : V) :
    low.aarch64.ghash.mulStep lo' mi hi' x (swap b) (zipm a b) true =
      ok ((karaTerms x b).1 ^^^ lo', (karaTerms x b).2.1 ^^^ mi, (karaTerms x b).2.2 ^^^ hi') :=
  mulStep_eq _ _ _ _ _ _ _ (by simp [zipm, lane64_1, hi_append])

/-- The powers H^n down to H. -/
def powersDesc (p : List (BitVec 128)) (n : Nat) : List (BitVec 128) :=
  (List.range n).reverse.map fun i => p[i]!

theorem powersDesc_succ (p : List (BitVec 128)) (n : Nat) :
    powersDesc p (n + 1) = p[n]! :: powersDesc p n := by
  simp [powersDesc, List.range_succ]

theorem sum_powersDesc (H : P) (hH : Small H) (p : List (BitVec 128))
    (hp : ∀ i < 8, toPoly p[i]! = shiftKey1 128 gf128ModulusLowTerms (gPower H (i + 1))) :
    ∀ xs : List (BitVec 128), xs.length ≤ 8 →
      ((xs.zip (powersDesc p xs.length)).map fun q => toPoly (mulModel q.1 q.2)).sum =
        sumPow H (xs.map toPoly)
  | [], _ => by simp [powersDesc, sumPow_nil]
  | x :: xs, hl => by
    rw [List.length_cons, powersDesc_succ, List.zip_cons_cons, List.map_cons, List.sum_cons,
      sum_powersDesc H hH p hp xs (by simp at hl; omega), List.map_cons, sumPow_cons, List.length_map,
      mul_data _ _ _ (small_gPower H hH _) (hp xs.length (by simp at hl; omega))]

theorem toPoly_reduceAll_powers (H : P) (hH : Small H) (p : List (BitVec 128))
    (hp : ∀ i < 8, toPoly p[i]! = shiftKey1 128 gf128ModulusLowTerms (gPower H (i + 1)))
    (xs : List (BitVec 128)) (hl : xs.length ≤ 8) :
    toPoly (reduceAll (xs.zip (powersDesc p xs.length))) = sumPow H (xs.map toPoly) := by
  rw [toPoly_reduceAll, sum_powersDesc H hH p hp xs hl]

theorem mul8_eq (t : low.aarch64.ghash.PmullTable) (p : List (BitVec 128)) (ht : t.htable.val = htableOf p)
    (x1 x2 x3 x4 x5 x6 x7 x8 : BitVec 128) :
    low.aarch64.ghash._mul8 t x1 x2 x3 x4 x5 x6 x7 x8 =
      ok (reduceAll ([x1, x2, x3, x4, x5, x6, x7, x8].zip (powersDesc p 8))) := by
  simp only [low.aarch64.ghash._mul8, zero_eq, bind_ok, ht, htableOf, List.getElem!_cons_succ,
    List.getElem!_cons_zero, mulStep_lo, mulStep_hi, reduce_eq, reduceAll, accum, powersDesc,
    List.range_succ, List.range_zero, List.nil_append, List.reverse_cons, List.reverse_nil, List.map_cons,
    List.map_nil, List.cons_append, List.zip_cons_cons, List.zip_nil_right]
  rfl

theorem mul_h_eq (t : low.aarch64.ghash.PmullTable) (p : List (BitVec 128)) (ht : t.htable.val = htableOf p)
    (x : BitVec 128) :
    low.aarch64.ghash._mul_h t x = ok (reduceAll ([x].zip (powersDesc p 1))) := by
  simp only [low.aarch64.ghash._mul_h, zero_eq, bind_ok, ht, htableOf, List.getElem!_cons_succ,
    List.getElem!_cons_zero, mulStep_lo, reduce_eq, reduceAll, accum, powersDesc, List.range_one,
    List.reverse_singleton, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left]
  rfl

theorem toPoly_mul_h (H : P) (hH : Small H) (p : List (BitVec 128))
    (hp : ∀ i < 8, toPoly p[i]! = shiftKey1 128 gf128ModulusLowTerms (gPower H (i + 1))) (x : BitVec 128) :
    toPoly (reduceAll ([x].zip (powersDesc p 1))) = gf128MulRev (toPoly x) H := by
  have h1 := toPoly_reduceAll_powers H hH p hp [x] (by simp)
  rw [List.length_singleton] at h1
  rw [h1, List.map_cons, List.map_nil, sumPow_cons, sumPow_nil, List.length_nil, gPower_one, add_zero]

/-! ## `Ghash::add` -/

theorem fromBeBytes_eq (b : List U8) :
    low.aarch64.ghash.from_u128 (low.aarch64.ghash.fromBeBytes b) = ok (blockBE b) := rfl

/-- `one_block` is one step of GHASH. -/
theorem one_block_spec (H : P) (hH : Small H) (t : low.aarch64.ghash.PmullTable) (ht : TableFor H t)
    (c : V) (b : List U8) :
    ∃ y, low.aarch64.ghash.one_block t c (low.aarch64.ghash.fromBeBytes b) = ok y ∧
      toPoly y = ghashPoly H (toPoly c) [toPoly (blockBE b)] := by
  obtain ⟨p, hp, hv⟩ := ht
  refine ⟨reduceAll ([c ^^^ blockBE b].zip (powersDesc p 1)), by
    simp only [low.aarch64.ghash.one_block, fromBeBytes_eq, veorq_u64, bind_ok, mul_h_eq t p hv], ?_⟩
  rw [toPoly_mul_h H hH p hp, ghashPoly_cons, ghashPoly_nil, toPoly_xor]

/-- `eight_blocks` hashes a 128-byte chunk's eight blocks. -/
theorem eight_blocks_spec (H : P) (hH : Small H) (t : low.aarch64.ghash.PmullTable) (ht : TableFor H t)
    (c : V) (chunk : List U8) (hc : chunk.length = 128) :
    ∃ y, low.aarch64.ghash.eight_blocks t c chunk = ok y ∧
      toPoly y = ghashPoly H (toPoly c) ((padBlocks chunk).map toPoly) := by
  obtain ⟨p, hp, hv⟩ := ht
  have hpad : padBlocks chunk = tailInputs 0 ((List.range 8).map fun i => blockBE ((chunk.drop (16 * i)).take 16)) := by
    rw [padBlocks_128 chunk hc, tailInputs_zero, chunksOf, hc, List.map_map]; rfl
  refine ⟨reduceAll ((tailInputs c ((List.range 8).map fun i => blockBE ((chunk.drop (16 * i)).take 16))).zip
    (powersDesc p 8)), by
    simp only [low.aarch64.ghash.eight_blocks, fromBeBytes_eq, veorq_u64, bind_ok, mul8_eq t p hv]; rfl, ?_⟩
  have hl : (tailInputs c ((List.range 8).map fun i => blockBE ((chunk.drop (16 * i)).take 16))).length = 8 := by
    simp [length_tailInputs]
  have h := toPoly_reduceAll_powers H hH p hp _ (by rw [hl])
  rw [hl] at h
  have hne : ((List.range 8).map fun i => blockBE ((chunk.drop (16 * i)).take 16)) ≠ [] := by simp
  rw [h, sumPow_tailInputs H c _ hne, hpad, tailInputs_zero]

theorem add_loop_spec (H : P) (hH : Small H) (t : low.aarch64.ghash.PmullTable) (ht : TableFor H t) :
    ∀ (chunks : List (List U8)) (x : V), (∀ c ∈ chunks, c.length = 128) →
      ∃ y, chunks.foldlM (low.aarch64.ghash.eight_blocks t) x = ok y ∧
        toPoly y = ghashPoly H (toPoly x) ((chunks.flatMap padBlocks).map toPoly)
  | [], x, _ => ⟨x, rfl, by simp [ghashPoly_nil]⟩
  | c :: chunks, x, hc => by
    obtain ⟨y, hy, hyp⟩ := eight_blocks_spec H hH t ht x c (hc c (by simp))
    obtain ⟨z, hz, hzp⟩ := add_loop_spec H hH t ht chunks y (fun c h => hc c (by simp [h]))
    exact ⟨z, by rw [List.foldlM_cons, hy]; simpa using hz,
      by rw [hzp, hyp, List.flatMap_cons, List.map_append, ghashPoly_append]⟩

theorem add_blocks_spec (H : P) (hH : Small H) (t : low.aarch64.ghash.PmullTable) (ht : TableFor H t) :
    ∀ (chunks : List (List U8)) (x : V),
      ∃ y, chunks.foldlM (fun c chunk => low.aarch64.ghash.one_block t c (low.aarch64.ghash.fromBeBytes chunk)) x
          = ok y ∧
        toPoly y = ghashPoly H (toPoly x) ((chunks.map blockBE).map toPoly)
  | [], x => ⟨x, rfl, by simp [ghashPoly_nil]⟩
  | c :: chunks, x => by
    obtain ⟨y, hy, hyp⟩ := one_block_spec H hH t ht x c
    obtain ⟨z, hz, hzp⟩ := add_blocks_spec H hH t ht chunks y
    exact ⟨z, by rw [List.foldlM_cons, hy]; simpa using hz,
      by rw [hzp, hyp, List.map_cons, List.map_cons, ← ghashPoly_append, List.singleton_append]⟩

/-- `Ghash::add` on a PMULL table hashes the padded blocks of the bytes from
the state `x`, for a table of `H`'s powers. -/
theorem addPmull_spec (H : P) (hH : Small H) (t : low.aarch64.ghash.PmullTable) (ht : TableFor H t)
    (x : V) (bytes : List U8) :
    ∃ y, low.aarch64.ghash.Ghash.addPmull t x bytes = ok y ∧
      toPoly y = ghashPoly H (toPoly x) ((padBlocks bytes).map toPoly) := by
  obtain ⟨y, hy, hyp⟩ := add_loop_spec H hH t ht (chunksOf 128 bytes) x (fun c h => chunksOf_length_mem h)
  obtain ⟨z, hz, hzp⟩ := add_blocks_spec H hH t ht (chunksOf 16 (chunksRest 128 bytes)) y
  rw [padBlocks_split bytes, List.map_append, ghashPoly_append, ← hyp]
  simp only [low.aarch64.ghash.Ghash.addPmull, hy, hz, bind_ok]
  by_cases hr : chunksRest 16 (chunksRest 128 bytes) = []
  · refine ⟨z, by simp [hr], ?_⟩
    rw [hzp, padBlocks, hr]; simp
  · obtain ⟨w, hw, hwp⟩ := one_block_spec H hH t ht z
      (chunksRest 16 (chunksRest 128 bytes) ++
        List.replicate (16 - (chunksRest 16 (chunksRest 128 bytes)).length) 0#u8)
    refine ⟨w, by simp [hr, hw], ?_⟩
    rw [hwp, hzp, padBlocks, if_neg hr, List.map_append, ghashPoly_append]
    rfl

/-- `Ghash::add` on a PMULL table of `H`'s powers hashes the padded blocks of
the bytes from the state `x`. -/
theorem ghash_add_spec (H : P) (hH : Small H) (t : low.aarch64.ghash.PmullTable) (ht : TableFor H t)
    (x : V) (bytes : Slice U8) :
    ∃ y, low.aarch64.ghash.Ghash.add ⟨.Pmull t, x⟩ bytes = ok ⟨.Pmull t, y⟩ ∧
      toPoly y = ghashPoly H (toPoly x) ((padBlocks bytes.val).map toPoly) := by
  obtain ⟨y, hy, hyp⟩ := addPmull_spec H hH t ht x bytes.val
  exact ⟨y, by simp [low.aarch64.ghash.Ghash.add, hy], hyp⟩

/-- `GhashTable::new` on a CPU with the crypto extension builds a PMULL table
of the key's powers. -/
theorem ghash_table_new_spec (h : Std.U128) (tok : low.aarch64.cpu.HaveCryptoExt)
    (htok : low.aarch64.cpu.HaveCryptoExt.check = ok (some tok))
    (o : Option low.aarch64.cpu.HaveSha3) (ho : low.aarch64.cpu.HaveSha3.check = ok o) :
    ∃ t, low.aarch64.ghash.GhashTable.new h = ok (.Pmull t) ∧ TableFor (toPoly h.bv) t := by
  obtain ⟨t, ht, hf⟩ := pmull_new_spec h tok o ho
  exact ⟨t, by simp [low.aarch64.ghash.GhashTable.new, htok, ht], hf⟩

end rind.aarch64.pmull

