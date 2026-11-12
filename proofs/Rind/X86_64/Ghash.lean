import Rind.X86_64.Funs
import Rind.Gf128
import Rind.ValeBytes
open Aeneas Aeneas.Std Result rind.vale rind.simd

namespace rind.x86_64

/-- `u128_to_m128i` keeps `v`'s bits, its halves rejoined. -/
theorem u128_to_m128i_eq (v : Std.U128) : low.x86_64.ghash.u128_to_m128i v = ok v.bv := by
  have h64 : (64#i32).val ≥ 0 := by decide
  have t64 : (64#i32).toNat = 64 := by decide
  simp only [low.x86_64.ghash.u128_to_m128i, HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, h64,
    ite_true, t64, UScalar.shiftRight, lift, UScalar.hcast, core.core_arch.x86.sse2._mm_set_epi64x, bind_ok]
  simp only [UScalarTy.numBits, show 64 < 128 by decide, ite_true, bind_ok, IScalarTy.numBits]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append]
  by_cases h : i < 64
  · simp [h, hi]
  · simp [h, hi, show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega]

theorem poly_carry_mask_bv :
    low.x86_64.ghash.GF128_POLY_CARRY_MASK.bv = 257870231182273679361785313768096399361#128 := by
  unfold low.x86_64.ghash.GF128_POLY_CARRY_MASK; rfl

theorem poly_hi_bv : low.x86_64.ghash.GF128_POLY_HI.bv = 0xc2000000_00000000#128 := by
  unfold low.x86_64.ghash.GF128_POLY_HI; rfl

theorem swap_lanes (x : BitVec 128) :
    ofLanes32 (fun i => lane32 x ((78#i32).bv.toNat / 4 ^ i % 4)) = swap x := by
  have : (78#i32).bv.toNat = 78 := by decide
  simp only [ofLanes32, lane32, swap, lo, hi, this]
  norm_num
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp


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

set_option maxHeartbeats 4000000 in
theorem big_endian_eq (h : BitVec 128) : low.x86_64.ghash.gf128_big_endian h = ok (skBV h) := by
  simp only [low.x86_64.ghash.gf128_big_endian, core.core_arch.x86.sse2._mm_shuffle_epi32,
    core.core_arch.x86.sse2._mm_srai_epi32, core.core_arch.x86.sse2._mm_add_epi64,
    core.core_arch.x86.sse2._mm_and_si128, core.core_arch.x86.sse2._mm_xor_si128,
    u128_to_m128i_eq, poly_carry_mask_bv, bind_ok, add_self_eq]
  congr 1
  have e1 : (I32.bv 211#i32).toNat = 211 := by decide
  have e2 : (I32.bv 31#i32).toNat = 31 := by decide
  simp only [e1, e2, ofLanes32, lane32, lane64, skBV]
  norm_num
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hb : h.getLsbD 127 <;>
    interval_cases i <;>
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_sshiftRight, carry_mask_bit, BitVec.msb_eq_getLsbD_last,
      ] <;>
    simp (config := { decide := true }) [hb, ← BitVec.getLsbD_eq_getElem]


theorem lane64_0 (x : BitVec 128) : lane64 x 0 = lo x := rfl
theorem lane64_1 (x : BitVec 128) : lane64 x 1 = hi x := rfl

theorem xor_zero' {n : Nat} (x : BitVec n) : x ^^^ (0 : BitVec n) = x := BitVec.xor_zero

theorem poly_hi_lo : lo 0xc2000000_00000000#128 = c64 := by decide

theorem mul_eq (a b : BitVec 128) : low.x86_64.ghash._mul a b = ok (mulModel a b) := by
  have e0 : (I32.bv 0#i32).getLsbD 0 = false := by decide
  have e4 : (I32.bv 0#i32).getLsbD 4 = false := by decide
  have f0 : (I32.bv 17#i32).getLsbD 0 = true := by decide
  have f4 : (I32.bv 17#i32).getLsbD 4 = true := by decide
  simp only [low.x86_64.ghash._mul, low.x86_64.ghash.zero, low.x86_64.ghash.xor_halves,
    u128_to_m128i_eq, poly_hi_bv, core.core_arch.x86.sse2._mm_setzero_si128,
    core.core_arch.x86.sse2._mm_shuffle_epi32, core.core_arch.x86.sse2._mm_xor_si128,
    core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128, swap_lanes, bind_ok, e0, e4, f0, f4,
    Bool.false_eq_true, ite_false, ite_true, lane64_0, lane64_1, xor_zero', poly_hi_lo]
  rfl

/-! ## The GHASH key powers, `ClmulTable` and `AvxKernel::new` -/

/-- H to H^8 as `ClmulTable::powers` multiplies them, from the key `h`. -/
def ghashPowers (h : BitVec 128) : List (BitVec 128) :=
  let h1 := skBV h
  let h2 := mulModel h1 h1
  let h3 := mulModel h2 h1
  let h4 := mulModel h2 h2
  [h1, h2, h3, h4, mulModel h4 h1, mulModel h4 h2, mulModel h4 h3, mulModel h4 h4]

theorem powers_eq (h : Std.U128) :
    low.x86_64.ghash.ClmulTable.impl.powers h = ok (Std.Array.make 8#usize (ghashPowers h.bv) (by simp [ghashPowers])) := by
  simp only [low.x86_64.ghash.ClmulTable.impl.powers, u128_to_m128i_eq, big_endian_eq,
    mul_eq, bind_ok, ghashPowers]

/-- `<[T; N]>::map` returns, for a closure that always does. -/
theorem map_ok {T F U : Type} {N : Std.Usize} (inst : core.ops.function.FnMut F T U)
    (hf : ∀ f x, ∃ y, inst.call_mut f x = ok (y, f)) (a : Std.Array T N) (f : F) :
    ∃ r, core.array.Array.map inst a f = ok r := by
  have key : ∀ (l : List T) (acc : List U),
      ∃ r : List U, l.foldlM (fun (p : List U × F) x => do
        let (y, f) ← inst.call_mut p.2 x
        ok (p.1 ++ [y], f)) (acc, f) = ok (r, f) ∧ r.length = acc.length + l.length := by
    intro l
    induction l with
    | nil => intro acc; exact ⟨acc, rfl, by simp⟩
    | cons x l ih =>
      intro acc
      obtain ⟨y, hy⟩ := hf f x
      obtain ⟨r, hr, hl⟩ := ih (acc ++ [y])
      refine ⟨r, ?_, by simp only [List.length_append, List.length_cons, List.length_nil] at hl ⊢; omega⟩
      simp only [List.foldlM_cons, hy, bind_ok]
      simpa using hr
  obtain ⟨r, hr, hl⟩ := key a.val []
  unfold core.array.Array.map
  simp only [hr, bind_ok]
  have hlen : r.length = N.val := by simp only [List.length_nil, zero_add] at hl; rw [hl, Std.Array.property]
  show ∃ r', (if h : r.length = N.val then ok (Std.Array.from r h) else fail .panic) = ok r'
  rw [dite_eq_left hlen]
  exact ⟨_, rfl⟩

theorem clmul_new_eq (h : Std.U128) (hw : low.x86_64.cpu.HaveAesHardware) :
    ∃ px, low.x86_64.ghash.ClmulTable.new h hw =
      ok { powers := Std.Array.make 8#usize (ghashPowers h.bv) (by simp [ghashPowers]), powers_xor := px } := by
  obtain ⟨px, hpx⟩ := map_ok
    low.x86_64.ghash.ClmulTable.with_powers.closure.Insts.CoreOpsFunctionFnMutTuple__m128i__m128i
    (fun f x => ⟨_, by simp only [
      low.x86_64.ghash.ClmulTable.with_powers.closure.Insts.CoreOpsFunctionFnMutTuple__m128i__m128i.call_mut,
      low.x86_64.ghash.xor_halves, core.core_arch.x86.sse2._mm_shuffle_epi32,
      core.core_arch.x86.sse2._mm_xor_si128, bind_ok]; rfl⟩) (Std.Array.make 8#usize (ghashPowers h.bv) (by simp [ghashPowers])) ()
  exact ⟨px, by simp only [low.x86_64.ghash.ClmulTable.new, powers_eq, bind_ok,
    low.x86_64.ghash.ClmulTable.with_powers, hpx]⟩

/-- The GHASH key powers in the layout Vale reads, from the key `h` and its
powers `p`. -/
def valeHkeys (h : BitVec 128) (p : List (BitVec 128)) : List (BitVec 128) :=
  [p[0]!, p[1]!, h, p[2]!, p[3]!, 0, p[4]!, p[5]!]

theorem kernel_new_eq (h : Std.U128) (p : List (BitVec 128)) (hp : p.length = 8)
    (px : Std.Array core.core_arch.x86.__m128i 8#usize) (tok : low.x86_64.cpu.HaveAvxMovbeForAesGcm) :
    low.x86_64.aes_gcm_avx.AvxKernel.new { powers := Std.Array.make 8#usize p hp, powers_xor := px } h tok =
      ok { hkeys := Std.Array.make 8#usize (valeHkeys h.bv p) (by simp [valeHkeys]), token := tok } := by
  unfold low.x86_64.aes_gcm_avx.AvxKernel.new low.x86_64.ghash.ClmulTable.vale_hkeys
  match p, hp with
  | [p0, p1, p2, p3, p4, p5, p6, p7], _ =>
  simp [Std.Array.index_usize, u128_to_m128i_eq, low.x86_64.ghash.zero,
    core.core_arch.x86.sse2._mm_setzero_si128, valeHkeys]

/-- rind's GHASH key powers are those `hkeys_reqs_pub` requires of the key `h`. -/
theorem valeHkeys_spec (h : BitVec 128) : hkeysReqsPub (valeHkeys h (ghashPowers h)) h := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := powers_spec h
  unfold hkeysReqsPub
  rw [reverseBytesQuad32_involutive]
  refine ⟨by simp [valeHkeys], ?_, ?_, rfl, ?_, ?_, rfl, ?_, ?_⟩
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6

end rind.x86_64
