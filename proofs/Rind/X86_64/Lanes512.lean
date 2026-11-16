import Rind.X86_64.GhashClmul
open Aeneas Aeneas.Std Result rind.vale rind.simd Polynomial

/-!
# rind's AVX-512 intrinsics, lane by lane

A 512-bit vector as `ofLanes128` of four 128-bit lanes: each AVX-512, VAES,
and VPCLMULQDQ intrinsic that `Rind.X86_64.AesGcmModel`'s by-16 AES-GCM calls
acts on each lane as its 128-bit form does, so `Rind.X86_64.GhashAvx512` and
`Rind.X86_64.AesGcmAvx512` reason one lane at a time.
-/

local notation "P" => Polynomial (ZMod 2)

set_option maxRecDepth 20000

namespace rind.x86_64

/-! ## 512-bit lanes

Each 512-bit intrinsic of `ofLanes128` vectors is `ofLanes128` of its 128-bit
form on their lanes. -/

theorem lane128_ofLanes128 (f : Nat → BitVec 128) (j : Nat) (hj : j < 4) : lane128 (ofLanes128 f) j = f j := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [lane128, ofLanes128, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp [hk, show ¬ 128 + k < 128 by omega, show ¬ 256 + k < 128 by omega, show ¬ 256 + k - 128 < 128 by omega,
      show ¬ 384 + k < 128 by omega, show ¬ 384 + k - 128 < 128 by omega, show ¬ 384 + k - 128 - 128 < 128 by omega,
      show 256 + k - 128 - 128 = k by omega, show 384 + k - 128 - 128 - 128 = k by omega,
      show 128 + k - 128 = k by omega]

/-- The four lanes, as `ofLanes128` unfolds. -/
theorem ternary_xor {w : Nat} (a b c : BitVec w) : ternary 150#8 a b c = a ^^^ b ^^^ c := by
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

theorem getLsbD_ofLanes128 (f : Nat → BitVec 128) (k : Nat) :
    (ofLanes128 f).getLsbD k = (decide (k < 512) && (f (k / 128)).getLsbD (k % 128)) := by
  simp only [ofLanes128, BitVec.getLsbD_append]
  by_cases h0 : k < 128
  · simp [h0, show k < 512 by omega, Nat.div_eq_of_lt h0, Nat.mod_eq_of_lt h0]
  by_cases h1 : k - 128 < 128
  · simp [h0, h1, show k < 512 by omega, show k / 128 = 1 by omega, show k % 128 = k - 128 by omega]
  by_cases h2 : k - 128 - 128 < 128
  · simp [h0, h1, h2, show k < 512 by omega, show k / 128 = 2 by omega, show k % 128 = k - 128 - 128 by omega]
  by_cases h3 : k < 512
  · simp [h0, h1, h2, h3, show k / 128 = 3 by omega, show k % 128 = k - 128 - 128 - 128 by omega]
  · simp [h0, h1, h2, h3]
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem xor_ofLanes128 (f g : Nat → BitVec 128) :
    ofLanes128 f ^^^ ofLanes128 g = ofLanes128 fun j => f j ^^^ g j := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_xor, getLsbD_ofLanes128, hk, decide_true, Bool.true_and]


theorem ofLanes128_ext (f g : Nat → BitVec 128) (h : ∀ j < 4, f j = g j) : ofLanes128 f = ofLanes128 g := by
  simp only [ofLanes128, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

/-- `PSHUFB`'s bytes, as `_mm_shuffle_epi8` computes them. -/
def pshufb (a b : BitVec 128) : BitVec 128 :=
  ofBytes fun i => if (byte b i).msb then 0 else byte a ((byte b i).toNat % 16)

theorem shuffle_epi8_eq (a b : BitVec 128) : core.core_arch.x86.ssse3._mm_shuffle_epi8 a b = ok (pshufb a b) := rfl

/-- `PADDD`'s lanes, as `_mm_add_epi32` computes them. -/
def paddd (a b : BitVec 128) : BitVec 128 := ofLanes32 fun i => lane32 a i + lane32 b i

theorem add_epi32_eq (a b : BitVec 128) : core.core_arch.x86.sse2._mm_add_epi32 a b = ok (paddd a b) := rfl

section lanes
variable (f g h : Nat → BitVec 128)

theorem xor512_eq : core.core_arch.x86.avx512f._mm512_xor_epi32 (ofLanes128 f) (ofLanes128 g) =
    ok (ofLanes128 fun j => f j ^^^ g j) := by
  rw [core.core_arch.x86.avx512f._mm512_xor_epi32, xor_ofLanes128]

theorem xor512q_eq : core.core_arch.x86.avx512f._mm512_xor_epi64 (ofLanes128 f) (ofLanes128 g) =
    ok (ofLanes128 fun j => f j ^^^ g j) := by
  rw [core.core_arch.x86.avx512f._mm512_xor_epi64, xor_ofLanes128]

theorem zero_ofLanes128 : (0 : BitVec 512) = ofLanes128 fun _ => 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have hz : ∀ n i, (0 : BitVec n).getLsbD i = false := fun _ _ => BitVec.getLsbD_zero
  simp only [getLsbD_ofLanes128, hz, Bool.and_false]

theorem setzero512_eq : core.core_arch.x86.avx512f._mm512_setzero_si512 = ok (ofLanes128 fun _ => 0) := by
  rw [core.core_arch.x86.avx512f._mm512_setzero_si512, zero_ofLanes128]

theorem insert512_eq (IMM8 : Std.I32) (b : BitVec 128) :
    core.core_arch.x86.avx512f._mm512_inserti32x4 IMM8 (ofLanes128 f) b =
      ok (ofLanes128 fun j => if j = IMM8.bv.toNat % 4 then b else f j) := by
  simp only [core.core_arch.x86.avx512f._mm512_inserti32x4]
  exact congrArg ok (ofLanes128_ext _ _ fun j hj => by rw [lane128_ofLanes128 f j hj])

theorem extract512_eq (IMM8 : Std.I32) :
    core.core_arch.x86.avx512f._mm512_extracti32x4_epi32 IMM8 (ofLanes128 f) = ok (f (IMM8.bv.toNat % 4)) := by
  simp only [core.core_arch.x86.avx512f._mm512_extracti32x4_epi32, lane128_ofLanes128 f _ (Nat.mod_lt _ (by omega))]

theorem shuffle512_eq : core.core_arch.x86.avx512f._mm512_shuffle_epi32 78#i32 (ofLanes128 f) =
    ok (ofLanes128 fun j => swap (f j)) := by
  simp only [core.core_arch.x86.avx512f._mm512_shuffle_epi32]
  exact congrArg ok (ofLanes128_ext _ _ fun j hj => by rw [lane128_ofLanes128 f j hj, swap_lanes])

theorem ternary512_eq : core.core_arch.x86.avx512f._mm512_ternarylogic_epi32 low.x86_64.ghash.ternaryXor
    (ofLanes128 f) (ofLanes128 g) (ofLanes128 h) = ok (ofLanes128 fun j => f j ^^^ g j ^^^ h j) := by
  simp only [core.core_arch.x86.avx512f._mm512_ternarylogic_epi32, low.x86_64.ghash.ternaryXor,
    show (150#i32).bv.setWidth 8 = 150#8 by decide, ternary_xor, xor_ofLanes128]

theorem ternary512q_eq : core.core_arch.x86.avx512f._mm512_ternarylogic_epi64 low.x86_64.ghash.ternaryXor
    (ofLanes128 f) (ofLanes128 g) (ofLanes128 h) = ok (ofLanes128 fun j => f j ^^^ g j ^^^ h j) := by
  simp only [core.core_arch.x86.avx512f._mm512_ternarylogic_epi64, low.x86_64.ghash.ternaryXor,
    show (150#i32).bv.setWidth 8 = 150#8 by decide, ternary_xor, xor_ofLanes128]

theorem clmul512_eq (IMM8 : Std.I32) :
    core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 IMM8 (ofLanes128 f) (ofLanes128 g) =
      ok (ofLanes128 fun j => clmul (lane64 (f j) (if IMM8.bv.getLsbD 0 then 1 else 0))
        (lane64 (g j) (if IMM8.bv.getLsbD 4 then 1 else 0))) := by
  simp only [core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128]
  exact congrArg ok (ofLanes128_ext _ _ fun j hj => by rw [lane128_ofLanes128 f j hj, lane128_ofLanes128 g j hj])

theorem pshufb512_eq : core.core_arch.x86.avx512bw._mm512_shuffle_epi8 (ofLanes128 f) (ofLanes128 g) =
    ok (ofLanes128 fun j => pshufb (f j) (g j)) := by
  simp only [core.core_arch.x86.avx512bw._mm512_shuffle_epi8]
  exact congrArg ok (ofLanes128_ext _ _ fun j hj => by rw [lane128_ofLanes128 f j hj, lane128_ofLanes128 g j hj]; rfl)

theorem add512_eq : core.core_arch.x86.avx512f._mm512_add_epi32 (ofLanes128 f) (ofLanes128 g) =
    ok (ofLanes128 fun j => paddd (f j) (g j)) := by
  simp only [core.core_arch.x86.avx512f._mm512_add_epi32]
  exact congrArg ok (ofLanes128_ext _ _ fun j hj => by rw [lane128_ofLanes128 f j hj, lane128_ofLanes128 g j hj]; rfl)

theorem aesenc512_eq : core.core_arch.x86.vaes._mm512_aesenc_epi128 (ofLanes128 f) (ofLanes128 g) =
    ok (ofLanes128 fun j => mixColumns (subBytes (shiftRows (f j))) ^^^ g j) := by
  simp only [core.core_arch.x86.vaes._mm512_aesenc_epi128]
  exact congrArg ok (ofLanes128_ext _ _ fun j hj => by rw [lane128_ofLanes128 f j hj, lane128_ofLanes128 g j hj])

theorem aesenclast512_eq : core.core_arch.x86.vaes._mm512_aesenclast_epi128 (ofLanes128 f) (ofLanes128 g) =
    ok (ofLanes128 fun j => subBytes (shiftRows (f j)) ^^^ g j) := by
  simp only [core.core_arch.x86.vaes._mm512_aesenclast_epi128]
  exact congrArg ok (ofLanes128_ext _ _ fun j hj => by rw [lane128_ofLanes128 f j hj, lane128_ofLanes128 g j hj])

theorem maskz512_eq (k : Std.U64) : core.core_arch.x86.avx512bw._mm512_maskz_mov_epi8 k (ofLanes128 f) =
    ok (ofLanes128 fun j => ofBytes fun i => if k.bv.getLsbD (16 * j + i) then byte (f j) i else 0) := by
  simp only [core.core_arch.x86.avx512bw._mm512_maskz_mov_epi8]
  exact congrArg ok (ofLanes128_ext _ _ fun j hj => by rw [lane128_ofLanes128 f j hj])

end lanes

theorem ternary128_eq (a b c : BitVec 128) : core.core_arch.x86.avx512f._mm_ternarylogic_epi32
    low.x86_64.ghash.ternaryXor a b c = ok (a ^^^ b ^^^ c) := by
  simp only [core.core_arch.x86.avx512f._mm_ternarylogic_epi32, low.x86_64.ghash.ternaryXor,
    show (150#i32).bv.setWidth 8 = 150#8 by decide, ternary_xor]

theorem broadcast512_eq (a : BitVec 128) :
    core.core_arch.x86.avx512f._mm512_broadcast_i32x4 a = ok (ofLanes128 fun _ => a) := rfl

end rind.x86_64
