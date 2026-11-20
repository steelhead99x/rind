module
public import Aeneas
public import Rind.Vale
public import Rind.AesInverse
public import Rind.Lanes
@[expose] public section
set_option linter.style.nameCheck false
open Aeneas Aeneas.Std Result

/-!
# x86_64's vectors and the intrinsics rind's AES-GCM and point select call

`core::arch` implements each intrinsic with an LLVM builtin, which Aeneas
cannot translate, so these model them by hand, each as Intel's Software
Developer's Manual defines its instruction, and as `core::arch` passes its
immediate: masked to the bits the instruction reads. `__m128i` and `__m256i`
are their 128 and 256 bits, lane 0 lowest.

The AES instructions run FIPS 197's rounds, `Rind.Vale`'s `subBytes`,
`shiftRows`, and opaque `mixColumns`, the functions Vale's AES spec assumes,
and their inverses in `Rind.AesInverse`.
That these models are what the CPU computes is trusted, as an instruction
model is for s2n-bignum's and Vale's own proofs.
-/

/-- `__m128i`: 128 bits, lane 0 lowest. -/
@[reducible] def core.core_arch.x86.__m128i : Type := BitVec 128

/-- `__m256i`: 256 bits, lane 0 lowest. -/
@[reducible] def core.core_arch.x86.__m256i : Type := BitVec 256

namespace rind.simd

/-- A 256-bit vector's 32-bit lane `i`. -/
def lane32x8 (x : BitVec 256) (i : Nat) : BitVec 32 := x.extractLsb' (32 * i) 32

/-- The 256-bit vector of eight 32-bit lanes, lane 0 lowest. -/
def ofLanes32x8 (f : Nat → BitVec 32) : BitVec 256 :=
  f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

end rind.simd

open rind.simd rind.vale

/-- `__m128i`'s `Clone`. -/
def core.core_arch.x86.__m128i.Insts.CoreCloneClone.clone (x : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok x

/-- `_mm_xor_si128`, `PXOR`. -/
def core.core_arch.x86.sse2._mm_xor_si128 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (a ^^^ b)

/-- `_mm_and_si128`, `PAND`. -/
def core.core_arch.x86.sse2._mm_and_si128 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (a &&& b)

/-- `_mm_setzero_si128`. -/
def core.core_arch.x86.sse2._mm_setzero_si128 : Result core.core_arch.x86.__m128i :=
  ok 0

/-- `_mm_add_epi64`, `PADDQ`: each 64-bit lane's sum, wrapping. -/
def core.core_arch.x86.sse2._mm_add_epi64 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok ((lane64 a 1 + lane64 b 1) ++ (lane64 a 0 + lane64 b 0))

/-- `_mm_or_si128`, `POR`. -/
def core.core_arch.x86.sse2._mm_or_si128 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (a ||| b)

/-- `_mm_add_epi32`, `PADDD`: each 32-bit lane's sum, wrapping. -/
def core.core_arch.x86.sse2._mm_add_epi32 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (ofLanes32 fun i => lane32 a i + lane32 b i)

/-- `_mm_shufflelo_epi16::<IMM8>`, `PSHUFLW`: 16-bit lane `i` below 4 is the
lane bits `2i` and `2i + 1` of `IMM8` select of the low four, and the high
four are `a`'s. -/
def core.core_arch.x86.sse2._mm_shufflelo_epi16 (IMM8 : Std.I32) (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (ofLanes16 fun i => if i < 4 then lane16 a (IMM8.bv.toNat / 4 ^ i % 4) else lane16 a i)

/-- `_mm_shufflehi_epi16::<IMM8>`, `PSHUFHW`: 16-bit lane `4 + i` is the lane
bits `2i` and `2i + 1` of `IMM8` select of the high four, and the low four are
`a`'s. -/
def core.core_arch.x86.sse2._mm_shufflehi_epi16 (IMM8 : Std.I32) (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (ofLanes16 fun i => if i < 4 then lane16 a i else lane16 a (4 + IMM8.bv.toNat / 4 ^ (i - 4) % 4))

/-- `_mm_slli_epi16::<IMM8>`, `PSLLW`: each 16-bit lane shifted left by
`IMM8` bits, or zero past 15. -/
def core.core_arch.x86.sse2._mm_slli_epi16 (IMM8 : Std.I32) (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  let n := IMM8.bv.toNat % 256
  ok (ofLanes16 fun i => if n > 15 then 0 else lane16 a i <<< n)

/-- `_mm_srli_epi16::<IMM8>`, `PSRLW`: each 16-bit lane shifted right
logically by `IMM8` bits, or zero past 15. -/
def core.core_arch.x86.sse2._mm_srli_epi16 (IMM8 : Std.I32) (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  let n := IMM8.bv.toNat % 256
  ok (ofLanes16 fun i => if n > 15 then 0 else lane16 a i >>> n)

/-- `_mm_srai_epi32::<IMM8>`, `PSRAD`: each 32-bit lane shifted right
arithmetically, by at most 31. -/
def core.core_arch.x86.sse2._mm_srai_epi32 (IMM8 : Std.I32) (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (ofLanes32 fun i => (lane32 a i).sshiftRight (min (IMM8.bv.toNat % 256) 31))

/-- `_mm_shuffle_epi32::<IMM8>`, `PSHUFD`: lane `i` is the lane bits `2i` and
`2i + 1` of `IMM8` select. -/
def core.core_arch.x86.sse2._mm_shuffle_epi32 (IMM8 : Std.I32) (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (ofLanes32 fun i => lane32 a (IMM8.bv.toNat / 4 ^ i % 4))

/-- `_mm_clmulepi64_si128::<IMM8>`, `PCLMULQDQ`: the carry-less product of the
64-bit lanes of `a` and `b` that bits 0 and 4 of `IMM8` select. -/
def core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 (IMM8 : Std.I32)
    (a b : core.core_arch.x86.__m128i) : Result core.core_arch.x86.__m128i :=
  ok (clmul (lane64 a (if IMM8.bv.getLsbD 0 then 1 else 0))
    (lane64 b (if IMM8.bv.getLsbD 4 then 1 else 0)))

/-- `_mm_slli_si128::<IMM8>`, `PSLLDQ`: shifted left by `IMM8` bytes, or zero
past 15. -/
def core.core_arch.x86.sse2._mm_slli_si128 (IMM8 : Std.I32) (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  let n := IMM8.bv.toNat % 256
  ok (if n > 15 then 0 else a <<< (8 * n))

/-- `_mm_shuffle_epi8`, `PSHUFB`: byte `i` is zero if byte `i` of `b` has its
top bit set, and otherwise the byte of `a` its low four bits select. -/
def core.core_arch.x86.ssse3._mm_shuffle_epi8 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (ofBytes fun i => if (byte b i).msb then 0 else byte a ((byte b i).toNat % 16))

/-- `_mm_setr_epi8`: the bytes in order, the first lowest. -/
def core.core_arch.x86.sse2._mm_setr_epi8
    (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 : Std.I8) :
    Result core.core_arch.x86.__m128i :=
  ok (leBytesToQuad32
    [e0.bv, e1.bv, e2.bv, e3.bv, e4.bv, e5.bv, e6.bv, e7.bv, e8.bv, e9.bv, e10.bv, e11.bv, e12.bv,
      e13.bv, e14.bv, e15.bv])

/-- `_mm_set_epi64x`: the 64-bit lanes, the last lowest. -/
def core.core_arch.x86.sse2._mm_set_epi64x (e1 e0 : Std.I64) : Result core.core_arch.x86.__m128i :=
  ok (e1.bv ++ e0.bv)

/-- `_mm_cvtsi128_si64`, `MOVQ`: the low 64-bit lane. -/
def core.core_arch.x86_64.sse2._mm_cvtsi128_si64 (a : core.core_arch.x86.__m128i) : Result Std.I64 :=
  ok ⟨lane64 a 0⟩

/-- `_mm_unpackhi_epi64`, `PUNPCKHQDQ`: the high 64-bit lanes of `a` then `b`, `a`'s lowest. -/
def core.core_arch.x86.sse2._mm_unpackhi_epi64 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (lane64 b 1 ++ lane64 a 1)

/-- `_mm_set1_epi32`: each 32-bit lane `a`. -/
def core.core_arch.x86.sse2._mm_set1_epi32 (a : Std.I32) : Result core.core_arch.x86.__m128i :=
  ok (ofLanes32 fun _ => a.bv)

/-- `_mm_aesenc_si128`, `AESENC`: `ShiftRows`, `SubBytes`, and `MixColumns`, then
the round key XORed. -/
def core.core_arch.x86.aes._mm_aesenc_si128 (a roundKey : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (mixColumns (subBytes (shiftRows a)) ^^^ roundKey)

/-- `_mm_aesenclast_si128`, `AESENCLAST`: `ShiftRows` and `SubBytes`, then the
round key XORed. -/
def core.core_arch.x86.aes._mm_aesenclast_si128 (a roundKey : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (subBytes (shiftRows a) ^^^ roundKey)

/-- `_mm_aesdec_si128`, `AESDEC`: `InvShiftRows`, `InvSubBytes`, and
`InvMixColumns`, then the round key XORed. -/
def core.core_arch.x86.aes._mm_aesdec_si128 (a roundKey : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (invMixColumns (invSubBytes (invShiftRows a)) ^^^ roundKey)

/-- `_mm_aesdeclast_si128`, `AESDECLAST`: `InvShiftRows` and `InvSubBytes`,
then the round key XORed. -/
def core.core_arch.x86.aes._mm_aesdeclast_si128 (a roundKey : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (invSubBytes (invShiftRows a) ^^^ roundKey)

/-- `_mm_aesimc_si128`, `AESIMC`: `InvMixColumns`. -/
def core.core_arch.x86.aes._mm_aesimc_si128 (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (invMixColumns a)

/-- `_mm_unpacklo_epi64`, `PUNPCKLQDQ`: the low 64-bit lanes of `a` then `b`, `a`'s lowest. -/
def core.core_arch.x86.sse2._mm_unpacklo_epi64 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (lane64 b 0 ++ lane64 a 0)

/-- `_mm_alignr_epi8::<IMM8>`, `PALIGNR`: the 16 bytes from byte `IMM8` of
`a`:`b`, `b` lowest, or zero past 31. -/
def core.core_arch.x86.ssse3._mm_alignr_epi8 (IMM8 : Std.I32) (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (((a ++ b) >>> (8 * (IMM8.bv.toNat % 256))).setWidth 128)

/-- `_mm_cmpeq_epi32`, `PCMPEQD`: each 32-bit lane all ones where the lanes
are equal, and zero where not. -/
def core.core_arch.x86.sse2._mm_cmpeq_epi32 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i :=
  ok (ofLanes32 fun i => if lane32 a i = lane32 b i then BitVec.allOnes 32 else 0)

/-- `_mm256_setzero_si256`. -/
def core.core_arch.x86.avx._mm256_setzero_si256 : Result core.core_arch.x86.__m256i :=
  ok 0

/-- `_mm256_set1_epi32`: each 32-bit lane `a`. -/
def core.core_arch.x86.avx._mm256_set1_epi32 (a : Std.I32) : Result core.core_arch.x86.__m256i :=
  ok (ofLanes32x8 fun _ => a.bv)

/-- `_mm256_castsi256_si128`: the low 128 bits. -/
def core.core_arch.x86.avx._mm256_castsi256_si128 (a : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m128i :=
  ok (a.setWidth 128)

/-- `_mm256_cmpeq_epi32`, `VPCMPEQD`: each 32-bit lane all ones where the
lanes are equal, and zero where not. -/
def core.core_arch.x86.avx2._mm256_cmpeq_epi32 (a b : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m256i :=
  ok (ofLanes32x8 fun i => if lane32x8 a i = lane32x8 b i then BitVec.allOnes 32 else 0)

/-- `_mm256_add_epi32`, `VPADDD`: each 32-bit lane's sum, wrapping. -/
def core.core_arch.x86.avx2._mm256_add_epi32 (a b : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m256i :=
  ok (ofLanes32x8 fun i => lane32x8 a i + lane32x8 b i)

/-- `_mm256_and_si256`, `VPAND`. -/
def core.core_arch.x86.avx2._mm256_and_si256 (a b : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m256i :=
  ok (a &&& b)

/-- `_mm256_xor_si256`, `VPXOR`. -/
def core.core_arch.x86.avx2._mm256_xor_si256 (a b : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m256i :=
  ok (a ^^^ b)

namespace rind.simd

/-- A 256-bit vector's 128-bit half `j`. -/
def half (x : BitVec 256) (j : Nat) : BitVec 128 := x.extractLsb' (128 * j) 128

/-- The 256-bit vector of two 128-bit halves, half 0 lowest. -/
def ofHalves (f : Nat → BitVec 128) : BitVec 256 := f 1 ++ f 0

end rind.simd

/-- `_mm256_setr_epi32`: the 32-bit lanes in order, the first lowest. -/
def core.core_arch.x86.avx._mm256_setr_epi32 (e0 e1 e2 e3 e4 e5 e6 e7 : Std.I32) :
    Result core.core_arch.x86.__m256i :=
  ok (e7.bv ++ e6.bv ++ e5.bv ++ e4.bv ++ e3.bv ++ e2.bv ++ e1.bv ++ e0.bv)

/-- `_mm256_set_epi8`: the bytes, the last lowest. -/
def core.core_arch.x86.avx._mm256_set_epi8
    (e31 e30 e29 e28 e27 e26 e25 e24 e23 e22 e21 e20 e19 e18 e17 e16 e15 e14 e13 e12 e11 e10 e9 e8 e7
      e6 e5 e4 e3 e2 e1 e0 : Std.I8) : Result core.core_arch.x86.__m256i :=
  ok (e31.bv ++ e30.bv ++ e29.bv ++ e28.bv ++ e27.bv ++ e26.bv ++ e25.bv ++ e24.bv ++ e23.bv ++ e22.bv ++
    e21.bv ++ e20.bv ++ e19.bv ++ e18.bv ++ e17.bv ++ e16.bv ++ e15.bv ++ e14.bv ++ e13.bv ++ e12.bv ++
    e11.bv ++ e10.bv ++ e9.bv ++ e8.bv ++ e7.bv ++ e6.bv ++ e5.bv ++ e4.bv ++ e3.bv ++ e2.bv ++ e1.bv ++ e0.bv)

/-- `_mm256_extract_epi32::<INDEX>`: the 32-bit lane `INDEX` selects. Rust
accepts only 0 to 7; the model reads `INDEX`'s low three bits. -/
def core.core_arch.x86.avx._mm256_extract_epi32 (INDEX : Std.I32) (a : core.core_arch.x86.__m256i) :
    Result Std.I32 :=
  ok ⟨lane32x8 a (INDEX.bv.toNat % 8)⟩

/-- `_mm256_or_si256`, `VPOR`. -/
def core.core_arch.x86.avx2._mm256_or_si256 (a b : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m256i :=
  ok (a ||| b)

/-- `_mm256_slli_epi32::<IMM8>`, `VPSLLD`: each 32-bit lane shifted left by
`IMM8` bits, or zero past 31. -/
def core.core_arch.x86.avx2._mm256_slli_epi32 (IMM8 : Std.I32) (a : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m256i :=
  let n := IMM8.bv.toNat % 256
  ok (ofLanes32x8 fun i => if n > 31 then 0 else lane32x8 a i <<< n)

/-- `_mm256_srli_epi32::<IMM8>`, `VPSRLD`: each 32-bit lane shifted right
logically by `IMM8` bits, or zero past 31. -/
def core.core_arch.x86.avx2._mm256_srli_epi32 (IMM8 : Std.I32) (a : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m256i :=
  let n := IMM8.bv.toNat % 256
  ok (ofLanes32x8 fun i => if n > 31 then 0 else lane32x8 a i >>> n)

/-- `_mm256_shuffle_epi8`, `VPSHUFB`: `PSHUFB` in each 128-bit half. -/
def core.core_arch.x86.avx2._mm256_shuffle_epi8 (a b : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m256i :=
  ok (ofHalves fun j => ofBytes fun i =>
    if (byte (half b j) i).msb then 0 else byte (half a j) ((byte (half b j) i).toNat % 16))

/-- `_mm256_shuffle_epi32::<MASK>`, `VPSHUFD`: `PSHUFD` in each 128-bit half. -/
def core.core_arch.x86.avx2._mm256_shuffle_epi32 (MASK : Std.I32) (a : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m256i :=
  ok (ofHalves fun j => ofLanes32 fun i => lane32 (half a j) (MASK.bv.toNat / 4 ^ i % 4))

/-- `_mm256_permute2x128_si256::<IMM8>`, `VPERM2I128`: half `j` is zero if
bit `4j + 3` of `IMM8` is set, and otherwise the half of `a`:`b`, `a`'s
lowest, that bits `4j` and `4j + 1` select. -/
def core.core_arch.x86.avx2._mm256_permute2x128_si256 (IMM8 : Std.I32)
    (a b : core.core_arch.x86.__m256i) : Result core.core_arch.x86.__m256i :=
  ok (ofHalves fun j =>
    let sel := IMM8.bv.toNat / 16 ^ j % 16
    if sel / 8 % 2 = 1 then 0 else [half a 0, half a 1, half b 0, half b 1][sel % 4]!)

/-! ## 512-bit vectors

`__m512i` is its 512 bits, 128-bit lane 0 lowest. VAES, VPCLMULQDQ, and the
byte shuffle and 32-bit operations below act on each 128-bit lane as their
128-bit forms above do, which is how Intel's manual defines them. -/

/-- `__m512i`: 512 bits, 128-bit lane 0 lowest. -/
@[reducible] def core.core_arch.x86.__m512i : Type := BitVec 512

namespace rind.simd

/-- A 512-bit vector's 128-bit lane `j`. -/
def lane128 (x : BitVec 512) (j : Nat) : BitVec 128 := x.extractLsb' (128 * j) 128

/-- The 512-bit vector of four 128-bit lanes, lane 0 lowest. -/
def ofLanes128 (f : Nat → BitVec 128) : BitVec 512 := f 3 ++ f 2 ++ f 1 ++ f 0

/-- `VPTERNLOG`'s bitwise function: bit `i` is the bit of `imm` that bits `i`
of `a`, `b`, and `c` index, `a`'s the highest, as the union of the minterms
`imm` selects. -/
def ternary {w : Nat} (imm : BitVec 8) (a b c : BitVec w) : BitVec w :=
  let t (k : Nat) (m : BitVec w) := if imm.getLsbD k then m else 0
  t 0 (~~~a &&& ~~~b &&& ~~~c) ||| t 1 (~~~a &&& ~~~b &&& c) ||| t 2 (~~~a &&& b &&& ~~~c) |||
    t 3 (~~~a &&& b &&& c) ||| t 4 (a &&& ~~~b &&& ~~~c) ||| t 5 (a &&& ~~~b &&& c) |||
    t 6 (a &&& b &&& ~~~c) ||| t 7 (a &&& b &&& c)

end rind.simd

open rind.simd

/-- `_mm512_setzero_si512`. -/
def core.core_arch.x86.avx512f._mm512_setzero_si512 : Result core.core_arch.x86.__m512i :=
  ok 0

/-- `_mm512_xor_epi32`, `VPXORD`. -/
def core.core_arch.x86.avx512f._mm512_xor_epi32 (a b : core.core_arch.x86.__m512i) :
    Result core.core_arch.x86.__m512i :=
  ok (a ^^^ b)

/-- `_mm512_xor_epi64`, `VPXORQ`. -/
def core.core_arch.x86.avx512f._mm512_xor_epi64 (a b : core.core_arch.x86.__m512i) :
    Result core.core_arch.x86.__m512i :=
  ok (a ^^^ b)

/-- `_mm512_add_epi32`, `VPADDD`: each 32-bit lane's sum, wrapping. -/
def core.core_arch.x86.avx512f._mm512_add_epi32 (a b : core.core_arch.x86.__m512i) :
    Result core.core_arch.x86.__m512i :=
  ok (ofLanes128 fun j => ofLanes32 fun i => lane32 (lane128 a j) i + lane32 (lane128 b j) i)

/-- `_mm512_inserti32x4::<IMM8>`, `VINSERTI32X4`: `a` with its 128-bit lane
that bits 0 and 1 of `IMM8` select replaced by `b`. -/
def core.core_arch.x86.avx512f._mm512_inserti32x4 (IMM8 : Std.I32) (a : core.core_arch.x86.__m512i)
    (b : core.core_arch.x86.__m128i) : Result core.core_arch.x86.__m512i :=
  ok (ofLanes128 fun j => if j = IMM8.bv.toNat % 4 then b else lane128 a j)

/-- `_mm512_extracti32x4_epi32::<IMM8>`, `VEXTRACTI32X4`: the 128-bit lane that
bits 0 and 1 of `IMM8` select. -/
def core.core_arch.x86.avx512f._mm512_extracti32x4_epi32 (IMM8 : Std.I32)
    (a : core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m128i :=
  ok (lane128 a (IMM8.bv.toNat % 4))

/-- `_mm512_broadcast_i32x4`, `VBROADCASTI32X4`: `a` in each 128-bit lane. -/
def core.core_arch.x86.avx512f._mm512_broadcast_i32x4 (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m512i :=
  ok (ofLanes128 fun _ => a)

/-- `_mm512_shuffle_epi32::<IMM8>`, `VPSHUFD`: `PSHUFD` in each 128-bit lane. -/
def core.core_arch.x86.avx512f._mm512_shuffle_epi32 (IMM8 : Std.I32) (a : core.core_arch.x86.__m512i) :
    Result core.core_arch.x86.__m512i :=
  ok (ofLanes128 fun j => ofLanes32 fun i => lane32 (lane128 a j) (IMM8.bv.toNat / 4 ^ i % 4))

/-- `_mm512_ternarylogic_epi32::<IMM8>`, `VPTERNLOGD`: `ternary` of the low
byte of `IMM8`. -/
def core.core_arch.x86.avx512f._mm512_ternarylogic_epi32 (IMM8 : Std.I32)
    (a b c : core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m512i :=
  ok (ternary (IMM8.bv.setWidth 8) a b c)

/-- `_mm512_ternarylogic_epi64::<IMM8>`, `VPTERNLOGQ`: `ternary` of the low
byte of `IMM8`. -/
def core.core_arch.x86.avx512f._mm512_ternarylogic_epi64 (IMM8 : Std.I32)
    (a b c : core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m512i :=
  ok (ternary (IMM8.bv.setWidth 8) a b c)

/-- `_mm_ternarylogic_epi32::<IMM8>`, `VPTERNLOGD` on 128 bits: `ternary` of
the low byte of `IMM8`. -/
def core.core_arch.x86.avx512f._mm_ternarylogic_epi32 (IMM8 : Std.I32)
    (a b c : core.core_arch.x86.__m128i) : Result core.core_arch.x86.__m128i :=
  ok (ternary (IMM8.bv.setWidth 8) a b c)

/-- `_mm512_shuffle_epi8`, `VPSHUFB`: `PSHUFB` in each 128-bit lane. -/
def core.core_arch.x86.avx512bw._mm512_shuffle_epi8 (a b : core.core_arch.x86.__m512i) :
    Result core.core_arch.x86.__m512i :=
  ok (ofLanes128 fun j => ofBytes fun i =>
    if (byte (lane128 b j) i).msb then 0 else byte (lane128 a j) ((byte (lane128 b j) i).toNat % 16))

/-- `_mm512_maskz_mov_epi8`, `VMOVDQU8` zero-masked: byte `i` is `a`'s where
bit `i` of `k` is set, and zero where not. -/
def core.core_arch.x86.avx512bw._mm512_maskz_mov_epi8 (k : Std.U64) (a : core.core_arch.x86.__m512i) :
    Result core.core_arch.x86.__m512i :=
  ok (ofLanes128 fun j => ofBytes fun i => if k.bv.getLsbD (16 * j + i) then byte (lane128 a j) i else 0)

/-- `_mm512_aesenc_epi128`, `VAESENC`: `AESENC` in each 128-bit lane. -/
def core.core_arch.x86.vaes._mm512_aesenc_epi128 (a roundKey : core.core_arch.x86.__m512i) :
    Result core.core_arch.x86.__m512i :=
  ok (ofLanes128 fun j => mixColumns (subBytes (shiftRows (lane128 a j))) ^^^ lane128 roundKey j)

/-- `_mm512_aesenclast_epi128`, `VAESENCLAST`: `AESENCLAST` in each 128-bit lane. -/
def core.core_arch.x86.vaes._mm512_aesenclast_epi128 (a roundKey : core.core_arch.x86.__m512i) :
    Result core.core_arch.x86.__m512i :=
  ok (ofLanes128 fun j => subBytes (shiftRows (lane128 a j)) ^^^ lane128 roundKey j)

/-- `_mm512_clmulepi64_epi128::<IMM8>`, `VPCLMULQDQ`: `PCLMULQDQ` in each
128-bit lane. -/
def core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 (IMM8 : Std.I32)
    (a b : core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m512i :=
  ok (ofLanes128 fun j => clmul (lane64 (lane128 a j) (if IMM8.bv.getLsbD 0 then 1 else 0))
    (lane64 (lane128 b j) (if IMM8.bv.getLsbD 4 then 1 else 0)))
