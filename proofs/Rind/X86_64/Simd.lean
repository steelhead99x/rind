module
public import Aeneas
public import Rind.Vale
@[expose] public section
set_option linter.style.nameCheck false
open Aeneas Aeneas.Std Result

/-!
# x86_64's 128-bit vectors and the intrinsics rind's AES-GCM setup and partial blocks call

`core::arch` implements each intrinsic with an LLVM builtin, which Aeneas
cannot translate, so these model them by hand, each as Intel's Software
Developer's Manual defines its instruction, and as `core::arch` passes its
immediate: masked to the bits the instruction reads. `__m128i` is its 128 bits,
lane 0 lowest.

The AES instructions run FIPS 197's rounds, `Rind.Vale`'s `subBytes`,
`shiftRows`, and opaque `mixColumns`, the functions Vale's AES spec assumes.
That these models are what the CPU computes is trusted, as an instruction
model is for s2n-bignum's and Vale's own proofs.
-/

/-- `__m128i`: 128 bits, lane 0 lowest. -/
@[reducible] def core.core_arch.x86.__m128i : Type := BitVec 128

namespace rind.simd

/-- 64-bit lane `i`. -/
def lane64 (x : BitVec 128) (i : Nat) : BitVec 64 := x.extractLsb' (64 * i) 64

/-- 32-bit lane `i`. -/
def lane32 (x : BitVec 128) (i : Nat) : BitVec 32 := x.extractLsb' (32 * i) 32

/-- The vector of four 32-bit lanes, lane 0 lowest. -/
def ofLanes32 (f : Nat → BitVec 32) : BitVec 128 := f 3 ++ f 2 ++ f 1 ++ f 0

/-- Carry-less multiplication's first `k` partial products: `a` shifted left by
each of `b`'s set bits below `k`, XORed. -/
def clmulAux (a b : BitVec 64) : Nat → BitVec 128
  | 0 => 0
  | k + 1 => clmulAux a b k ^^^ (if b.getLsbD k then a.setWidth 128 <<< k else 0)

/-- `PCLMULQDQ`'s carry-less product of two 64-bit values. -/
@[irreducible] def clmul (a b : BitVec 64) : BitVec 128 := clmulAux a b 64

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
