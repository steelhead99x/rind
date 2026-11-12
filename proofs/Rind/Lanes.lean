module
public import Aeneas
public import Rind.Vale
@[expose] public section

/-!
# A 128-bit vector's lanes and bytes

Both targets' vector registers as `BitVec 128`, lane 0 lowest, which
`Rind.X86_64.Simd` and `Rind.Aarch64.Neon` model the intrinsics over.
-/

namespace rind.simd

open Aeneas Aeneas.Std rind.vale

/-- 64-bit lane `i`. -/
def lane64 (x : BitVec 128) (i : Nat) : BitVec 64 := x.extractLsb' (64 * i) 64

/-- 32-bit lane `i`. -/
def lane32 (x : BitVec 128) (i : Nat) : BitVec 32 := x.extractLsb' (32 * i) 32

/-- The vector of four 32-bit lanes, lane 0 lowest. -/
def ofLanes32 (f : Nat → BitVec 32) : BitVec 128 := f 3 ++ f 2 ++ f 1 ++ f 0

/-- 16-bit lane `i`. -/
def lane16 (x : BitVec 128) (i : Nat) : BitVec 16 := x.extractLsb' (16 * i) 16

/-- The vector of eight 16-bit lanes, lane 0 lowest. -/
def ofLanes16 (f : Nat → BitVec 16) : BitVec 128 :=
  f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

/-- A byte array as a vector load reads it, `_mm_loadu_si128` or `vld1q_u8`:
its bytes, the first in lane 0. -/
def loadBytes (bytes : List U8) : BitVec 128 := leBytesToQuad32 (bytes.map (·.bv))

/-- A vector's bytes as a vector store writes them, `_mm_storeu_si128` or
`vst1q_u8`: lane 0 first. -/
def storeBytes (v : BitVec 128) : Std.Array Std.U8 16#usize :=
  Std.Array.from ((leQuad32ToBytes v).map fun b => ⟨b⟩) (by simp [leQuad32ToBytes])

end rind.simd
