module
public import Aeneas
public import Rind.Vale
public import Rind.AesInverse
public import Rind.Lanes
@[expose] public section
set_option linter.style.nameCheck false
open Aeneas Aeneas.Std Result

/-!
# aarch64's 128-bit vectors and the NEON intrinsics rind's AES calls

`core::arch` implements each intrinsic with an LLVM builtin, which Aeneas
cannot translate, so these model them by hand, each as the Arm Architecture
Reference Manual defines its instruction, and as `core::arch` passes its
immediate: masked to the bits the instruction reads. Each vector type is its
128 bits, lane 0 lowest, as a little-endian load lays out its bytes, so a
reinterpretation between them changes nothing.

`AESE` and `AESMC` run FIPS 197's rounds, `Rind.Vale`'s `subBytes`,
`shiftRows`, and opaque `mixColumns`, the functions Vale's AES spec assumes,
and `AESD` and `AESIMC` their inverses in `Rind.AesInverse`, on the state laid
out as x86_64's AES instructions take it. That these models
are what the CPU computes is trusted, as an instruction model is for
s2n-bignum's and Vale's own proofs, and `admin/neon-vectors.rs` tests them on
an aarch64 CPU.
-/

/-- `uint8x16_t`: 128 bits, byte lane 0 lowest. -/
@[reducible] def core.core_arch.arm_shared.neon.uint8x16_t : Type := BitVec 128

/-- `uint32x4_t`: 128 bits, word lane 0 lowest. -/
@[reducible] def core.core_arch.arm_shared.neon.uint32x4_t : Type := BitVec 128

/-- `uint64x2_t`: 128 bits, doubleword lane 0 lowest. -/
@[reducible] def core.core_arch.arm_shared.neon.uint64x2_t : Type := BitVec 128

open rind.simd rind.vale

/-- `uint8x16_t`'s `Clone`. -/
def core.core_arch.arm_shared.neon.uint8x16_t.Insts.CoreCloneClone.clone
    (x : core.core_arch.arm_shared.neon.uint8x16_t) : Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok x

/-- `vdupq_n_u8`, `DUP`: `a` in each byte lane. -/
def core.core_arch.arm_shared.neon.generated.vdupq_n_u8 (a : Std.U8) :
    Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok (ofBytes fun _ => a.bv)

/-- `vdupq_n_u32`, `DUP`: `a` in each word lane. -/
def core.core_arch.arm_shared.neon.generated.vdupq_n_u32 (a : Std.U32) :
    Result core.core_arch.arm_shared.neon.uint32x4_t :=
  ok (ofLanes32 fun _ => a.bv)

/-- `vdupq_laneq_u32::<LANE>`, `DUP` (element): word lane `LANE` of `a` in each
word lane, of the two bits of `LANE` the instruction reads. -/
def core.core_arch.arm_shared.neon.generated.vdupq_laneq_u32 (LANE : Std.I32)
    (a : core.core_arch.arm_shared.neon.uint32x4_t) : Result core.core_arch.arm_shared.neon.uint32x4_t :=
  ok (ofLanes32 fun _ => lane32 a (LANE.bv.toNat % 4))

/-- `veorq_u8`, `EOR`. -/
def core.core_arch.arm_shared.neon.generated.veorq_u8 (a b : core.core_arch.arm_shared.neon.uint8x16_t) :
    Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok (a ^^^ b)

/-- `vextq_u8::<N>`, `EXT`: the 16 bytes from byte `N` of `b`:`a`, `a` lowest,
of the four bits of `N` the instruction reads. -/
def core.core_arch.arm_shared.neon.generated.vextq_u8 (N : Std.I32)
    (a b : core.core_arch.arm_shared.neon.uint8x16_t) : Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok (((b ++ a) >>> (8 * (N.bv.toNat % 16))).setWidth 128)

/-- `vqtbl1q_u8`, `TBL` of one register: byte `i` is the byte of `t` that byte
`i` of `idx` selects, or zero if it is past 15. -/
def core.core_arch.aarch64.neon.generated.vqtbl1q_u8 (t idx : core.core_arch.arm_shared.neon.uint8x16_t) :
    Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok (ofBytes fun i => if (byte idx i).toNat < 16 then byte t (byte idx i).toNat else 0)

/-- `vzip1q_u64`, `ZIP1`: the low doublewords of `a` then `b`, `a`'s lowest. -/
def core.core_arch.aarch64.neon.generated.vzip1q_u64 (a b : core.core_arch.arm_shared.neon.uint64x2_t) :
    Result core.core_arch.arm_shared.neon.uint64x2_t :=
  ok (lane64 b 0 ++ lane64 a 0)

/-- `vaeseq_u8`, `AESE`: the round key XORed, then `SubBytes` and `ShiftRows`. -/
def core.core_arch.arm_shared.neon.generated.vaeseq_u8 (data key : core.core_arch.arm_shared.neon.uint8x16_t) :
    Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok (shiftRows (subBytes (data ^^^ key)))

/-- `vaesmcq_u8`, `AESMC`: `MixColumns`. -/
def core.core_arch.arm_shared.neon.generated.vaesmcq_u8 (data : core.core_arch.arm_shared.neon.uint8x16_t) :
    Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok (mixColumns data)

/-- `vaesdq_u8`, `AESD`: the round key XORed, then `InvShiftRows` and `InvSubBytes`. -/
def core.core_arch.arm_shared.neon.generated.vaesdq_u8 (data key : core.core_arch.arm_shared.neon.uint8x16_t) :
    Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok (invSubBytes (invShiftRows (data ^^^ key)))

/-- `vaesimcq_u8`, `AESIMC`: `InvMixColumns`. -/
def core.core_arch.arm_shared.neon.generated.vaesimcq_u8 (data : core.core_arch.arm_shared.neon.uint8x16_t) :
    Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok (invMixColumns data)

/-- `vreinterpretq_u8_p128`: the 128 bits, the least significant byte in lane 0. -/
def core.core_arch.arm_shared.neon.generated.vreinterpretq_u8_p128 (a : Std.U128) :
    Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok a.bv

/-- `vreinterpretq_p128_u8`: the 128 bits, lane 0 least significant. -/
def core.core_arch.arm_shared.neon.generated.vreinterpretq_p128_u8
    (a : core.core_arch.arm_shared.neon.uint8x16_t) : Result Std.U128 :=
  ok ⟨a⟩

/-- `vreinterpretq_u32_u8`: the same bits. -/
def core.core_arch.arm_shared.neon.generated.vreinterpretq_u32_u8
    (a : core.core_arch.arm_shared.neon.uint8x16_t) : Result core.core_arch.arm_shared.neon.uint32x4_t :=
  ok a

/-- `vreinterpretq_u8_u32`: the same bits. -/
def core.core_arch.arm_shared.neon.generated.vreinterpretq_u8_u32
    (a : core.core_arch.arm_shared.neon.uint32x4_t) : Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok a

/-- `vreinterpretq_u64_u8`: the same bits. -/
def core.core_arch.arm_shared.neon.generated.vreinterpretq_u64_u8
    (a : core.core_arch.arm_shared.neon.uint8x16_t) : Result core.core_arch.arm_shared.neon.uint64x2_t :=
  ok a

/-- `vreinterpretq_u8_u64`: the same bits. -/
def core.core_arch.arm_shared.neon.generated.vreinterpretq_u8_u64
    (a : core.core_arch.arm_shared.neon.uint64x2_t) : Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok a
