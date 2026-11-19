module
public import Aeneas
public import Rind.Vale
public import Rind.AesInverse
public import Rind.Lanes
@[expose] public section
set_option linter.style.nameCheck false
open Aeneas Aeneas.Std Result

/-!
# aarch64's 128-bit vectors and the NEON intrinsics rind's AES and point select call

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

/-- `vsetq_lane_u32::<LANE>`, `INS` (general): `v` with word lane `LANE` set
to `a`, of the two bits of `LANE` the instruction reads. -/
def core.core_arch.arm_shared.neon.generated.vsetq_lane_u32 (LANE : Std.I32) (a : Std.U32)
    (v : core.core_arch.arm_shared.neon.uint32x4_t) : Result core.core_arch.arm_shared.neon.uint32x4_t :=
  ok (ofLanes32 fun i => if i = LANE.bv.toNat % 4 then a.bv else lane32 v i)

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

/-- `vceqq_u32`, `CMEQ`: each word lane all ones where the lanes are equal, and
zero where not. -/
def core.core_arch.arm_shared.neon.generated.vceqq_u32 (a b : core.core_arch.arm_shared.neon.uint32x4_t) :
    Result core.core_arch.arm_shared.neon.uint32x4_t :=
  ok (ofLanes32 fun i => if lane32 a i = lane32 b i then BitVec.allOnes 32 else 0)

/-- `vaddq_u32`, `ADD`: each word lane's sum, wrapping. -/
def core.core_arch.arm_shared.neon.generated.vaddq_u32 (a b : core.core_arch.arm_shared.neon.uint32x4_t) :
    Result core.core_arch.arm_shared.neon.uint32x4_t :=
  ok (ofLanes32 fun i => lane32 a i + lane32 b i)

/-- `vandq_u32`, `AND`. -/
def core.core_arch.arm_shared.neon.generated.vandq_u32 (a b : core.core_arch.arm_shared.neon.uint32x4_t) :
    Result core.core_arch.arm_shared.neon.uint32x4_t :=
  ok (a &&& b)

/-- `veorq_u32`, `EOR`. -/
def core.core_arch.arm_shared.neon.generated.veorq_u32 (a b : core.core_arch.arm_shared.neon.uint32x4_t) :
    Result core.core_arch.arm_shared.neon.uint32x4_t :=
  ok (a ^^^ b)

/-! ## The intrinsics rind's PMULL GHASH and one-pass AES-GCM call -/

/-- `int32x4_t`: 128 bits, word lane 0 lowest. -/
@[reducible] def core.core_arch.arm_shared.neon.int32x4_t : Type := BitVec 128

/-- `vextq_u64::<N>`, `EXT`: the two doublewords from doubleword `N` of
`b`:`a`, `a` lowest, of the bit of `N` the instruction reads. -/
def core.core_arch.arm_shared.neon.generated.vextq_u64 (N : Std.I32)
    (a b : core.core_arch.arm_shared.neon.uint64x2_t) : Result core.core_arch.arm_shared.neon.uint64x2_t :=
  ok (((b ++ a) >>> (64 * (N.bv.toNat % 2))).setWidth 128)

/-- `veorq_u64`, `EOR`. -/
def core.core_arch.arm_shared.neon.generated.veorq_u64 (a b : core.core_arch.arm_shared.neon.uint64x2_t) :
    Result core.core_arch.arm_shared.neon.uint64x2_t :=
  ok (a ^^^ b)

/-- `vandq_u64`, `AND`. -/
def core.core_arch.arm_shared.neon.generated.vandq_u64 (a b : core.core_arch.arm_shared.neon.uint64x2_t) :
    Result core.core_arch.arm_shared.neon.uint64x2_t :=
  ok (a &&& b)

/-- `vandq_u8`, `AND`. -/
def core.core_arch.arm_shared.neon.generated.vandq_u8 (a b : core.core_arch.arm_shared.neon.uint8x16_t) :
    Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok (a &&& b)

/-- `vaddq_u64`, `ADD`: each doubleword lane's sum, wrapping. -/
def core.core_arch.arm_shared.neon.generated.vaddq_u64 (a b : core.core_arch.arm_shared.neon.uint64x2_t) :
    Result core.core_arch.arm_shared.neon.uint64x2_t :=
  ok ((lane64 a 1 + lane64 b 1) ++ (lane64 a 0 + lane64 b 0))

/-- `vgetq_lane_u64::<LANE>`, `UMOV`: doubleword lane `LANE` of `v`, of the
bit of `LANE` the instruction reads. -/
def core.core_arch.arm_shared.neon.generated.vgetq_lane_u64 (LANE : Std.I32)
    (v : core.core_arch.arm_shared.neon.uint64x2_t) : Result Std.U64 :=
  ok ⟨lane64 v (LANE.bv.toNat % 2)⟩

/-- `vdupq_n_u64`, `DUP`: `a` in each doubleword lane. -/
def core.core_arch.arm_shared.neon.generated.vdupq_n_u64 (a : Std.U64) :
    Result core.core_arch.arm_shared.neon.uint64x2_t :=
  ok (a.bv ++ a.bv)

/-- `vmull_p64`, `PMULL`: the carry-less product of two doublewords. -/
def core.core_arch.aarch64.neon.generated.vmull_p64 (a b : Std.U64) : Result Std.U128 :=
  ok ⟨clmul a.bv b.bv⟩

/-- `vrev64q_u8`, `REV64`: the bytes of each doubleword lane reversed. -/
def core.core_arch.arm_shared.neon.generated.vrev64q_u8 (a : core.core_arch.arm_shared.neon.uint8x16_t) :
    Result core.core_arch.arm_shared.neon.uint8x16_t :=
  ok (ofBytes fun i => byte a (8 * (i / 8) + (7 - i % 8)))

/-- `vreinterpretq_s32_u64`: the same bits. -/
def core.core_arch.arm_shared.neon.generated.vreinterpretq_s32_u64
    (a : core.core_arch.arm_shared.neon.uint64x2_t) : Result core.core_arch.arm_shared.neon.int32x4_t :=
  ok a

/-- `vreinterpretq_u64_s32`: the same bits. -/
def core.core_arch.arm_shared.neon.generated.vreinterpretq_u64_s32
    (a : core.core_arch.arm_shared.neon.int32x4_t) : Result core.core_arch.arm_shared.neon.uint64x2_t :=
  ok a

/-- `vgetq_lane_s32::<LANE>`, `MOV`: word lane `LANE` of `v`, of the two bits
of `LANE` the instruction reads. -/
def core.core_arch.arm_shared.neon.generated.vgetq_lane_s32 (LANE : Std.I32)
    (v : core.core_arch.arm_shared.neon.int32x4_t) : Result Std.I32 :=
  ok ⟨lane32 v (LANE.bv.toNat % 4)⟩

/-- `vsetq_lane_s32::<LANE>`, `INS` (general): `v` with word lane `LANE` set
to `a`, of the two bits of `LANE` the instruction reads. -/
def core.core_arch.arm_shared.neon.generated.vsetq_lane_s32 (LANE : Std.I32) (a : Std.I32)
    (v : core.core_arch.arm_shared.neon.int32x4_t) : Result core.core_arch.arm_shared.neon.int32x4_t :=
  ok (ofLanes32 fun i => if i = LANE.bv.toNat % 4 then a.bv else lane32 v i)

/-- `vshrq_n_s32::<N>`, `SSHR`: each word lane shifted right by `N`, from 1
to 32, filling with its sign; `core::arch` shifts by 31 for 32, which fills
the same. -/
def core.core_arch.arm_shared.neon.generated.vshrq_n_s32 (N : Std.I32)
    (a : core.core_arch.arm_shared.neon.int32x4_t) : Result core.core_arch.arm_shared.neon.int32x4_t :=
  ok (ofLanes32 fun i => (lane32 a i).sshiftRight (min N.bv.toNat 31))
