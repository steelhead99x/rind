module

public import VerifiedGarbage.Impl.MlKem.X86_64.NttAvx2

/-!
# ML-KEM on x86-64: `vg_mlkem_decode12_avx2`

`decode12Avx2(b = rdi, f = rsi)` is `vg_mlkem_decode12` (`Encode12.lean`)
on eight coefficients at a time, from 12 bytes, in the doublewords of an
AVX2 register, as `vg_mlkem_sample_ntt4_avx2` computes its candidates
(`Sample4.vcand`): `vbroadcasti128` loads 16 bytes into both lanes,
`vpshufb` puts bytes `3i, 3i+1` (for the first value of a pair) or
`3i+1, 3i+2` (for the second) of the 12 in the low half of each
doubleword, bytes 0 to 5 in the low lane and 6 to 11 in the high one
(`ymm8`), `vpsrlvd` shifts the second values right by 4 (`ymm9`), and
`vpand` keeps their low 12 bits (`ymm10`). Each value `x < 2¹²` is then
reduced modulo `q` (`ymm11`) without a branch: `x - q` is negative exactly
when `x < q`, and `vpsrad` by 31 turns its sign into a mask of `q` to add
back. The eight are stored to `f`.

The loop runs over the first 31 groups of 12 bytes, with `rcx` counting
down. A load of the last group would read 4 bytes past `b`, so the code
loads it from 4 bytes before it, with a mask that takes bytes 4 to 15
instead (`ymm12`). The constants are built in registers, through `rax`,
`ymm0` and `ymm1`. There are no multiplications. It clears the upper
halves of the vector registers before returning (`vzeroupper`), for the
SSE code its callers run next. Every address and branch depends only on
the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The constants of four quadwords (from the lowest) that the AVX2 code of
ML-KEM loads (`yconst4`), one after the other: the words of the static
`VG_MLKEM_YCONSTS`. -/
def ytab : List (BitVec 64) := [
  0x0000000b00000000, 0x0000000b00000000, 0x0000000b00000000, 0x0000000b00000000,
  0x3fffff, 0x3fffff, 0x3fffff, 0x3fffff,
  0, 22, 4, 26,
  0x8080050403020100, 0x8080808080808080, 0x0201008080808080, 0x8080808080050403,
  0x0000000500000000, 0x0000000500000000, 0x0000000500000000, 0x0000000500000000,
  0x3ff, 0x3ff, 0x3ff, 0x3ff,
  0, 10, 4, 14,
  0x8080808080020100, 0x8080808080808080, 0x8080800201008080, 0x8080808080808080,
  0x8080020180800100, 0x8080050480040302, 0x8008070680800605, 0x80800a0980800908,
  0x8080070680800605, 0x80800a0980090807, 0x800d0c0b80800b0a, 0x80800f0e80800e0d,
  0x0000000300000000, 0x0000000100000006, 0x0000000700000004, 0x0000000500000002,
  0x8080010080808000, 0x8080020180808001, 0x8080800380800302, 0x8080800480800403,
  0x8080060580808005, 0x8080070680808006, 0x8080800880800807, 0x8080800980800908,
  0x8080070680808006, 0x8080080780808007, 0x8080800980800908, 0x8080800a80800a09,
  0x80800c0b8080800b, 0x80800d0c8080800c, 0x8080800e80800e0d, 0x8080800f80800f0e,
  0x0000000500000000, 0x0000000700000002, 0x0000000100000004, 0x0000000300000006,
  0x0000000a00000000, 0x0000000a00000000, 0x0000000a00000000, 0x0000000a00000000,
  0xfffff, 0xfffff, 0xfffff, 0xfffff,
  0, 20, 0, 20,
  0x8080800403020100, 0x8080808080808080, 0x0201008080808080, 0x8080808080800403,
  0x0000000400000000, 0x0000000400000000, 0x0000000400000000, 0x0000000400000000,
  0x8080808080800800, 0x8080808080808080, 0x8080808008008080, 0x8080808080808080,
  0x0000000100000000, 0x0000000300000002, 0x0000000500000004, 0x0000000700000006,
  0x0000000900000008, 0x0000000b0000000a, 0x0000000d0000000c, 0x0000000f0000000e,
  0x0000001100000010, 0x0000001300000012, 0x0000001500000014, 0x0000001700000016,
  0x0000001900000018, 0x0000001b0000001a, 0x0000001d0000001c, 0x0000001f0000001e,
  0x8080020180800100, 0x8080040380800302, 0x8080070680800605, 0x8080090880800807,
  0x8080080780800706, 0x80800a0980800908, 0x80800d0c80800c0b, 0x80800f0e80800e0d,
  0x0000000200000000, 0x0000000600000004, 0x0000000200000000, 0x0000000600000004,
  0x8080800080808000, 0x8080800180808001, 0x8080800280808002, 0x8080800380808003,
  0x8080800480808004, 0x8080800580808005, 0x8080800680808006, 0x8080800780808007,
  0x8080800880808008, 0x8080800980808009, 0x8080800a8080800a, 0x8080800b8080800b,
  0x8080800c8080800c, 0x8080800d8080800d, 0x8080800e8080800e, 0x8080800f8080800f,
  0x0302010003020100, 0x0302010003020100, 0x0302010003020100, 0x0302010003020100,
  0x0706050407060504, 0x0706050407060504, 0x0706050407060504, 0x0706050407060504,
  0x0b0a09080b0a0908, 0x0b0a09080b0a0908, 0x0b0a09080b0a0908, 0x0b0a09080b0a0908,
  0x0f0e0d0c0f0e0d0c, 0x0f0e0d0c0f0e0d0c, 0x0f0e0d0c0f0e0d0c, 0x0f0e0d0c0f0e0d0c,
  0x8080020180800100, 0x8080050480800403, 0x8080080780800706, 0x80800b0a80800a09,
  0x8080060580800504, 0x8080090880800807, 0x80800c0b80800b0a, 0x80800f0e80800e0d,
  0x0908060504020100, 0x808080800e0d0c0a, 0x0908060504020100, 0x808080800e0d0c0a,
  0x0000000100000000, 0x0000000400000002, 0x0000000600000005, 0,
  0x0000000400000002, 0x0000000600000005, 0, 0x0000000100000000,
  12, 12, 12, 12,
  0x0a09080403020100, 0x8080808080800c0b, 0x808080800c0b0a09, 0x0804030201008080,
  0x808080800c080400, 0x8080808080808080, 0x0c08040080808080, 0x8080808080808080,
  10, 10, 10, 10,
  10, 30, 10, 30,
  0x8080800403020100, 0x800c0b0a09088080, 0x8080800403020100, 0x800c0b0a09088080,
  0x0201008080808080, 0x0880808080800403, 0x0201008080808080, 0x0880808080800403]

/-- The index in `ytab` of the constant `q₀, q₁, q₂, q₃` among those of the
quadwords `ws`, four at a time (their number if it is none of them). -/
def yfind (q₀ q₁ q₂ q₃ : BitVec 64) : List (BitVec 64) → Nat
  | a :: b :: c :: d :: t => if a = q₀ ∧ b = q₁ ∧ c = q₂ ∧ d = q₃ then 0 else yfind q₀ q₁ q₂ q₃ t + 1
  | _ => 0

/-- `ymm r` set to the quadwords `q₀, q₁, q₂, q₃` (from the lowest), from the
static `VG_MLKEM_YCONSTS` of them all (`ytab`), whose address goes to `rax`. -/
def yconst4 (r : XReg) (q₀ q₁ q₂ q₃ : BitVec 64) : List Instr :=
  [.leaSym .rax "VG_MLKEM_YCONSTS",
    .vmovdquTbl r (at_ .rax (32 * yfind q₀ q₁ q₂ q₃ ytab)) "VG_MLKEM_YCONSTS" ytab]

/-- The constants: the masks of `vpshufb` (`ymm8`, and `ymm12` for the last
group), the shifts (`ymm9`), `0xfff` (`ymm10`) and `q` (`ymm11`). -/
def d12Consts : List Instr :=
  yconst4 .xmm8 0x8080020180800100 0x8080050480800403 0x8080080780800706 0x80800b0a80800a09 ++
    yconst4 .xmm12 0x8080060580800504 0x8080090880800807 0x80800c0b80800b0a 0x80800f0e80800e0d ++
    [.movImm64 .rax 0x0000000400000000, .vop (.vmovq .xmm9 .rax), .vop (.vpbroadcastq .l256 .xmm9 .xmm9)] ++
    yconst .xmm10 0xfff ++ yconst .xmm11 3329

/-- The eight coefficients of the 12 bytes that the mask `m` selects from
the 16 at `rdi`, reduced, to `rsi`. -/
def d12Body (m : XReg) : List Instr :=
  [.vbroadcasti128 .xmm0 (at_ .rdi 0), yb .vpshufb .xmm0 .xmm0 m, .vop (.vvar .vpsrlvd .l256 .xmm0 .xmm0 .xmm9),
    yb .vpand .xmm0 .xmm0 .xmm10, yb .vpsubd .xmm0 .xmm0 .xmm11, .vop (.vshift .psrad .l256 .xmm1 .xmm0 31),
    yb .vpand .xmm1 .xmm1 .xmm11, yb .vpaddd .xmm0 .xmm0 .xmm1, .vmovdquStore .l256 (at_ .rsi 0) .xmm0]

def d12Step : List Instr := [.alu .add .rdi (.imm 12), .alu .add .rsi (.imm 32), .alu .sub .rcx (.imm 1)]

def decode12Avx2 : Prog isa :=
  .seq (.block (d12Consts ++ [.mov32 .rcx (.imm 31)]))
    (.seq (.loop (.block (d12Body .xmm8 ++ d12Step)) .ne)
      (.block (.alu .sub .rdi (.imm 4) :: d12Body .xmm12 ++ [.vop .vzeroupper])))

end VG.Impl.MlKem.X86_64
