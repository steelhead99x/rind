module

public import VerifiedGarbage.Impl.MlKem.X86_64.Compress
public import VerifiedGarbage.Impl.MlKem.X86_64.Decode12Avx2

/-!
# ML-KEM on x86-64: `vg_mlkem_compress_encode_avx2` and `vg_mlkem_decode_decompress_avx2`

`vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress` (`Compress.lean`)
on eight coefficients at a time, in the doublewords of AVX2 registers, for
the widths 10, 4 and 1. There are no multiplications: the products by the
constants are sums of shifts. (`cm10` and `cm4`, below, are the compression
with multiplications, for code that runs in an MXCSR region.)

* Compression (`f = rdi`, `d = esi`, `out = rdx` moved to `r8`, `rcx`
  counting down): each coefficient `x < q` is `((x · M_d + 262080) >> 19)
  mod 2ᵈ` as in the scalar code, with `x · M_d` the sum of its shifts (`M₁₀
  = 161271 = 2¹⁷ + 2¹⁵ - 2¹¹ - 2⁹ - 2³ - 1`, `M₄ = 2520 = 2¹¹ + 2⁹ - 2⁵ -
  2³`). The eight values are then packed: `vpsllvd` shifts the odd ones left
  by `d`, adding each quadword's high doubleword to its low one gives the
  `2d`-bit pair (masked for `d = 10`), and for `d = 10`, `vpsllvq` and
  `vpsrldq` add each lane's two pairs into a 40-bit value. `vpshufb` and
  `vextracti128` gather the `d` bytes of the eight in the low bytes of
  `xmm1`, the others zero.
  - `d = 10`: a group of eight is ten bytes, stored as 16 (the next group
    overwrites the last six); the last group (`r8 = out + 310`) is stored
    to `out + 304`, its bytes shifted up by six over the last six bytes of
    the group before it (`vpsrldq` of `xmm1` by 4), so that the code writes
    only the 320 bytes of `out`.
  - `d = 4`: four groups of eight are four bytes each, interleaved
    (`vpunpckldq`, `vpunpcklqdq`) into the 16 bytes of 32 coefficients.
  - `d = 1` (`M₁ = 315 = 2⁸ + 2⁶ - 2² - 1`): `vpsllvd` shifts the bit of
    value `j` of lane `l` of group `g` of 32 coefficients to bit
    `8 g + 4 l + j` of its doubleword, `vpaddd` adds the four groups, and
    `vpsrlq`, `vpsrldq` and `vextracti128` with `vpaddd` add up the eight
    doublewords into the four bytes of the 32 coefficients, which `movq`
    and a 32-bit store write.
* Decompression (`b = rdi`, `len = rsi`, `d = edx`, `f = rcx` moved to
  `rsi`, `rcx` counting down): `vbroadcasti128` loads 16 bytes into both
  lanes, `vpshufb` puts the two bytes that hold value `j` in the low half of
  doubleword `j`, `vpsrlvd` and `vpand` extract it, and each value `y` is
  decompressed to `(q · y + 2ᵈ⁻¹) >> d`, with `q · y = y + 2⁸ y - 2¹⁰ y +
  2¹² y`.
  - `d = 10`: a group of eight is ten bytes; the last group is loaded from
    six bytes before it, with a mask that takes bytes 6 to 15 (`ymm12`), so
    that the code reads only the 320 bytes of `b`.
  - `d = 4`: one load holds 32 values, extracted with four masks.
  - `d = 1`: one load holds 128 values; `vpshufb` puts one of its
    doublewords in every doubleword (four masks), and `vpsrlvd` shifts bit
    `8 j + 4 l + i` of it, value `i` of lane `l` of its byte `j`, down to
    bit 0 (four shifts).

Each constant of four quadwords is loaded from a static of them, whose
address goes to `rax` (`yconst4`); each constant of a repeated doubleword is
built in registers, through `rax` (`yconst`). Both clear the upper halves of the vector registers
before returning (`vzeroupper`). Every address and branch depends only on
the pointers and `d`.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `ymm d ← ymm a << n` and `>> n` (each doubleword). -/
def ysl (d a : XReg) (n : Nat) : Instr := .vop (.vshift .pslld .l256 d a (BitVec.ofNat 8 n))
def ysr (d a : XReg) (n : Nat) : Instr := .vop (.vshift .psrld .l256 d a (BitVec.ofNat 8 n))

/-! ## Compression -/

/-- `ymm1 ← x · 161271` for the doublewords `x` of `ymm0`, through `ymm2` and `ymm3`. -/
def ceMul10 : List Instr :=
  [ysl .xmm1 .xmm0 17, ysl .xmm2 .xmm0 15, yb .vpaddd .xmm1 .xmm1 .xmm2,
    ysl .xmm2 .xmm0 11, ysl .xmm3 .xmm0 9, yb .vpaddd .xmm2 .xmm2 .xmm3, yb .vpsubd .xmm1 .xmm1 .xmm2,
    ysl .xmm2 .xmm0 3, yb .vpaddd .xmm2 .xmm2 .xmm0, yb .vpsubd .xmm1 .xmm1 .xmm2]

/-- `ymm1 ← x · 2520` for the doublewords `x` of `ymm0`, through `ymm2` and `ymm3`. -/
def ceMul4 : List Instr :=
  [ysl .xmm1 .xmm0 11, ysl .xmm2 .xmm0 9, yb .vpaddd .xmm1 .xmm1 .xmm2,
    ysl .xmm2 .xmm0 5, ysl .xmm3 .xmm0 3, yb .vpaddd .xmm2 .xmm2 .xmm3, yb .vpsubd .xmm1 .xmm1 .xmm2]

/-- `ymm1 ← ((ymm1 + 262080) >> 19) ∧ (2ᵈ - 1)`, with `262080` in `ymm12` and `2ᵈ - 1` in `ymm13`. -/
def ceRound : List Instr := [yb .vpaddd .xmm1 .xmm1 .xmm12, ysr .xmm1 .xmm1 19, yb .vpand .xmm1 .xmm1 .xmm13]

/-- The `d` bytes of the eight `d`-bit values in `ymm1`, in the low bytes of
`xmm1` (the others zero), through `ymm2`: `ymm8` holds the shifts `0, d` of
`vpsllvd`, `ymm11` the mask of `vpshufb`; for `d = 10` (`wide`), `ymm9` the
mask `2²⁰ - 1` of each quadword and `ymm10` the shifts `0, 20` of `vpsllvq`. -/
def cePack (wide : Bool) : List Instr :=
  [.vop (.vvar .vpsllvd .l256 .xmm1 .xmm1 .xmm8), .vop (.vshift .psrlq .l256 .xmm2 .xmm1 32),
    yb .vpaddd .xmm1 .xmm1 .xmm2] ++
  (if wide then
    [yb .vpand .xmm1 .xmm1 .xmm9, .vop (.vvar .vpsllvq .l256 .xmm1 .xmm1 .xmm10),
      .vop (.vshift .psrldq .l256 .xmm2 .xmm1 8), yb .vpaddq .xmm1 .xmm1 .xmm2]
  else []) ++
  [yb .vpshufb .xmm1 .xmm1 .xmm11, .vop (.vextracti128 .xmm2 .xmm1 1), .vop (.vbin .vpor .l128 .xmm1 .xmm1 .xmm2)]

/-- The eight coefficients at `rdi + o`, compressed to 10 bits and packed into `xmm1`. -/
def ce10Grp (o : Nat) : List Instr :=
  .vmovdquLoad .l256 .xmm0 (at_ .rdi o) :: ceMul10 ++ ceRound ++ cePack true

/-- The eight coefficients at `rdi + o`, compressed to 4 bits and packed into `xmm1`. -/
def ce4Grp (o : Nat) : List Instr :=
  .vmovdquLoad .l256 .xmm0 (at_ .rdi o) :: ceMul4 ++ ceRound ++ cePack false

/-- The constants of `d = 10`. -/
def ce10Consts : List Instr :=
  yconst4 .xmm8 0x0000000a00000000 0x0000000a00000000 0x0000000a00000000 0x0000000a00000000 ++
  yconst4 .xmm9 0xfffff 0xfffff 0xfffff 0xfffff ++ yconst4 .xmm10 0 20 0 20 ++
  yconst4 .xmm11 0x8080800403020100 0x8080808080808080 0x0201008080808080 0x8080808080800403 ++
  yconst .xmm12 262080 ++ yconst .xmm13 1023

/-- The constants of `d = 4`. -/
def ce4Consts : List Instr :=
  yconst4 .xmm8 0x0000000400000000 0x0000000400000000 0x0000000400000000 0x0000000400000000 ++
  yconst4 .xmm11 0x8080808080800800 0x8080808080808080 0x8080808008008080 0x8080808080808080 ++
  yconst .xmm12 262080 ++ yconst .xmm13 15

/-- `d = 10`: 31 groups of eight, then the last (see the module's documentation). -/
def ce10V : Prog isa :=
  .seq (.block (ce10Consts ++ [.mov32 .rcx (.imm 31)]))
    (.seq (.loop (.block (ce10Grp 0 ++
        [.vmovdquStore .l128 (at_ .r8 0) .xmm1, .alu .add .rdi (.imm 32), .alu .add .r8 (.imm 10),
          .alu .sub .rcx (.imm 1)])) .ne)
      (.block (.vop (.vshift .psrldq .l128 .xmm4 .xmm1 4) :: ce10Grp 0 ++
        [.vop (.vshift .pslldq .l128 .xmm1 .xmm1 6), .vop (.vbin .vpor .l128 .xmm1 .xmm1 .xmm4),
          .alu .sub .r8 (.imm 6), .vmovdquStore .l128 (at_ .r8 0) .xmm1, .vop .vzeroupper])))

/-- `d = 4`: eight groups of 32. -/
def ce4V : Prog isa :=
  .seq (.block (ce4Consts ++ [.mov32 .rcx (.imm 8)]))
    (.seq (.loop (.block (ce4Grp 0 ++ [.vop (.vmovdqa .l128 .xmm4 .xmm1)] ++ ce4Grp 32 ++
        [.vop (.vmovdqa .l128 .xmm5 .xmm1)] ++ ce4Grp 64 ++ [.vop (.vmovdqa .l128 .xmm6 .xmm1)] ++ ce4Grp 96 ++
        [.vop (.vbin .vpunpckldq .l128 .xmm4 .xmm4 .xmm5), .vop (.vbin .vpunpckldq .l128 .xmm6 .xmm6 .xmm1),
          .vop (.vbin .vpunpcklqdq .l128 .xmm4 .xmm4 .xmm6), .vmovdquStore .l128 (at_ .r8 0) .xmm4,
          .alu .add .rdi (.imm 128), .alu .add .r8 (.imm 16), .alu .sub .rcx (.imm 1)])) .ne)
      (.block [.vop .vzeroupper]))

/-- `ymm1 ← x · 315` for the doublewords `x` of `ymm0`, through `ymm2`. -/
def ceMul1 : List Instr :=
  [ysl .xmm1 .xmm0 8, ysl .xmm2 .xmm0 6, yb .vpaddd .xmm1 .xmm1 .xmm2, ysl .xmm2 .xmm0 2,
    yb .vpaddd .xmm2 .xmm2 .xmm0, yb .vpsubd .xmm1 .xmm1 .xmm2]

/-- The eight coefficients at `rdi + 32 g`, compressed to 1 bit and shifted
to bits `8 g` to `8 g + 7` of the doublewords by `ymm (8 + g)`, added to
`ymm4` (or, for the first, stored to it). -/
def ce1Grp (g : Nat) (sh : XReg) : List Instr :=
  .vmovdquLoad .l256 .xmm0 (at_ .rdi (32 * g)) :: ceMul1 ++ ceRound ++
    (if g = 0 then [.vop (.vvar .vpsllvd .l256 .xmm4 .xmm1 sh)]
    else [.vop (.vvar .vpsllvd .l256 .xmm1 .xmm1 sh), yb .vpaddd .xmm4 .xmm4 .xmm1])

/-- The constants of `d = 1`: the shifts `8 g + 4 l + j` of value `j` of lane
`l` of group `g` (`ymm8` to `ymm11`), `262080` (`ymm12`) and `1` (`ymm13`). -/
def ce1Consts : List Instr :=
  yconst4 .xmm8 0x0000000100000000 0x0000000300000002 0x0000000500000004 0x0000000700000006 ++
  yconst4 .xmm9 0x0000000900000008 0x0000000b0000000a 0x0000000d0000000c 0x0000000f0000000e ++
  yconst4 .xmm10 0x0000001100000010 0x0000001300000012 0x0000001500000014 0x0000001700000016 ++
  yconst4 .xmm11 0x0000001900000018 0x0000001b0000001a 0x0000001d0000001c 0x0000001f0000001e ++
  yconst .xmm12 262080 ++ yconst .xmm13 1

/-- The sum of the eight doublewords of `ymm4` in `eax`, stored to `r8`. -/
def ce1Sum : List Instr :=
  [.vop (.vshift .psrlq .l256 .xmm1 .xmm4 32), yb .vpaddd .xmm4 .xmm4 .xmm1,
    .vop (.vshift .psrldq .l256 .xmm1 .xmm4 8), yb .vpaddd .xmm4 .xmm4 .xmm1, .vop (.vextracti128 .xmm1 .xmm4 1),
    .vop (.vbin .vpaddd .l128 .xmm4 .xmm4 .xmm1), .movqR .rax .xmm4, .store32 (at_ .r8 0) .rax]

/-- `d = 1`: eight iterations of 32 coefficients, four bytes each. -/
def ce1V : Prog isa :=
  .seq (.block (ce1Consts ++ [.mov32 .rcx (.imm 8)]))
    (.seq (.loop (.block (ce1Grp 0 .xmm8 ++ ce1Grp 1 .xmm9 ++ ce1Grp 2 .xmm10 ++ ce1Grp 3 .xmm11 ++ ce1Sum ++
        [.alu .add .rdi (.imm 128), .alu .add .r8 (.imm 4), .alu .sub .rcx (.imm 1)])) .ne)
      (.block [.vop .vzeroupper]))

/-! ### Compression with multiplications

`cm10` and `cm4` are `compressEncodeAvx2` for `d = 10` and `d = 4` (with the
same arguments; they read neither `d` nor `len`) on sixteen coefficients at
a time, in the words of an AVX2 register, with the multiplications of the
reference AVX2 code of Kyber: the instructions MXCSR must be `0x1FBF` for
(`Vec.lean`), which the dispatcher of every public function that runs them
sees to (`vg_mcdt_enter`).

* `cmLd`: sixteen `u32`s as words, in order (`vpackssdw`, `vpermq`).
* `cmHi` (`d = 10`, `11`): with `v = 20159 = ⌈2²⁶/q⌉`, `vpmulhw` of `8x` by
  `v` is `⌊x · 8v / 2¹⁶⌋`, which is `⌊2¹³ x / q⌋` or one more; it is one more
  only when the low half of `x · 8v` (`vpmullw`) is small, less than
  `x + off`, and then that half's top bit is clear and its difference with
  `x + off` has it set (`vpandn`, `vpsrlw` by 15), which is subtracted.
  `vpmulhrsw` by `2^(d + 2)` rounds that to `d` bits, and `vpand` reduces it
  modulo `2ᵈ`.
* `cmLo` (`d = 4`, `5`): `vpmulhw` by `v` is `⌊2¹⁰ x / q⌋` (or one more, which
  the rounding does not see), `vpmulhrsw` by `2^(d + 5)` rounds it to `d` bits.
* `vpmaddwd` by the words `1, 2ᵈ` then puts each pair of values in a
  doubleword.
* `d = 10`: `vpsllvd` by 12 of the even doublewords and `vpsrlq` by 12 put
  four values in the low 40 bits of each quadword; `vpshufb` gathers the ten
  bytes of each lane, the first lane's in its bytes 0 to 9, the second's
  first six in its bytes 10 to 15 and its last four in its bytes 0 to 3, so
  that `vpblendw` makes the first sixteen of the twenty bytes, stored as
  such, and the other four are stored from `eax`.
* `d = 4`: `vpshufb` gathers the low bytes of the doublewords, the first
  lane's in bytes 0 to 3 and the second's in bytes 4 to 7, stored from `rax`.
-/

/-- The sixteen `u32`s at `rdi + o` as the words of `ymm0`, in order, through `ymm1`. -/
def cmLd (o : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdi o), .vmovdquLoad .l256 .xmm1 (at_ .rdi (o + 32)),
    yb .vpackssdw .xmm0 .xmm0 .xmm1, .vop (.vpermq .xmm0 .xmm0 0xD8)]

/-- `Compress_d` of the words of `xmm0`, less than `q`, for `d = 10` or `11`,
and each pair of them in a doubleword: with `8v mod 2¹⁶` in the words of
`xmm8`, `off` in those of `xmm9`, `v` in `xmm10`, `2^(d + 2)` in `xmm11`,
`2ᵈ - 1` in `xmm12`, and `1, 2ᵈ` in the words of each doubleword of `xmm13`;
through `xmm1`, `xmm2`, `xmm3`. -/
def cmHi : List Instr :=
  [xmov .xmm1 .xmm0, xb .pmullw .xmm1 .xmm8, xmov .xmm2 .xmm0, xb .paddw .xmm2 .xmm9,
    .xop (.shift .psllw .xmm0 3), xb .pmulhw .xmm0 .xmm10, xmov .xmm3 .xmm1, xb .psubw .xmm3 .xmm2,
    xb .pandn .xmm1 .xmm3, .xop (.shift .psrlw .xmm1 15), xb .psubw .xmm0 .xmm1, xb .pmulhrsw .xmm0 .xmm11,
    xb .pand .xmm0 .xmm12, xb .pmaddwd .xmm0 .xmm13]

/-- `cmHi` for `d = 4` or `5`: with `v` in the words of `xmm10`, `2^(d + 5)`
in `xmm11`, `2ᵈ - 1` in `xmm12` and `1, 2ᵈ` in `xmm13`. -/
def cmLo : List Instr :=
  [xb .pmulhw .xmm0 .xmm10, xb .pmulhrsw .xmm0 .xmm11, xb .pand .xmm0 .xmm12, xb .pmaddwd .xmm0 .xmm13]

/-- The twenty bytes of the sixteen values of ten bits whose pairs are the
doublewords of `ymm0`, to `r8` (see above): with `12, 0` in the doublewords
of each quadword of `ymm14` and the masks of `vpshufb` in `ymm7`; through
`xmm1` and `rax`. -/
def cmPack10 : List Instr :=
  [.vop (.vvar .vpsllvd .l256 .xmm0 .xmm0 .xmm14), .vop (.vshift .psrlq .l256 .xmm0 .xmm0 12),
    yb .vpshufb .xmm0 .xmm0 .xmm7, .vop (.vextracti128 .xmm1 .xmm0 1),
    .vop (.vpblendw .l128 .xmm0 .xmm0 .xmm1 0xE0), .vmovdquStore .l128 (at_ .r8 0) .xmm0,
    .movqR .rax .xmm1, .store32 (at_ .r8 16) .rax]

/-- The eight bytes of the sixteen values of four bits whose pairs are the
doublewords of `ymm0`, to `r8`: with the masks of `vpshufb` in `ymm7`. -/
def cmPack4 : List Instr :=
  [yb .vpshufb .xmm0 .xmm0 .xmm7, .vop (.vextracti128 .xmm1 .xmm0 1), .vop (.vbin .vpor .l128 .xmm0 .xmm0 .xmm1),
    .movqR .rax .xmm0, .store (at_ .r8 0) .rax]

/-- The constants of `cmHi` for `d = 10`, and those of `cmPack10`. -/
def cm10Consts : List Instr :=
  yconst .xmm8 0x75F875F8 ++ yconst .xmm9 0x000F000F ++ yconst .xmm10 0x4EBF4EBF ++ yconst .xmm11 0x10001000 ++
    yconst .xmm12 0x03FF03FF ++ yconst .xmm13 0x04000001 ++ yconst4 .xmm14 12 12 12 12 ++
    yconst4 .xmm7 0x0a09080403020100 0x8080808080800c0b 0x808080800c0b0a09 0x0804030201008080

/-- The constants of `cmLo` for `d = 4`, and those of `cmPack4`. -/
def cm4Consts : List Instr :=
  yconst .xmm10 0x4EBF4EBF ++ yconst .xmm11 0x02000200 ++ yconst .xmm12 0x000F000F ++ yconst .xmm13 0x00100001 ++
    yconst4 .xmm7 0x808080800c080400 0x8080808080808080 0x0c08040080808080 0x8080808080808080

/-- `compressEncodeAvx2` for `d = 10`, in an MXCSR region: sixteen iterations
of sixteen coefficients, twenty bytes each. -/
def cm10 : Prog isa :=
  .seq (.block (.mov .r8 (.reg .rdx) :: cm10Consts))
    (.seq (rcxLoop 16 (cmLd 0 ++ toY cmHi ++ cmPack10 ++ [.alu .add .rdi (.imm 64), .alu .add .r8 (.imm 20)]))
      (.block [.vop .vzeroupper]))

/-- `compressEncodeAvx2` for `d = 4`, in an MXCSR region: sixteen iterations
of sixteen coefficients, eight bytes each. -/
def cm4 : Prog isa :=
  .seq (.block (.mov .r8 (.reg .rdx) :: cm4Consts))
    (.seq (rcxLoop 16 (cmLd 0 ++ toY cmLo ++ cmPack4 ++ [.alu .add .rdi (.imm 64), .alu .add .r8 (.imm 8)]))
      (.block [.vop .vzeroupper]))

def compressEncodeAvx2 : Prog isa :=
  .seq (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx), .alu32 .cmp .rsi (.imm 1)])
    (.ite .e ce1V (.seq (.block [.alu32 .cmp .rsi (.imm 4)]) (.ite .e ce4V ce10V)))

/-! ## Decompression -/

/-- `ymm o ← (q · y + r) >> d` for the doublewords `y` of `ymm x`, with `r` in
`ymm rr`, through `ymm t₁`, `ymm t₂`. -/
def ddMul (o x t₁ t₂ rr : XReg) (d : Nat) : List Instr :=
  [ysl o x 8, yb .vpaddd o o x, ysl t₁ x 12, ysl t₂ x 10, yb .vpsubd t₁ t₁ t₂, yb .vpaddd o o t₁,
    yb .vpaddd o o rr, ysr o o d]

/-- The eight values of the 10 bytes that the mask `m` selects from the 16 at
`rdi`, decompressed, to `rsi`. -/
def dd10Grp (m : XReg) : List Instr :=
  [.vbroadcasti128 .xmm0 (at_ .rdi 0), yb .vpshufb .xmm0 .xmm0 m, .vop (.vvar .vpsrlvd .l256 .xmm0 .xmm0 .xmm9),
    yb .vpand .xmm0 .xmm0 .xmm10] ++ ddMul .xmm1 .xmm0 .xmm2 .xmm3 .xmm11 10 ++
  [.vmovdquStore .l256 (at_ .rsi 0) .xmm1]

/-- The constants of `d = 10`: the masks (`ymm8`, and `ymm12` for the last
group), the shifts (`ymm9`), `2¹⁰ - 1` (`ymm10`) and `2⁹` (`ymm11`). -/
def dd10Consts : List Instr :=
  yconst4 .xmm8 0x8080020180800100 0x8080040380800302 0x8080070680800605 0x8080090880800807 ++
  yconst4 .xmm12 0x8080080780800706 0x80800a0980800908 0x80800d0c80800c0b 0x80800f0e80800e0d ++
  yconst4 .xmm9 0x0000000200000000 0x0000000600000004 0x0000000200000000 0x0000000600000004 ++
  yconst .xmm10 1023 ++ yconst .xmm11 512

def dd10V : Prog isa :=
  .seq (.block (dd10Consts ++ [.mov32 .rcx (.imm 31)]))
    (.seq (.loop (.block (dd10Grp .xmm8 ++ [.alu .add .rdi (.imm 10), .alu .add .rsi (.imm 32),
        .alu .sub .rcx (.imm 1)])) .ne)
      (.block (.alu .sub .rdi (.imm 6) :: dd10Grp .xmm12 ++ [.vop .vzeroupper])))

/-- The eight values of bytes `4k` to `4k + 3` of `ymm0` (mask `ymm (8 + k)`),
decompressed from 4 bits, to `rsi + 32 k`. -/
def dd4Grp (m : XReg) (k : Nat) : List Instr :=
  [yb .vpshufb .xmm1 .xmm0 m, .vop (.vvar .vpsrlvd .l256 .xmm1 .xmm1 .xmm12), yb .vpand .xmm1 .xmm1 .xmm13] ++
    ddMul .xmm2 .xmm1 .xmm3 .xmm4 .xmm14 4 ++ [.vmovdquStore .l256 (at_ .rsi (32 * k)) .xmm2]

/-- The constants of `d = 4`: the masks of the four groups of a load
(`ymm8` to `ymm11`), the shifts `0, 4` (`ymm12`), `15` (`ymm13`) and `8` (`ymm14`). -/
def dd4Consts : List Instr :=
  yconst4 .xmm8 0x8080800080808000 0x8080800180808001 0x8080800280808002 0x8080800380808003 ++
  yconst4 .xmm9 0x8080800480808004 0x8080800580808005 0x8080800680808006 0x8080800780808007 ++
  yconst4 .xmm10 0x8080800880808008 0x8080800980808009 0x8080800a8080800a 0x8080800b8080800b ++
  yconst4 .xmm11 0x8080800c8080800c 0x8080800d8080800d 0x8080800e8080800e 0x8080800f8080800f ++
  yconst4 .xmm12 0x0000000400000000 0x0000000400000000 0x0000000400000000 0x0000000400000000 ++
  yconst .xmm13 15 ++ yconst .xmm14 8

def dd4V : Prog isa :=
  .seq (.block (dd4Consts ++ [.mov32 .rcx (.imm 8)]))
    (.seq (.loop (.block (.vbroadcasti128 .xmm0 (at_ .rdi 0) :: dd4Grp .xmm8 0 ++ dd4Grp .xmm9 1 ++
        dd4Grp .xmm10 2 ++ dd4Grp .xmm11 3 ++
        [.alu .add .rdi (.imm 16), .alu .add .rsi (.imm 128), .alu .sub .rcx (.imm 1)])) .ne)
      (.block [.vop .vzeroupper]))

/-- The eight values of byte `j` of the doubleword of `ymm0` that the mask
`m` puts in every doubleword, shifted by `ymm sh` (`8 j` plus the value's
index), decompressed from 1 bit, to `rsi + 32 g`. -/
def dd1Grp (m sh : XReg) (g : Nat) : List Instr :=
  [yb .vpshufb .xmm1 .xmm0 m, .vop (.vvar .vpsrlvd .l256 .xmm1 .xmm1 sh), yb .vpand .xmm1 .xmm1 .xmm6] ++
    ddMul .xmm2 .xmm1 .xmm3 .xmm4 .xmm6 1 ++ [.vmovdquStore .l256 (at_ .rsi (32 * g)) .xmm2]

/-- The constants of `d = 1`: the masks that put doubleword `k` of a load in
every doubleword (`ymm8` to `ymm11`), the shifts `8 j + i` of value `i` of
byte `j` (`ymm12` to `ymm15`), and `1` (`ymm6`), the mask of a value and the
rounding constant. -/
def dd1Consts : List Instr :=
  yconst4 .xmm8 0x0302010003020100 0x0302010003020100 0x0302010003020100 0x0302010003020100 ++
  yconst4 .xmm9 0x0706050407060504 0x0706050407060504 0x0706050407060504 0x0706050407060504 ++
  yconst4 .xmm10 0x0b0a09080b0a0908 0x0b0a09080b0a0908 0x0b0a09080b0a0908 0x0b0a09080b0a0908 ++
  yconst4 .xmm11 0x0f0e0d0c0f0e0d0c 0x0f0e0d0c0f0e0d0c 0x0f0e0d0c0f0e0d0c 0x0f0e0d0c0f0e0d0c ++
  yconst4 .xmm12 0x0000000100000000 0x0000000300000002 0x0000000500000004 0x0000000700000006 ++
  yconst4 .xmm13 0x0000000900000008 0x0000000b0000000a 0x0000000d0000000c 0x0000000f0000000e ++
  yconst4 .xmm14 0x0000001100000010 0x0000001300000012 0x0000001500000014 0x0000001700000016 ++
  yconst4 .xmm15 0x0000001900000018 0x0000001b0000001a 0x0000001d0000001c 0x0000001f0000001e ++
  yconst .xmm6 1

/-- The 32 values of doubleword `k` of the 16 bytes in `ymm0`, to `rsi + 128 k`. -/
def dd1Dw (m : XReg) (k : Nat) : List Instr :=
  dd1Grp m .xmm12 (4 * k) ++ dd1Grp m .xmm13 (4 * k + 1) ++ dd1Grp m .xmm14 (4 * k + 2) ++
    dd1Grp m .xmm15 (4 * k + 3)

/-- `d = 1`: two iterations of 16 bytes. -/
def dd1V : Prog isa :=
  .seq (.block (dd1Consts ++ [.mov32 .rcx (.imm 2)]))
    (.seq (.loop (.block (.vbroadcasti128 .xmm0 (at_ .rdi 0) :: dd1Dw .xmm8 0 ++ dd1Dw .xmm9 1 ++
        dd1Dw .xmm10 2 ++ dd1Dw .xmm11 3 ++
        [.alu .add .rdi (.imm 16), .alu .add .rsi (.imm 512), .alu .sub .rcx (.imm 1)])) .ne)
      (.block [.vop .vzeroupper]))

def decodeDecompressAvx2 : Prog isa :=
  .seq (.block [.mov32 .rdx (.reg .rdx), .mov .rsi (.reg .rcx), .alu32 .cmp .rdx (.imm 1)])
    (.ite .e dd1V (.seq (.block [.alu32 .cmp .rdx (.imm 4)]) (.ite .e dd4V dd10V)))

end VG.Impl.MlKem.X86_64
