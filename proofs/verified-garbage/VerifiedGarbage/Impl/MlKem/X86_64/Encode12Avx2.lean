module

public import VerifiedGarbage.Impl.MlKem.X86_64.Decode12Avx2

/-!
# ML-KEM on x86-64: `vg_mlkem_encode12_avx2`

`encode12Avx2(f = rdi, out = rsi)` is `vg_mlkem_encode12` (`Encode12.lean`)
on 32 coefficients at a time, in AVX2 registers. For each 16 of them
(`e12Half`): `vpackssdw` and `vpermq` pack the doublewords into words, in
order (the coefficients are less than `q`), so that each
doubleword holds a pair `f₀ + 2¹⁶ f₁`; shifts take it to `2¹² f₁` and to
`f₀`, and `vpaddd` adds them into the 24-bit number `f₀ + 2¹² f₁`; `vpshufb`
(`ymm8`) moves the three low bytes of each doubleword together, 12 bytes in
the low doublewords of each lane. `vpermd` then gathers the 24 bytes of the
first 16 coefficients in the low 24 bytes of `ymm0` (`ymm9`), and those of
the next 16 as 8 bytes in the top doublewords and 16 bytes in the low lane
of `ymm2` (`ymm10`); `vpblendd` puts the 8 bytes after the 24, and the 48
bytes are stored as 32 and 16, so that the code writes only the 384 bytes of
`*out`.

The loop runs eight times, with `rcx` counting down. The constants are
loaded from statics of them, through `rax` (`yconst4`). There are no
multiplications. It clears the upper halves of the vector registers before
returning (`vzeroupper`). Every address and branch depends only on the
pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The constants: the mask of `vpshufb` (`ymm8`) and the indices of
`vpermd` (`ymm9`, `ymm10`). -/
def e12Consts : List Instr :=
  yconst4 .xmm8 0x0908060504020100 0x808080800e0d0c0a 0x0908060504020100 0x808080800e0d0c0a ++
    yconst4 .xmm9 0x0000000100000000 0x0000000400000002 0x0000000600000005 0 ++
    yconst4 .xmm10 0x0000000400000002 0x0000000600000005 0 0x0000000100000000

/-- The 24 bytes of the 16 coefficients at `rdi + off` in the low 12 bytes
of each lane of `d`, with `t` as a temporary. -/
def e12Half (d t : XReg) (off : Nat) : List Instr :=
  [.vmovdquLoad .l256 d (at_ .rdi off), .vmovdquLoad .l256 t (at_ .rdi (off + 32)),
    yb .vpackssdw d d t, .vop (.vpermq d d 0xD8), .vop (.vshift .psrld .l256 t d 16),
    .vop (.vshift .pslld .l256 t t 12), .vop (.vshift .pslld .l256 d d 16), .vop (.vshift .psrld .l256 d d 16),
    yb .vpaddd d d t, yb .vpshufb d d .xmm8]

/-- The 48 bytes of the 32 coefficients at `rdi`, to `rsi`. -/
def e12Body : List Instr :=
  e12Half .xmm0 .xmm1 0 ++ e12Half .xmm2 .xmm3 64 ++
    [.vop (.vpermd .xmm0 .xmm9 .xmm0), .vop (.vpermd .xmm2 .xmm10 .xmm2), .vop (.vpblendd .l256 .xmm0 .xmm0 .xmm2 0xC0),
      .vmovdquStore .l256 (at_ .rsi 0) .xmm0, .vmovdquStore .l128 (at_ .rsi 32) .xmm2]

def e12Step : List Instr := [.alu .add .rdi (.imm 128), .alu .add .rsi (.imm 48), .alu .sub .rcx (.imm 1)]

def encode12Avx2 : Prog isa :=
  .seq (.block (e12Consts ++ [.mov32 .rcx (.imm 8)]))
    (.seq (.loop (.block (e12Body ++ e12Step)) .ne) (.block [.vop .vzeroupper]))

end VG.Impl.MlKem.X86_64
