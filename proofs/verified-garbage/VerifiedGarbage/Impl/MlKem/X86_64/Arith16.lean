module

public import VerifiedGarbage.Impl.MlKem.X86_64.Arith
public import VerifiedGarbage.Impl.MlKem.X86_64.NttAvx2

/-!
# ML-KEM on x86-64: a polynomial of `u16`s added to one of `u32`s, with AVX2

`add16Y` adds the polynomial of `u16`s at `rsi` to the one of `u32`s at `rdi`,
as `addAvx2` adds two of `u32`s, 16 coefficients at a time: it loads 16
`u16`s, brings quadwords `0, 2` to lane 0 and `1, 3` to lane 1 (`vpermq` with
`0xD8`), and widens the low (high) four words of each lane against the zero
in `ymm14` (`vpunpck{l,h}wd`) to the eight coefficients of the first (second)
half, which `addArith` adds to those of `rdi`.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- Eight coefficients of `f` at `rdi + o` plus the words `op` widens from `ymm2`. -/
def add16Half (op : XBinOp) (o : Nat) : List Instr :=
  .vmovdquLoad .l256 .xmm0 (at_ .rdi o) :: toY (xmov .xmm1 .xmm2 :: xb op .xmm1 .xmm14 :: addArith) ++
    [.vmovdquStore .l256 (at_ .rdi o) .xmm0]

/-- Sixteen coefficients: `f` (`u32`s at `rdi`) plus `g` (`u16`s at `rsi`). -/
def add16Body : List Instr :=
  [.vmovdquLoad .l256 .xmm2 (at_ .rsi 0), .vop (.vpermq .xmm2 .xmm2 0xD8)] ++ add16Half .punpcklwd 0 ++
    add16Half .punpckhwd 32 ++ [.alu .add .rdi (.imm 64), .alu .add .rsi (.imm 32)]

/-- `f = rdi` (`u32`s) plus `g = rsi` (`u16`s), to `f`. -/
def add16Y : Prog isa :=
  .seq (.block (yconst .xmm15 3329 ++ [yb .vpxor .xmm14 .xmm14 .xmm14]))
    (.seq (rcxLoop 16 add16Body) (.block [.vop .vzeroupper]))

end VG.Impl.MlKem.X86_64
