module

public import VerifiedGarbage.Impl.MlKem.X86_64.Ntt
public import VerifiedGarbage.Impl.MlKem.X86_64.Avx

/-!
# ML-KEM on x86-64: binary operations on AVX2 registers

`yb`, a binary operation on 256-bit registers (`Avx.lean`), which the AVX2
code of ML-KEM builds on.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `vop d, a, b` on 256-bit registers. -/
def yb (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)

end VG.Impl.MlKem.X86_64
