module

public import VerifiedGarbage.Impl.ChaCha20.AArch64

@[expose] public section

namespace VG.Impl.ChaCha20.AArch64

open VG.AArch64

/-- A block implementation used by the scalar stream code. -/
structure Callee where
  name : String
  code : Prog isa
  suffix : String

def Callee.scalar : Callee := ⟨"vg_chacha20_block", block, ""⟩

end VG.Impl.ChaCha20.AArch64
